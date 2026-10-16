-- @kz1m on dc.

local DataStoreService = game:GetService("DataStoreService")
local HttpService = game:GetService("HttpService")
local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local RunService = game:GetService("RunService")

local InventoryManager = {}

local STORE_NAME = "PlayerInventory_v3"
local DATA_VERSION = 3
local DEFAULT_CAPACITY = 30
local MAX_CAPACITY = 200
local AUTOSAVE_INTERVAL = 120
local MAX_RETRIES = 4

-- Keep the lock alive across missed autosaves and temporary server lag.
local LOCK_EXPIRY = 600
local LOCK_ATTEMPTS = 5
local LOCK_RETRY_DELAY = 5

local RELEASE_ATTEMPTS = 5
local RELEASE_RETRY_DELAY = 15

-- Leave some time for shutdown saves to complete.
local SHUTDOWN_BUDGET = 24
local DEFAULT_LOAD_TIMEOUT = 60

local KICK_REASONS = {
	error = "Couldn't load your inventory, please rejoin",
	locked = "Your data is still saving on another server, try again in a minute",
	unreadable = "Your save data couldn't be read on this server, please rejoin",
}

-- Replace this with the project's shared item definitions.
local ITEM_DEFS = {
	Wood = { maxStack = 64 },
	Stone = { maxStack = 64 },
	IronOre = { maxStack = 32 },
	HealthPotion = { maxStack = 8 },
	RustySword = { maxStack = 1 },
}

-- Fields controlled by this module. Other fields are preserved.
local OWNED_FIELDS = {
	v = true,
	capacity = true,
	items = true,
	lock = true,
}

local storeOk, store = pcall(
	DataStoreService.GetDataStore,
	DataStoreService,
	STORE_NAME
)

if not storeOk then
	warn("Inventory datastore unavailable: " .. tostring(store))
	store = nil
end

-- Sessions remain here until their datastore lock has been released.
local sessions = {}
local loading = {}
local shuttingDown = false
local initialized = false

local itemAdded = Instance.new("BindableEvent")
local itemRemoved = Instance.new("BindableEvent")
local sessionLoaded = Instance.new("BindableEvent")

InventoryManager.ItemAdded = itemAdded.Event
InventoryManager.ItemRemoved = itemRemoved.Event
InventoryManager.Loaded = sessionLoaded.Event

-- Server-to-client inventory replication.
local syncRemote = ReplicatedStorage:FindFirstChild("InventorySync")

if not syncRemote then
	syncRemote = Instance.new("RemoteEvent")
	syncRemote.Name = "InventorySync"
	syncRemote.Parent = ReplicatedStorage
end

assert(
	syncRemote:IsA("RemoteEvent"),
	"InventorySync exists but is not a RemoteEvent"
)

local function retry(fn)
	local ok, result

	for attempt = 1, MAX_RETRIES do
		ok, result = pcall(fn)

		if ok or attempt == MAX_RETRIES then
			break
		end

		task.wait(0.5 * 2 ^ attempt)
	end

	return ok, result
end

-- Only positive whole numbers are accepted.
local function isPositiveInt(n)
	return type(n) == "number"
		and n > 0
		and n % 1 == 0
end

-- Reject malformed saves rather than overwriting them with defaults.
local function isReadable(raw)
	if type(raw) ~= "table" or #raw > 0 then
		return false
	end

	if raw.items ~= nil and type(raw.items) ~= "table" then
		return false
	end

	return raw.v == nil
		or (type(raw.v) == "number" and raw.v <= DATA_VERSION)
end

local function lockOwnedBy(raw, lockId)
	return type(raw) == "table"
		and type(raw.lock) == "table"
		and raw.lock.id == lockId
end

local function serialize(session)
	local data = table.clone(session.extra)

	-- Store slots as normal entries rather than a sparse table.
	local items = table.clone(session.orphans)

	for slot, stack in pairs(session.slots) do
		table.insert(items, {
			slot,
			stack.id,
			stack.count,
		})
	end

	data.v = DATA_VERSION
	data.capacity = session.capacity
	data.items = items

	return data
end

local function deserialize(raw)
	local capacity = raw.capacity

	if not isPositiveInt(capacity) or capacity > MAX_CAPACITY then
		capacity = DEFAULT_CAPACITY
	end

	local extra = {}

	for key, value in pairs(raw) do
		if not OWNED_FIELDS[key] then
			extra[key] = value
		end
	end

	local slots = {}
	local orphans = {}
	local homeless = {}
	local junk = 0

	-- pairs allows malformed or sparse item arrays to still be processed.
	for _, entry in pairs(raw.items or {}) do
		local valid = type(entry) == "table"
			and type(entry[2]) == "string"
			and isPositiveInt(entry[3])

		if not valid or not ITEM_DEFS[entry[2]] then
			-- Preserve unknown or malformed entries instead of deleting them.
			table.insert(orphans, entry)

			if not valid then
				junk += 1
			end
		else
			local slot = entry[1]
			local id = entry[2]
			local count = entry[3]

			-- Split stacks that exceed the current item limit.
			if isPositiveInt(slot)
				and slot <= capacity
				and not slots[slot] then

				local fits = math.min(
					count,
					ITEM_DEFS[id].maxStack
				)

				slots[slot] = {
					id = id,
					count = fits,
				}

				count -= fits
			end

			if count > 0 then
				table.insert(homeless, {
					id = id,
					count = count,
				})
			end
		end
	end

	-- Rehome invalid, duplicate or overflowing stacks where possible.
	for _, stack in ipairs(homeless) do
		local maxStack = ITEM_DEFS[stack.id].maxStack
		local remaining = stack.count

		for slot = 1, capacity do
			if remaining == 0 then
				break
			end

			if not slots[slot] then
				local take = math.min(
					remaining,
					maxStack
				)

				slots[slot] = {
					id = stack.id,
					count = take,
				}

				remaining -= take
			end
		end

		if remaining > 0 then
			-- Slot 0 marks data that could not currently fit.
			table.insert(orphans, {
				0,
				stack.id,
				remaining,
			})
		end
	end

	if junk > 0 then
		warn(("Kept %d unreadable inventory entries"):format(junk))
	end

	return {
		slots = slots,
		capacity = capacity,
		orphans = orphans,
		extra = extra,
	}
end

local function replicate(session)
	-- Use string keys so empty inventory slots don't create a sparse array.
	local out = {}

	for slot, stack in pairs(session.slots) do
		out[tostring(slot)] = {
			id = stack.id,
			count = stack.count,
		}
	end

	syncRemote:FireClient(
		session.player,
		out,
		session.capacity
	)
end

local function markDirty(session)
	session.rev += 1

	if session.syncQueued then
		return
	end

	session.syncQueued = true

	-- Batch multiple changes made during the same execution cycle.
	task.defer(function()
		session.syncQueued = false

		if session.player.Parent then
			replicate(session)
		end
	end)
end

-- Serializes writes per session so an older snapshot cannot overwrite a newer one.
local function flush(session)
	while session.writing do
		table.insert(session.waiters, coroutine.running())
		coroutine.yield()
	end

	if session.done or session.noSave then
		return
	end

	local release = session.releasing

	local heartbeatDue =
		os.time() - session.lastWrite >= LOCK_EXPIRY / 3

	if not release
		and not heartbeatDue
		and session.rev == session.savedRev then
		return
	end

	session.writing = true

	local lost = false
	local rev = session.rev

	local ok, err = retry(function()
		return store:UpdateAsync(session.key, function(old)
			-- Never write if this server no longer owns the lock.
			if not lockOwnedBy(old, session.lockId) then
				lost = true
				return nil
			end

			-- Build the snapshot inside UpdateAsync.
			lost = false
			rev = session.rev

			local data = serialize(session)

			data.lock = if release
				then nil
				else {
					id = session.lockId,
					at = os.time(),
				}

			return data
		end)
	end)

	session.writing = false

	if ok and not lost then
		session.savedRev = rev
		session.lastWrite = os.time()
		session.done = release
	elseif ok and lost then
		session.done = true
	end

	-- Resume any operations waiting for this write.
	local waiters = session.waiters
	session.waiters = {}

	for _, thread in ipairs(waiters) do
		task.spawn(thread)
	end

	if ok and lost and not release then
		warn(("Lost inventory lock for %s"):format(session.player.Name))

		if session.player.Parent then
			session.player:Kick("Your data was loaded on another server")
		end
	elseif not ok then
		warn((
			"Inventory save failed for %s: %s"
		):format(
			session.player.Name,
			tostring(err)
		))
	end
end

local function release(session)
	session.releasing = true

	for attempt = 1, RELEASE_ATTEMPTS do
		flush(session)

		if session.done
			or session.noSave
			or shuttingDown
			or attempt == RELEASE_ATTEMPTS then
			break
		end

		task.wait(RELEASE_RETRY_DELAY)
	end

	if not session.done and not session.noSave then
		warn((
			"Gave up releasing %s; lock will expire automatically"
		):format(session.player.Name))
	end

	if sessions[session.player] == session then
		sessions[session.player] = nil
	end
end

-- Remove a lock if a failed load may have actually written it.
local function dropLock(key, lockId)
	retry(function()
		return store:UpdateAsync(key, function(old)
			if not lockOwnedBy(old, lockId) then
				return nil
			end

			old.lock = nil
			return old
		end)
	end)
end

local function acquire(player, key)
	if not store then
		return "error"
	end

	local lockId = HttpService:GenerateGUID(false)
	local wroteLock = false

	for attempt = 1, LOCK_ATTEMPTS do
		local status

		local ok, data = retry(function()
			return store:UpdateAsync(key, function(old)
				if old ~= nil and not isReadable(old) then
					status = "unreadable"
					return nil
				end

				old = old or {}

				local lock = old.lock

				if type(lock) == "table"
					and lock.id ~= lockId
					and os.time() - (tonumber(lock.at) or 0) < LOCK_EXPIRY then

					status = "locked"
					return nil
				end

				status = "ok"
				wroteLock = true

				old.lock = {
					id = lockId,
					at = os.time(),
				}

				return old
			end)
		end)

		if not ok then
			if wroteLock then
				dropLock(key, lockId)
			end

			return "error"
		elseif status ~= "locked" then
			return status, data, lockId
		elseif attempt == LOCK_ATTEMPTS
			or loading[player] == "left"
			or shuttingDown then
			break
		end

		task.wait(LOCK_RETRY_DELAY)
	end

	return if loading[player] == "left" or shuttingDown
		then "left"
		else "locked"
end

local function loadProfile(player)
	if shuttingDown or loading[player] or sessions[player] then
		return
	end

	loading[player] = true

	local key = "u_" .. player.UserId
	local status, data, lockId = acquire(player, key)

	if status == "error" and RunService:IsStudio() then
		-- Allow Studio testing when API access is disabled.
		warn((
			"Inventory for %s is running without saving"
		):format(player.Name))

		status, data, lockId = "ok", {}, nil
	end

	local left = loading[player] == "left"
		or not player.Parent
		or shuttingDown

	loading[player] = nil

	if status ~= "ok" then
		if not left and KICK_REASONS[status] then
			player:Kick(KICK_REASONS[status])
		end

		return
	end

	local session = deserialize(data)

	session.player = player
	session.key = key
	session.lockId = lockId
	session.noSave = lockId == nil
	session.rev = 0
	session.savedRev = 0
	session.lastWrite = os.time()
	session.waiters = {}

	sessions[player] = session

	if left then
		-- Release a lock acquired after the player left.
		task.spawn(release, session)
		return
	end

	replicate(session)
	sessionLoaded:Fire(player)
end

local function activeSession(player)
	local session = sessions[player]

	-- Prevent changes while the final save is being released.
	if session
		and not session.releasing
		and not session.done then
		return session
	end

	return nil
end

local function sessionFor(player, action)
	local session = activeSession(player)

	if not session and player.Parent then
		warn((
			"%s ignored for %s; inventory is not loaded"
		):format(action, player.Name))
	end

	return session
end

local function countIn(session, itemId)
	local total = 0

	for _, stack in pairs(session.slots) do
		if stack.id == itemId then
			total += stack.count
		end
	end

	return total
end

function InventoryManager:IsLoaded(player)
	return activeSession(player) ~= nil
end

function InventoryManager:WaitForLoaded(player, timeout)
	local remaining = timeout or DEFAULT_LOAD_TIMEOUT

	while not activeSession(player) do
		if not player.Parent or remaining <= 0 then
			return false
		end

		remaining -= task.wait(0.1)
	end

	return true
end

function InventoryManager:CountItem(player, itemId)
	local session = sessionFor(player, "CountItem")

	return if session
		then countIn(session, itemId)
		else 0
end

function InventoryManager:AddItem(player, itemId, amount)
	local def = assert(
		ITEM_DEFS[itemId],
		"Unknown item " .. tostring(itemId)
	)

	assert(
		isPositiveInt(amount),
		"Amount must be a positive whole number"
	)

	local session = sessionFor(player, "AddItem")

	if not session then
		return 0, amount
	end

	local remaining = amount

	-- Fill existing stacks before creating new ones.
	for slot = 1, session.capacity do
		local stack = session.slots[slot]

		if remaining > 0
			and stack
			and stack.id == itemId
			and stack.count < def.maxStack then

			local take = math.min(
				def.maxStack - stack.count,
				remaining
			)

			stack.count += take
			remaining -= take
		end
	end

	-- Create new stacks for anything that remains.
	for slot = 1, session.capacity do
		if remaining > 0 and not session.slots[slot] then
			local take = math.min(
				def.maxStack,
				remaining
			)

			session.slots[slot] = {
				id = itemId,
				count = take,
			}

			remaining -= take
		end
	end

	local added = amount - remaining

	if added > 0 then
		markDirty(session)
		itemAdded:Fire(player, itemId, added)
	end

	return added, remaining
end

function InventoryManager:RemoveItem(player, itemId, amount)
	assert(
		isPositiveInt(amount),
		"Amount must be a positive whole number"
	)

	local session = sessionFor(player, "RemoveItem")

	if not session or countIn(session, itemId) < amount then
		return false
	end

	local remaining = amount

	-- Remove from higher slots first to avoid unnecessary slot movement.
	for slot = session.capacity, 1, -1 do
		local stack = session.slots[slot]

		if remaining > 0
			and stack
			and stack.id == itemId then

			local take = math.min(
				stack.count,
				remaining
			)

			stack.count -= take
			remaining -= take

			if stack.count == 0 then
				session.slots[slot] = nil
			end
		end
	end

	markDirty(session)
	itemRemoved:Fire(player, itemId, amount)

	return true
end

function InventoryManager.Init()
	if initialized then
		return
	end

	initialized = true

	Players.PlayerAdded:Connect(loadProfile)

	for _, player in ipairs(Players:GetPlayers()) do
		task.spawn(loadProfile, player)
	end

	Players.PlayerRemoving:Connect(function(player)
		if loading[player] then
			loading[player] = "left"
		end

		local session = sessions[player]

		if session and not session.releasing then
			release(session)
		end
	end)

	task.spawn(function()
		while true do
			task.wait(AUTOSAVE_INTERVAL)

			if shuttingDown then
				break
			end

			for _, session in pairs(sessions) do
				if not session.releasing then
					task.spawn(flush, session)
				end
			end
		end
	end)

	game:BindToClose(function()
		shuttingDown = true

		for _, session in pairs(sessions) do
			task.spawn(release, session)
		end

		-- Wait for active saves and loads during shutdown.
		local deadline = os.time() + SHUTDOWN_BUDGET

		while (next(sessions) or next(loading))
			and os.time() < deadline do

			task.wait()
		end
	end)
end

return InventoryManager
