/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Store
public import Lake.Build.Job.Basic
public import Std.Sync.Mutex

set_option doc.verso true
set_option linter.missingDocs true

/-!
# The Lake Build Store

The Lake build store is the map of Lake build keys to build task and/or
build results that is slowly filled during a recursive build (e.g., via
topological-based build of an initial key's dependencies).
-/

namespace Lake

/-! ## Pure State -/

/-- Value type of a key in the Lake build store. -/
public abbrev BuildStoreCell (k : BuildKey) :=
  IO.Promise (Job (BuildData k))

/-- Creates a new build store cell. -/
def BuildStoreCell.new : BaseIO (BuildStoreCell k) :=
  IO.Promise.new

/-- Returns the job at this cell.  -/
@[inline] public def BuildStoreCell.get
  [FamilyOut BuildData k α] (self : BuildStoreCell k)
: BaseIO (Job α) :=
  -- The promise should resolve.
  -- If it does not, then there is another bug and a hang or panic here is acceptable.
  cast (by simp) <| IO.wait self.result!

/-- Saves {lean}`job` to this cell. Does nothing if there is already one there.  -/
@[inline] nonrec def BuildStoreCell.resolve
  [FamilyDef BuildData k α] (job : Job α) (self : BuildStoreCell k)
: BaseIO Unit := self.resolve <| cast (by simp) job

/-- The type of the Lake build store. -/
public  abbrev BuildStore :=
  Std.DTreeMap BuildKey BuildStoreCell BuildKey.quickCmp

/-- Returns a new empty build store. -/
@[inline] public def BuildStore.empty : BuildStore := Std.DTreeMap.empty

/-! ## Atomic Mutable Reference -/

/-- A mutable reference to the Lake build store. -/
public abbrev BuildStoreRef := Std.Mutex BuildStore

namespace BuildStoreRef

/-- Creates a new mutable build store. -/
@[inline] public def new (s : BuildStore := {}) : BaseIO BuildStoreRef :=
  Std.Mutex.new s

/-- Atomically applies a pure modifucation to the build store. -/
@[inline] public def modify (f : BuildStore → BuildStore) (r : BuildStoreRef) : BaseIO Unit :=
  r.atomically (·.modify f)

/-- Atomically pplies a pure modifucation to the build store and returns the paired value. -/
@[inline] public def modifyGet (f : BuildStore → (α × BuildStore)) (r : BuildStoreRef) : BaseIO α :=
  r.atomically (·.modifyGet f)

/-- Reads the current value of the build store, returning a snapshot of its state. -/
@[inline] public def get (r : BuildStoreRef) : BaseIO BuildStore :=
  r.atomically (·.get)

/-- Atomically returns a projection of current value of the build store. -/
@[inline] public def getMap (f : BuildStore → α) (r : BuildStoreRef) : BaseIO α :=
  r.atomically fun ref => return f (← ref.get)

/--
Atomically returns the build store's saved job for the build key {lean}`k`, if any.
Otehrwise, returns {lean}`none`.
-/
@[inline] public def fetch?
  (k : BuildKey) [FamilyOut BuildData k α] (r : BuildStoreRef)
: BaseIO (Option (Job α)) := do
  let some cell ← r.atomically fun r => return (← r.get).get? k
    | return none
  cast (by simp) <| IO.wait cell.result?

/--
Returns the cell in the build store for key {lean}`k`.
The {lean}`Bool` indicates whether the cell is new.
-/
@[inline] def fetchCell (k : BuildKey) (r : BuildStoreRef) : BaseIO (Bool × BuildStoreCell k) :=
  r.atomically fun sr => do
    let s ← unsafe sr.take
    if let some cell := s.get? k then
      unsafe sr.put s
      return (false, cell)
    else
      let cell ← BuildStoreCell.new
      let s := s.insert k cell
      unsafe sr.put s
      return (true, cell)

/-- Atomically inserts a new build job into the build store. Does nothing if one already exists. -/
@[inline] public def store
  (k : BuildKey) [FamilyDef BuildData k α] (v : Job α) (r : BuildStoreRef)
: BaseIO Unit := do
  let (_, cell) ← r.fetchCell k
  cell.resolve v

/--
Atomically inserts a new build job into the build store and returns it.
If one already exists, returns that instead.
-/
@[inline] def storeAndReturn
  (k : BuildKey) [FamilyDef BuildData k α] (v : Job α) (r : BuildStoreRef)
: BaseIO (Job α) := do
  let (_, cell) ← r.fetchCell k
  let v := cast (by simp) v
  cell.resolve v
  cast (by simp) <| IO.wait (cell.resultD v)

/--
Returns the value of {lean}`k` in the store if it exists.
Otherwise, runs {lean}`create` to generate it, adds it to the store, and returns the result.
-/
@[inline] public def fetchOrCreate
  [Monad m] [MonadLiftT BaseIO m]
  (k : BuildKey) [FamilyDef BuildData k α] (create : m (Job α))
  (r : BuildStoreRef)
: m (Job α) := do
  let (new, cell) ← r.fetchCell k
  if new then
    let val ← create
    cell.resolve val
    return val
  else
    cell.get

end BuildStoreRef

/-! ## Monadic Interaction -/

/--
Transformer to equip a monad with a mutable Lake build store.

An internal monad. **Not intended for user use.**
-/
public abbrev BuildStoreT := ReaderT BuildStoreRef

/---
Runs the monadic action {lean}`x` over the build store {lean}`s`,
returning the monadic result paired with the final state of the build store.
-/
@[inline] public nonrec def BuildStoreT.run
  [Monad m] [MonadLiftT BaseIO m]
  (s : BuildStore := {}) (x : BuildStoreT m α)
: m (α × BuildStore) := do
  let ref ← BuildStoreRef.new s
  let a ← x.run ref
  let s ← ref.get
  return (a, s)

/-- Type class for monads equipped with a Lake build store. -/
public abbrev MonadBuildStore (m) := MonadDStore BuildKey (Job <| BuildData ·) m

public instance [Monad m] [MonadLiftT BaseIO m] : MonadBuildStore (BuildStoreT m) where
  fetch? k := fun r => r.fetch? k
  store k v := fun r => r.store k v
