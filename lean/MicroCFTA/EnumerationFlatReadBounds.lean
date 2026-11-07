import MicroCFTA.FlatUnionFindReadBounds
import MicroCFTA.EnumerationFlatNativeIncomingCache

/-!
# Fixed bounds for flat enumeration reads

The comparison input erases only the member lists of the actual flat forest.
Two earlier search steps cover each representative and count read. Native
intersection and emptiness-check bounds remain explicit.
-/

namespace MicroCFTA.EnumerationFlatState

/-- Keep all core fields and erase the flat forest member lists. -/
def erase (state : State Symbol Guard) : EnumerationState.State Symbol Guard :=
  {counter := state.counter
   representatives := FlatUnionFind.erase state.representatives
   values := state.values
   obligations := state.obligations
   recursionAncestry := state.recursionAncestry
   expansionAncestry := state.expansionAncestry}

/-- A valid flat core determines its related comparison input. -/
theorem erase_related (state : State Symbol Guard)
    (valid : FlatUnionFind.Valid state.representatives) : Related state (erase state) :=
  ⟨valid, FlatUnionFind.erase_represents valid, rfl, rfl, rfl, rfl, rfl⟩

/-- The fixed bound retains complete slot reads and explicit errors. -/
theorem getValue_fixed (state : State Symbol Guard)
    (valid : FlatUnionFind.Valid state.representatives) (uv extra : Nat) :
    EnumerationResultRelation.Results Related (getValue uv state)
      (EnumerationState.getValue (2 + extra) uv (erase state)) := by
  have read := FlatUnionFindReadBounds.root_erase_moreFuel state.representatives valid extra uv
  rw [SourceUnionFindRoot.root_eq] at read
  cases completed : UnionFind.findRoot (2 + extra) (FlatUnionFind.erase state.representatives) uv with
  | none => simp [completed] at read
  | some found => exact getValue_related (erase_related state valid) completed

end MicroCFTA.EnumerationFlatState

namespace MicroCFTA.EnumerationFlatCached

/-- Keep both indexes and compute the comparison core by forest erasure. -/
def erase (state : Cached Symbol Guard) : EnumerationExpandableIndex.Cached Symbol Guard :=
  ⟨EnumerationFlatState.erase state.core, state.expandable, state.waiting⟩

/-- A valid flat forest determines the entire related cached input. -/
theorem erase_related (state : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid state.core.representatives) : Related state (erase state) :=
  ⟨EnumerationFlatState.erase_related state.core valid, rfl, rfl⟩

end MicroCFTA.EnumerationFlatCached

namespace MicroCFTA.EnumerationFlatNativeIndex

local notation "Symbol" => SourcePruningTemplates.Symbol

/-- Two steps per reference retain both count folds and the full optional write. -/
theorem write_fixed (before : EnumerationFlatCached.Cached Symbol EnumGuard)
    (valid : FlatUnionFind.Valid before.core.representatives)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (extra target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended) :
    WritesRelated (write heap target value gained lost before)
      (SourcePruningEnumerationNativeIndex.write heap (2 + extra) target value gained lost
        (EnumerationFlatCached.erase before)) := by
  have removed := FlatUnionFindReadBounds.count_erase_moreFuel
    before.core.representatives valid extra (-1) lost before.waiting
  have saved := FlatUnionFindReadBounds.count_erase_moreFuel
    before.core.representatives valid extra 1 gained
      (EnumerationCanonicalWaiting.count (FlatUnionFind.root before.core.representatives)
        (-1) lost before.waiting)
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [write, SourcePruningEnumerationNativeIndex.write, classified, WritesRelated]
  | some flag =>
      simp only [write, classified, Option.map_some,
        SourcePruningEnumerationNativeIndex.write, EnumerationFlatCached.erase,
        EnumerationFlatState.erase, Option.bind_some, removed, saved]
      change EnumerationFlatCached.Related _ _
      exact ⟨⟨valid, FlatUnionFind.erase_represents valid, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

end MicroCFTA.EnumerationFlatNativeIndex

namespace MicroCFTA.EnumerationFlatNativeIncoming

open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat} {EnumGuard : Type}

/-- Two earlier search steps retain every bounded native incoming outcome. -/
theorem run_fixed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (before : EnumerationFlatState.State Symbol EnumGuard)
    (valid : FlatUnionFind.Valid before.representatives) (extra : Nat)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    EnumerationFlatNativeFold.ResultRelated
      (run checkEmpty nativeFuel p h beforeCaller before target incoming incomingScs queries)
      (SourcePruningEnumerationIncomingNode.run checkEmpty (2 + extra) nativeFuel p h
        beforeCaller (EnumerationFlatState.erase before) target incoming incomingScs queries) := by
  have read := FlatUnionFindReadBounds.root_erase_moreFuel before.representatives valid extra target
  rw [SourceUnionFindRoot.root_eq] at read
  cases completed : UnionFind.findRoot (2 + extra) (FlatUnionFind.erase before.representatives) target with
  | none => simp [completed] at read
  | some found =>
      exact run_related (EnumerationFlatState.erase_related before valid) completed
        checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries

/-- Every native outcome retains the full input core as its outer read core. -/
theorem read_core
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (before : EnumerationFlatState.State Symbol EnumGuard)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (run checkEmpty nativeFuel p h beforeCaller before target incoming incomingScs queries).2.2.2 = before := by
  simp only [run]
  repeat' first | rfl | split

end MicroCFTA.EnumerationFlatNativeIncoming

namespace MicroCFTA.SourcePruningEnumerationIncomingNode

open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat} {EnumGuard : Type}

/-- Every native outcome retains the core returned by the initial root read. -/
theorem read_core_of_findRoot
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (before : EnumerationState.State Symbol EnumGuard)
    (completed : UnionFind.findRoot representativeFuel before.representatives target = some found)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h beforeCaller before target incoming incomingScs queries).2.2.2 =
      {before with representatives := found.forest} := by
  simp only [run, completed]
  repeat' first | rfl | split

end MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.EnumerationFlatNativeIncomingCache

open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Fixed representative and index bounds retain the complete incoming observation. -/
theorem run_fixed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (before : EnumerationFlatCached.Cached Symbol Constraint)
    (valid : FlatUnionFind.Valid before.core.representatives)
    (extraRepresentative extraIndex : Nat)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    EnumerationFlatNativeCachedFold.ResultRelated
      (run checkEmpty nativeFuel p h beforeCaller before target incoming incomingScs queries)
      (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty
        (2 + extraRepresentative) nativeFuel p h (2 + extraIndex)
        beforeCaller (EnumerationFlatCached.erase before) target incoming incomingScs queries) := by
  have related := EnumerationFlatCached.erase_related before valid
  obtain ⟨found, completed, _representative, _size, _retained, _postRoot⟩ :=
    FlatUnionFindReadBounds.findRoot_erase before.core.representatives valid extraRepresentative target
  have rawRelated := EnumerationFlatNativeIncoming.run_related related.core completed
    checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries
  have flatRead := EnumerationFlatNativeIncoming.read_core before.core
    checkEmpty nativeFuel p h beforeCaller target incoming incomingScs queries
  have oldRead := SourcePruningEnumerationIncomingNode.read_core_of_findRoot
    (EnumerationFlatCached.erase before).core completed checkEmpty nativeFuel p h
    beforeCaller incoming incomingScs queries
  generalize flatRun : EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
    beforeCaller before.core target incoming incomingScs queries = left at rawRelated flatRead ⊢
  generalize oldRun : SourcePruningEnumerationIncomingNode.run checkEmpty
    (2 + extraRepresentative) nativeFuel p h beforeCaller (EnumerationFlatCached.erase before).core
    target incoming incomingScs queries = right at rawRelated oldRead ⊢
  obtain ⟨leftResult, reachedCaller, savedQueries, readFlat⟩ := left
  obtain ⟨rightResult, oldCaller, oldQueries, readEarlier⟩ := right
  obtain ⟨callerSame, queriesSame, reads, rows⟩ := rawRelated
  dsimp only at callerSame queriesSame flatRead oldRead
  subst oldCaller oldQueries
  have counted : ∀ waiting, SourcePruningEnumerationNativeIndex.count (2 + extraIndex)
      readEarlier.representatives 1 incomingScs waiting =
      some (EnumerationFlatNativeIndex.count readFlat.representatives 1 incomingScs waiting) := by
    intro waiting
    rw [flatRead, oldRead]
    exact FlatUnionFindReadBounds.count_findRoot_erase before.core.representatives valid
      (2 + extraRepresentative) target found completed extraIndex 1 incomingScs waiting
  simp only [run, SourcePruningEnumerationIncomingCacheAdapter.run, flatRun, oldRun]
  refine ⟨⟨rfl, rfl, reads, rows⟩, ?_⟩
  cases leftResult with
  | error first =>
      cases rightResult with
      | error second => trivial
      | ok value => cases rows
  | ok leftValue =>
      cases rightResult with
      | error fault => cases leftValue <;> cases rows
      | ok rightValue =>
          cases leftValue with
          | none =>
              cases rightValue with
              | none => trivial
              | some raw => cases rows
          | some leftRows =>
              cases rightValue with
              | none => cases rows
              | some rightRows =>
                  exact adapt_related related reads _ (2 + extraIndex) target incomingScs counted rows

end MicroCFTA.EnumerationFlatNativeIncomingCache
