import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourcePruningEnumerationSharedChildIsolation

/-!
# Isolation from actual prepared child input sources

The parent bucket comes from an actual stored pending slot.
The own prefix allocates only fresh suspended variables.
Both input sources avoid the original isolated class.
The own prefix retains every member of the original class.
The actual shared child singleton retains the same root and native handle.
This result does not cover every stopped or rejected cache.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedSharedChildIsolation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences
open EnumerationDischargeHistory InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)

set_option autoImplicit false
variable {bits : Nat}

/-- Actual preparation derives complete child resources before any child result. -/
theorem prepared_stored_child_inputs
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (caller : Caller (bits + 2)) (captured own : Cached)
    (parentOwner : Nat) (parentNode : Option Nat) (parentBucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (symbol : Symbol) (staged : List Child)
    (residual : Option Constraint) (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (held heldHandle : Nat) (safe : Safe captured.core)
    (isolated : IsolatedPending held heldHandle captured.core)
    (parentStored : captured.core.values[parentOwner]? = some (.unenumerated parentNode parentBucket))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap
      parentBucket edge captured = some [((symbol, staged, residual), own)])
    (selected : staged[position]? = some (incoming, bucket, action)) :
    EnumerationDriver.Protected held captured.core own.core ∧
      IsolatedPending held heldHandle own.core ∧
      Avoids own.core.representatives held bucket ∧ Safe own.core ∧
      ∀ sc ∈ bucket, sc.var < own.core.counter := by
  have allowed : arityAllows edge.children.length parentBucket = true := by
    by_cases accepted : arityAllows edge.children.length parentBucket = true
    · exact accepted
    · simp [SourcePruningEnumerationCachedOwn.prepare, accepted] at prepared
  cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
  | none =>
      simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at prepared
  | some pair =>
      obtain ⟨tries, projectedResidual⟩ := pair
      have scalars := SourcePruningEnumerationCachedOwn.prepare_scalars
        caller.checked.native.machine.heap parentBucket edge captured own tries projectedResidual
        (symbol, staged, residual) projected prepared
      have ownCore : own.core = suspendedState tries.length captured.core := scalars.2.1
      have ownCounter : own.core.counter = captured.core.counter + tries.length := scalars.2.2.1
      have ownSafe : Safe own.core := by
        rw [ownCore]
        exact suspension_safe tries.length captured.core safe
      have inside : held < captured.core.counter := by
        rw [safe.1.aligned]
        exact (List.getElem?_eq_some_iff.mp isolated.stored).1
      have protection : EnumerationDriver.Protected held captured.core own.core := by
        rw [ownCore]
        exact EnumerationDriver.suspension_protected held tries.length captured.core safe inside isolated.root
      have references : ReferencesAllowed
          (fun target => ¬UnionFind.SameClass captured.core.representatives held target) own.core := by
        rw [ownCore]
        exact suspension_allowed _ tries.length captured.core isolated.incoming
      have ownIsolated : IsolatedPending held heldHandle own.core := by
        refine ⟨protection.root, protection.value.trans isolated.stored, ?_⟩
        intro value member sc listed related
        exact references value member sc listed ((protection.classes sc.var).mp related)
      have parentAvoids : Avoids captured.core.representatives held parentBucket :=
        isolated.incoming _ (List.mem_of_getElem? parentStored)
      have freshAvoids : Avoids captured.core.representatives held
          (suspendedVars captured.core.counter tries) :=
        fresh_avoids captured.core safe.1 held inside tries
      have inputShape := SourcePruningEnumerationCachedOwn.prepare_inputs
        caller.checked.native.machine.heap parentBucket edge captured own tries projectedResidual
        (symbol, staged, residual) projected prepared
      have stagedSame : staged =
          (SourcePruningEnumerationEdgeInputs.children edge parentBucket captured.core.counter tries).map
            (fun input => (input.1, input.2,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1)) :=
        congrArg (fun result => result.2.1) inputShape
      have indexedSelection := selected
      rw [stagedSame, SourcePruningEnumerationEdgeInputs.children,
        List.map_map, List.getElem?_map] at indexedSelection
      obtain ⟨indexed, indexedStored, selectedSame⟩ := Option.map_eq_some_iff.mp indexedSelection
      rw [List.getElem?_zipIdx] at indexedStored
      obtain ⟨child, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
      have bucketSame : bucket = descendScs position parentBucket ++
          descendScs position (suspendedVars captured.core.counter tries) := by
        simpa only [Nat.zero_add, Function.comp_def] using
          (congrArg (fun input : Child => input.2.1) selectedSame).symm
      have bucketAvoids : Avoids own.core.representatives held bucket := by
        rw [bucketSame]
        have inherited := descend_avoids captured.core.representatives held position parentBucket parentAvoids
        have fresh := descend_avoids captured.core.representatives held position
          (suspendedVars captured.core.counter tries) freshAvoids
        intro sc member related
        have oldRelated := (protection.classes sc.var).mp related
        rcases List.mem_append.mp member with old | added
        · exact inherited sc old oldRelated
        · exact fresh sc added oldRelated
      have parentBounded : ∀ sc ∈ parentBucket, sc.var < own.core.counter := by
        intro sc member
        have oldBound := safe.1.values _ (List.mem_of_getElem? parentStored) sc member
        rw [ownCounter]
        omega
      have freshBounded : ∀ sc ∈ suspendedVars captured.core.counter tries, sc.var < own.core.counter := by
        rw [ownCounter]
        exact suspended_bounded captured.core.counter tries
      have bucketBounded : ∀ sc ∈ bucket, sc.var < own.core.counter := by
        rw [bucketSame]
        intro sc member
        rcases List.mem_append.mp member with old | added
        · exact descend_bounded own.core.counter position parentBucket parentBounded sc old
        · exact descend_bounded own.core.counter position
            (suspendedVars captured.core.counter tries) freshBounded sc added
      exact ⟨protection, ownIsolated, bucketAvoids, ownSafe, bucketBounded⟩

/-- Actual stored and fresh child inputs preserve the same isolated class without an input-avoidance premise. -/
theorem prepared_stored_child_isolated
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (caller reached : Caller (bits + 2)) (captured own after : Cached)
    (parentOwner : Nat) (parentNode : Option Nat) (parentBucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (symbol : Symbol) (staged : List Child)
    (residual : Option Constraint) (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (checkEmpty : Bool) (r n p h k : Nat) (queries saved : Queries)
    (fragment : Fragment) (returned outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (held heldHandle : Nat) (safe : Safe captured.core)
    (isolated : IsolatedPending held heldHandle captured.core)
    (parentStored : captured.core.values[parentOwner]? = some (.unenumerated parentNode parentBucket))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap
      parentBucket edge captured = some [((symbol, staged, residual), own)])
    (selected : staged[position]? = some (incoming, bucket, action))
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming caller own queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after)) :
    EnumerationDriver.Protected held captured.core own.core ∧
      IsolatedPending held heldHandle own.core ∧
      Avoids own.core.representatives held bucket ∧
      IsolatedPending held heldHandle after.core := by
  obtain ⟨protection, ownIsolated, bucketAvoids, ownSafe, bucketBounded⟩ :=
    prepared_stored_child_inputs caller captured own parentOwner parentNode parentBucket
      edge symbol staged residual position incoming bucket action held heldHandle safe isolated
      parentStored prepared selected
  exact ⟨protection, ownIsolated, bucketAvoids,
    SourcePruningEnumerationSharedChildIsolation.observed_isolated_pending
      checkEmpty r n p h k bucket incoming caller reached own after queries saved
      fragment returned outer waiting held heldHandle ownSafe ownIsolated bucketBounded bucketAvoids actual⟩

end MicroCFTA.SourcePruningEnumerationPreparedSharedChildIsolation
