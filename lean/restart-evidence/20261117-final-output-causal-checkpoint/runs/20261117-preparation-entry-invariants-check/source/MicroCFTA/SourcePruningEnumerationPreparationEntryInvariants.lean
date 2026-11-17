import MicroCFTA.SourcePruningEnumerationSelectedPrefixRawAliases
import MicroCFTA.SourcePruningEnumerationObservedEntryCanonical
import MicroCFTA.SourcePruningEnumerationRawAliasPrimitives
import MicroCFTA.SourcePruningEnumerationStagedChildRoots

namespace MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRawAliasPrimitives
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList
set_option autoImplicit false

/- Note [Entry qualifications from one actual preparation]
A successful entry retains every old finite raw alias.
An old self-alias therefore gives Total at that same entered Core.
The original actual preparation receipt supplies its exact bucket.
The existing canonical entry observer proves that bucket valid.
The prefix corollary combines the actual canonical and alias observers.
All supplied fuels and native endpoints remain unchanged.
The entry alias proof reuses the checked c4 proof text locally.
It does not call its private declaration across modules.
No future history, Packet, resource or model is supplied.
-/

theorem enter_sameClass_forward
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (result : Nat × Nat × List Suspended × Node)
    (actual : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right
 := by
  unfold SourcePruningEnumerationEntry.enter at actual
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
  have first : ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass middle.representatives left right := by
    obtain ⟨found, lookup, _stored, rfl⟩ := (getValue_success fuel uv before middle value).mp reading
    exact findRoot_sameClass_forward fuel uv before.representatives found lookup
  cases value with
  | eliminated | enumerated _ => simp [Success, reject, ExceptT.run] at continued
  | unenumerated node scs =>
      cases node with
      | none => simp [Success, reject, ExceptT.run] at continued
      | some handle =>
          obtain ⟨target, compressed, represented, final⟩ := (success_bind _ _ _ _ _).mp continued
          have second := representative_sameClass_forward fuel uv target middle compressed represented
          cases decoded : lookupNode heap handle with
          | none =>
              simp only [decoded] at final
              exact (success_failure .unresolvedReference compressed after result final).elim
          | some decodedValue =>
              simp only [decoded] at final
              obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp final
              cases token
              have shape := (EnumerationDriver.modify_success _ compressed written).mp writing
              have forest : written.representatives = compressed.representatives := by
                simpa only using congrArg (fun state : Core => state.representatives) shape
              obtain ⟨_resultSame, afterSame⟩ := (success_pure _ result written after).mp finished
              subst after
              intro left right same
              rw [forest]
              exact second left right (first left right same)

variable [DecidableEq (EdgeKey Symbol Constraint)]

theorem successful_preparation_entry_invariants
    (entryFuel nativeFuel uv target handle : Nat) (bucket : List Suspended)
    (caller : Caller width) (before : Cached) (entered : Core) (decoded result : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, bucket, decoded), entered)], some (.done result heap))) :
    UnionFind.Total entered.representatives ∧ Canonical entered ∧ ValidSuspended bucket ∧
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass entered.representatives left right
 := by
  have facts := SourcePruningEnumerationObservedEntryCanonical.successful_preparation_bucket_valid
    entryFuel nativeFuel uv target handle bucket caller before entered decoded result heap canonical observed
  have reading := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    entryFuel uv before.core) = [.ok ((target, handle, bucket, decoded), entered)] at reading
  have successful : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      entryFuel uv) before.core (target, handle, bucket, decoded) entered := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have aliases := enter_sameClass_forward caller.checked.native.machine.heap entryFuel uv before.core entered
    (target, handle, bucket, decoded) successful
  have totalEntered := SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
    before.core.representatives entered.representatives total aliases
  exact ⟨totalEntered, facts.1, facts.2, aliases⟩

theorem runPrefix_entry_invariants
    {Typing Key : Type}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives) :
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries with
    | .stopped _ _ => True
    | .parked checked candidate _ =>
        UnionFind.Total checked.representatives ∧ Canonical checked ∧
          ∀ after, candidate = some after →
            UnionFind.Total after.core.representatives ∧ Canonical after.core
    | .narrowed checked _ _ _ _ candidate _ _ =>
        UnionFind.Total checked.representatives ∧ Canonical checked ∧
          ∀ after, candidate = some after →
            UnionFind.Total after.core.representatives ∧ Canonical after.core
 := by
  have canonicalFacts := SourcePruningEnumerationObservedEntryCanonical.runPrefix_canonical
    holeKey fits admits graph templates stop order metadata
    readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries canonical
  have aliasFacts := SourcePruningEnumerationSelectedPrefixRawAliases.runPrefix_sameClass_forward
    holeKey fits admits graph templates stop order metadata
    readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries
  generalize actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
    metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries = result
      at canonicalFacts aliasFacts ⊢
  cases result with
  | stopped reading checked => trivial
  | parked checked candidate raw =>
      refine ⟨SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
        before.core.representatives checked.representatives total aliasFacts.1, canonicalFacts.1, ?_⟩
      intro after attached
      exact ⟨SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
        before.core.representatives after.core.representatives total (aliasFacts.2 after attached),
        canonicalFacts.2 after attached⟩
  | narrowed checked prepared reached saved action candidate right ordinary =>
      refine ⟨SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
        before.core.representatives checked.representatives total aliasFacts.1, canonicalFacts.1, ?_⟩
      intro after attached
      exact ⟨SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
        before.core.representatives after.core.representatives total (aliasFacts.2 after attached),
        canonicalFacts.2 after attached⟩

end MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants

#check MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.enter_sameClass_forward
#print axioms MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.enter_sameClass_forward
#check MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
#print axioms MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants

#check MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
#print axioms MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
