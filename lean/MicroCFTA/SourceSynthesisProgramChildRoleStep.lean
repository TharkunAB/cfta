import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourceSynthesisProgramChildSlots
import MicroCFTA.SourcePruningEnumerationChildEffects
import MicroCFTA.SourcePruningEnumerationIsolatedPending

/-!
# Program roles after one actual child allocation

The event keeps every old marked root and marks the actual fresh child.
Current storage bounds exclude references to the new root.
The transient child bucket must avoid the old marked root classes.
-/
namespace MicroCFTA.SourceSynthesisProgramChildRoleStep
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationReferences InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourceSynthesisProgramEnumerationRoles
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

private theorem fragment_mono {marked extended : Nat → Prop}
    (included : ∀ uv, marked uv → extended uv) {fragment : Fragment Symbol}
    (roles : FragmentRoles literal marked fragment) : FragmentRoles literal extended fragment := by
  induction roles with
  | hole uv known => exact .hole uv (included uv known)
  | component symbol annotation => exact .component symbol annotation
  | application annotation marker function argument _first _second firstIH secondIH =>
      exact .application annotation marker function argument firstIH secondIH
  | filter goal candidates _body ih => exact .filter goal candidates ih

private theorem slot_mono {heap : NativeHeap} {marked extended : Nat → Prop}
    (included : ∀ uv, marked uv → extended uv) {payload : UVarValue Symbol}
    (role : SlotRole valid literal heap marked payload) : SlotRole valid literal heap extended payload := by
  cases role with
  | pending handle scs value decoded fields validTries annotationPaths =>
      exact .pending handle scs value decoded fields validTries annotationPaths
  | enumerated fragment roles => exact .enumerated fragment (fragment_mono included roles)

/-- The same successful child action retains old Program roles and adds its fresh root. -/
theorem program_child_role_step
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap incoming) (closed : incoming.free = [])
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (roles : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ lookupNode heap handle = some incoming ∧
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ∧
      Safe after ∧ ProgramSlots valid literal heap after (fun uv => marked uv ∨ uv = before.counter) := by
  obtain ⟨handle, encoded, decoded⟩ := available_readback heap incoming coherent available closed
  obtain ⟨stored, storedEncoded, fragmentSame, shape⟩ :=
    SourceSynthesisProgramChildSlots.program_child_slot incoming scs fields pathScope before after action fragment prepared actual
  have storedSame : stored = handle := Option.some.inj (storedEncoded.symm.trans encoded)
  subst stored
  obtain ⟨afterSafe, _origin, protects⟩ := SourcePruningEnumerationChildEffects.child scs incoming action before after fragment safe bounded prepared actual
  have forestSame : after.representatives = before.representatives := by
    have projected := congrArg (fun state : Core => state.representatives) shape
    exact projected
  have counterSame : after.counter = before.counter + 1 :=
    congrArg (fun state : Core => state.counter) shape
  have writing : Success (setValue before.counter (.unenumerated (some handle) scs))
      (allocated (some handle) before) () after :=
    (EnumerationDriver.modify_success _ _ _).mpr shape
  have fresh := EnumerationDischargeHistory.allocated_isolated before handle safe
  have freshInside : before.counter < (allocated (some handle) before).values.length :=
    (List.getElem?_eq_some_iff.mp fresh.stored).elim (fun bound _ => bound)
  have freshStored : after.values[before.counter]? = some (.unenumerated (some handle) scs) := by
    simpa only [shape] using (List.getElem?_set_self freshInside :
      ((allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs))[before.counter]? =
        some (.unenumerated (some handle) scs))
  have freshRoot : IsRoot after.representatives before.counter := by
    rw [forestSame]
    exact fresh.root
  have bucketFresh : Avoids before.representatives before.counter scs := by
    intro sc member same
    have equal := outside_class before.representatives before.counter before.counter sc.var safe.1.forest (Nat.le_refl _) same
    have inside := bounded sc member
    omega
  have freshIncoming : IncomingAvoid before.counter after := by
    have written := setValue_allowed (fun uv => ¬UnionFind.SameClass before.representatives before.counter uv)
      before.counter (.unenumerated (some handle) scs) (allocated (some handle) before) after
      fresh.incoming bucketFresh writing
    simpa only [IncomingAvoid, forestSame] using written
  refine ⟨handle, encoded, decoded, fragmentSame, shape, afterSafe, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    rw [counterSame]
    rcases known with old | rfl
    · exact Nat.lt_succ_of_lt (roles.bounded uv old)
    · exact Nat.lt_succ_self _
  · intro uv known
    rcases known with old | rfl
    · exact (protects uv (roles.bounded uv old) (roles.roots uv old)).root
    · exact freshRoot
  · intro uv known
    rcases known with old | rfl
    · have allocatedIncoming := allocation_allowed
        (fun target => ¬UnionFind.SameClass before.representatives uv target) (some handle) before (roles.incoming uv old)
      have written := setValue_allowed (fun target => ¬UnionFind.SameClass before.representatives uv target)
        before.counter (.unenumerated (some handle) scs) (allocated (some handle) before) after
        allocatedIncoming (avoids uv old) writing
      simpa only [IncomingAvoid, forestSame] using written
    · exact freshIncoming
  · intro uv known
    rcases known with old | rfl
    · obtain ⟨payload, stored, role⟩ := roles.stored uv old
      exact ⟨payload, (protects uv (roles.bounded uv old) (roles.roots uv old)).value.trans stored,
        slot_mono (fun _ known => Or.inl known) role⟩
    · refine ⟨.unenumerated (some handle) scs, freshStored, ?_⟩
      refine .pending handle scs incoming decoded fields (fun sc member => (pathScope sc member).1) ?_
      intro sc member path listed
      obtain ⟨tail, same⟩ := (pathScope sc member).2 path listed
      exact ⟨tail, same.symm⟩

end MicroCFTA.SourceSynthesisProgramChildRoleStep
