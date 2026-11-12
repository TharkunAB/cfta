import MicroCFTA.SourceSynthesisProgramChildRoleStep

/-!
# Retained buckets across the actual Program child allocation

The existing child event retains its full action and role receipt.
Old roots stay protected. A current bounded bucket cannot name the fresh root.
The same bucket keeps its exclusion from every old marked class.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesChildRetained
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

/-- One actual child event protects old roots and excludes all marks from retained buckets. -/
theorem program_child_retained
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
    ∃ handle, (encodeNode incoming = some handle ∧ lookupNode heap handle = some incoming ∧
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ∧
      Safe after ∧ ProgramSlots valid literal heap after (fun uv => marked uv ∨ uv = before.counter)) ∧
      (∀ uv, marked uv → EnumerationDriver.Protected uv before after) ∧
      (∀ retained : List Suspended,
        (∀ sc ∈ retained, sc.var < before.counter) →
        (∀ uv, marked uv → Avoids before.representatives uv retained) →
        (∀ sc ∈ retained, sc.var < after.counter) ∧
        ∀ uv, marked uv ∨ uv = before.counter → Avoids after.representatives uv retained) := by
  obtain ⟨handle, original⟩ := SourceSynthesisProgramChildRoleStep.program_child_role_step
    heap incoming scs coherent available closed fields pathScope before after marked safe roles
    bounded avoids action fragment prepared actual
  have receipt := original
  rcases receipt with ⟨encoded, decoded, fragmentSame, shape, afterSafe, afterRoles⟩
  have forestSame : after.representatives = before.representatives := by
    have projected := congrArg (fun state : Core => state.representatives) shape
    exact projected
  have counterSame : after.counter = before.counter + 1 :=
    congrArg (fun state : Core => state.counter) shape
  have protects : ∀ uv, marked uv → EnumerationDriver.Protected uv before after := by
    intro uv tagged
    have inside := roles.bounded uv tagged
    have prior := EnumerationDriver.allocation_protected uv (some handle) before safe
      inside (roles.roots uv tagged)
    refine ⟨?_, ?_, ?_⟩
    · rw [shape]
      change ((allocated (some handle) before).values.set before.counter
        (.unenumerated (some handle) scs))[uv]? = _
      rw [List.getElem?_set_ne (Nat.ne_of_gt inside)]
      exact prior.value
    · rw [forestSame]
      exact roles.roots uv tagged
    · intro other
      rw [forestSame]
  refine ⟨handle, original, protects, ?_⟩
  intro retained retainedBounds oldAvoids
  refine ⟨?_, ?_⟩
  · intro sc member
    rw [counterSame]
    exact Nat.lt_succ_of_lt (retainedBounds sc member)
  · intro uv tagged
    rw [forestSame]
    rcases tagged with old | rfl
    · exact oldAvoids uv old
    · intro sc member same
      have equal := outside_class before.representatives before.counter before.counter sc.var
        safe.1.forest (Nat.le_refl _) same
      have inside := retainedBounds sc member
      omega

end MicroCFTA.SourceSynthesisProgramRolesChildRetained
