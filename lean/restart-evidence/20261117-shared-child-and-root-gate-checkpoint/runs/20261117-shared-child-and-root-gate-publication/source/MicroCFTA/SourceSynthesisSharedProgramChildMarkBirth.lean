import MicroCFTA.SourceSynthesisProgramChildRoleStep
import MicroCFTA.SourcePruningEnumerationSharedShallowFootprint

namespace MicroCFTA.SourceSynthesisSharedProgramChildMarkBirth
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [One observed shared Program-child birth]
The existing raw role step marks the actual allocated Program root.
The shared footprint fixes its action, returned Core and cached endpoint
from the same literal dispatch singleton and original five fuels.
These two receipts use the same action and success. Encoding equality
identifies their explicit handles. No history proof index joins data.
A source Program value is empty or ordinary. A successful one is ordinary
and stores the full annotation bucket. Mu and Union annotation fallbacks
have a different empty-bucket footprint and do not acquire Program marks.
-/

/-- One literal shared Program-child success marks its exact fresh root with the full bucket. -/
theorem successful_program_child_mark_birth
    (valid : Constraint → Prop) (literal : String → Symbol)
    (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (incoming : Node) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (available : Available caller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (marked : Nat → Prop) (safe : Safe before.core)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (avoids : ∀ uv, marked uv → Avoids before.core.representatives uv scs)
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after)) :
    ∃ handle,
      SourcePruningEnumerationNodes.encodeNode incoming = some handle ∧
      SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some incoming ∧
      fragment = .hole before.core.counter ∧ reached = caller ∧ saved = queries ∧
      read = before.core ∧ waiting = before.waiting ∧ after.core = returned ∧
      after.core = {allocated (some handle) before.core with
        values := (allocated (some handle) before.core).values.set before.core.counter (.unenumerated (some handle) scs)} ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) scs) ∧
      after.core.counter = before.core.counter + 1 ∧ Safe after.core ∧
      ProgramSlots valid literal reached.checked.native.machine.heap after.core
        (fun uv => marked uv ∨ uv = before.core.counter)
 := by
  have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
    apply List.any_eq_false.mpr
    intro sc member tagged
    have terminal : sc.trie = .terminal := by
      cases trieRead : sc.trie with
      | empty =>
          simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
      | terminal => rfl
      | branch children =>
          simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    obtain ⟨tail, impossible⟩ := (pathScope sc member).2 []
      ((EqualityTrie.nil_mem sc.trie).mpr terminal)
    cases impossible
  have receipt := SourcePruningEnumerationSharedShallowFootprint.nonterminal_success_footprint
    checkEmpty r n p h k scs incoming caller reached before after queries saved fragment
    returned read waiting nonterminal actual
  dsimp only at receipt
  obtain ⟨handle, _decoded, _flag, action, _nonempty, encoded, _readback, _classified,
      prepared, raw, _cached, fragmentSame, callerSame, querySame, readSame, waitingSame,
      coreSame, _footprintShape, counterSame, _fresh⟩ := receipt
  have success : Success action before.core fragment returned := by
    rw [Success, raw]
    exact List.mem_singleton_self _
  obtain ⟨actualHandle, actualEncoded, actualDecoded, _fragmentSame,
      returnedShape, returnedSafe, returnedRoles⟩ :=
    SourceSynthesisProgramChildRoleStep.program_child_role_step caller.checked.native.machine.heap
      incoming scs coherent available closed fields pathScope before.core returned marked
      safe slots bounded avoids action fragment prepared success
  have handleSame : actualHandle = handle := Option.some.inj (actualEncoded.symm.trans encoded)
  subst actualHandle
  have afterShape : after.core = {allocated (some handle) before.core with
      values := (allocated (some handle) before.core).values.set before.core.counter (.unenumerated (some handle) scs)} := coreSame.trans returnedShape
  have allocatedStored := EnumerationState.allocated_slot (some handle) before.core safe.1.aligned
  have freshInside : before.core.counter < (allocated (some handle) before.core).values.length :=
    (List.getElem?_eq_some_iff.mp allocatedStored).1
  have freshStored : after.core.values[before.core.counter]? =
      some (.unenumerated (some handle) scs) := by
    rw [afterShape]
    exact List.getElem?_set_self freshInside
  have afterSafe : Safe after.core := by
    rw [coreSame]
    exact returnedSafe
  have afterRoles : ProgramSlots valid literal reached.checked.native.machine.heap after.core
      (fun uv => marked uv ∨ uv = before.core.counter) := by
    rw [callerSame, coreSame]
    exact returnedRoles
  exact ⟨handle, encoded, actualDecoded, fragmentSame, callerSame, querySame, readSame,
    waitingSame, coreSame, afterShape, freshStored, counterSame, afterSafe, afterRoles⟩

end MicroCFTA.SourceSynthesisSharedProgramChildMarkBirth

#check @MicroCFTA.SourceSynthesisSharedProgramChildMarkBirth.successful_program_child_mark_birth
#print axioms MicroCFTA.SourceSynthesisSharedProgramChildMarkBirth.successful_program_child_mark_birth
