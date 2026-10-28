import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildProjectionHeap

/-!
# Projection heaps at actual selected opaque returns

The actual child observation supplies its reached native caller.
Finalization writes the enumeration cache and retains that caller.
The stored source handle and prepared input value remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => Heap projectable
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original opaque inputs retain projection at the exact supported returned caller. -/
theorem run_projection_heap (seed : Seed)
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {target originalHandle : Nat} {scs : List Suspended} {value : Node}
    (packet : Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap)
    (r n p h k : Nat) :
    match run checkEmpty r n p h k target scs value caller before memos.query with
    | some (.complete _ reached _ _) => ProjectionHeap reached.checked.native.machine.heap
    | some (.rejected reached _ _) => ProjectionHeap reached.checked.native.machine.heap
    | some (.stopped _ (.ok _, reached, _, _, _) _) =>
        ProjectionHeap reached.checked.native.machine.heap
    | _ => True := by
  obtain ⟨roots, paths, _storage, realized, counts, _flags⟩ := packet.valid
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    packet.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core packet.pending
    target (some originalHandle) scs stored
  let originalValue := value
  generalize observed : run checkEmpty r n p h k target scs value caller before memos.query = result
  cases value
  case empty =>
    simp only [run, ↓reduceIte] at observed
    rw [← observed]
    exact originalProjection
  case' reference =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' mu =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' union =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' node entry edges depth free =>
    cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie)
    case false =>
      simp only [run, reduceCtorEq, terminal, Bool.not_false, ↓reduceIte] at observed
      rw [← observed]
      trivial
    case' true =>
      simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at observed
  all_goals
    rcases childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
        scs originalValue caller before memos.query with
      ⟨⟨outcome, reached, saved, outer, waiting⟩, candidate⟩
    dsimp only [originalValue] at childRun
    rw [childRun] at observed
    cases outcome with
    | error _fault =>
        rw [← observed]
        trivial
    | ok raw =>
        have reachedProjection :=
          (SourcePruningEnumerationChildDispatch.observed_resources_projection_heap
            seed formulas solver inventory caller before checkEmpty r n p h k scs originalValue roots memos
            packet.context packet.safe paths counts realized bounded pending available closed fits reserved
            known originalProjection childRun).2.2
        cases raw with
        | none => rw [← observed]; exact reachedProjection
        | some rows =>
            cases rows with
            | nil => rw [← observed]; exact reachedProjection
            | cons first rest =>
                cases first with
                | error _fault => rw [← observed]; exact reachedProjection
                | ok pair =>
                    rcases pair with ⟨fragment, returned⟩
                    cases rest with
                    | cons _next _tail => rw [← observed]; exact reachedProjection
                    | nil =>
                        cases candidate with
                        | none => rw [← observed]; exact reachedProjection
                        | some middle =>
                            cases finished : SourcePruningEnumerationFinalize.run
                                reached.checked.native.machine.heap k target fragment middle with
                            | none =>
                                simp only [finished, Option.map_none] at observed
                                rw [← observed]
                                trivial
                            | some after =>
                                simp only [finished, Option.map_some] at observed
                                rw [← observed]
                                exact reachedProjection

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
