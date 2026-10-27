import MicroCFTA.SourceFlatPruningPrefixCompletion
import MicroCFTA.SourcePruningEnumerationRecursivePrefixLanguage
import MicroCFTA.EnumerationFlatSemantics

/-!
# Assignment meaning of actual flat selected prefixes

The original flat producer retains its complete validity and cache packet.
The actual narrowed cache has backward meaning at its own native heap.
The parked law retains the original bucket readback and removed restrictions.
-/
namespace MicroCFTA.SourceFlatPruningSelectedPrefix
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "OldCached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}

/-- Interpret the actual flat endpoint and keep the original parked bucket readback. -/
def PrefixMeaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached)
    (observed : Result width Typing) : Prop :=
  match observed with
  | .stopped _ _ | .parked _ none _ => False
  | .parked _ (some after) _ =>
      ∃ (oldHandle : Nat) (scs : List Suspended)
        (readAfter : EnumerationState.State Symbol Constraint),
        before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
        ExceptT.run (getValue fuel uv before.core) =
          [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
        ∀ ambient residualMeaning assignment,
          EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment flat.core ↔
          EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment after.core ∧
          ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc
  | .narrowed _ _ reached _ _ (some after) _ =>
      ∀ ambient residualMeaning assignment,
        EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
          residualMeaning assignment after.core →
        EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment flat.core
  | .narrowed _ _ _ _ _ none _ => True

/-- The actual ordered result relation transports both assignment endpoints. -/
theorem related_prefix_meaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached)
    (input : EnumerationFlatCached.Related flat before)
    (observed : Result width Typing)
    (earlier : SourcePruningEnumerationSelectedStep.Result width Typing)
    (related : ResultRelated observed earlier)
    (meaning : SourcePruningEnumerationSelectedStep.PrefixMeaning formulas solver fuel uv caller before earlier) :
    PrefixMeaning formulas solver fuel uv caller before flat observed := by
  cases observed with
  | stopped read checked =>
      cases earlier with
      | stopped _ _ => exact meaning
      | parked _ _ _ | narrowed _ _ _ _ _ _ _ _ => exact related.elim
  | parked checked candidate raw =>
      cases earlier with
      | stopped _ _ | narrowed _ _ _ _ _ _ _ _ => exact related.elim
      | parked oldChecked oldCandidate oldRaw =>
          cases oldCandidate with
          | none => exact meaning.elim
          | some oldAfter =>
              cases candidate with
              | none => exact related.2.1.elim
              | some after =>
                  obtain ⟨handle, scs, readAfter, stored, read, semantics⟩ := meaning
                  refine ⟨handle, scs, readAfter, stored, read, ?_⟩
                  intro ambient residualMeaning assignment
                  have beforeMeaning := EnumerationFlatState.related_satisfies input.core
                    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                      ambient caller.checked.native.machine.heap) residualMeaning assignment
                  have afterMeaning := EnumerationFlatState.related_satisfies related.2.1.core
                    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                      ambient caller.checked.native.machine.heap) residualMeaning assignment
                  exact beforeMeaning.symm.trans ((semantics ambient residualMeaning assignment).trans
                    (and_congr afterMeaning Iff.rfl))
  | narrowed checked prepared reached queries action candidate right =>
      cases earlier with
      | stopped _ _ | parked _ _ _ => exact related.elim
      | narrowed oldChecked oldPrepared oldReached oldQueries oldAction oldCandidate oldRight ordinary =>
          obtain ⟨_checked, _prepared, callerSame, _queries, _action, writes, _right, _ordinary⟩ := related
          subst oldReached
          cases candidate with
          | none => trivial
          | some after =>
              cases oldCandidate with
              | none => exact writes.elim
              | some oldAfter =>
                  intro ambient residualMeaning assignment satisfied
                  have earlierSatisfied := (EnumerationFlatState.related_satisfies writes.core
                    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                      ambient reached.checked.native.machine.heap) residualMeaning assignment).mpr satisfied
                  have original := meaning ambient residualMeaning assignment earlierSatisfied
                  exact (EnumerationFlatState.related_satisfies input.core
                    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                      ambient caller.checked.native.machine.heap) residualMeaning assignment).mp original

variable [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq Symbol] [DecidableEq Node]

variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
variable (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (fuel uv : Nat) (caller : Caller width) (memos : Memos)
variable (before : OldCached)

/-- The complete original flat prefix packet also certifies its actual backward assignment law. -/
theorem packet_prefix_complete_semantics
    (caller : Caller width) (memos : Memos) (before : OldCached) (flat : FlatCached)
    (related : EnumerationFlatCached.Related flat before)
    (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound,
      ((∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (bound + extra) selected caller before memos
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query)) ∧
      ∀ extra selected,
        SourceFlatPruningRestart.decision stop order metadata flat = some (.expand selected) →
        ResultRelated
          (run holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) selected caller flat memos.query)
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query) ∧
        match run holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) selected caller flat memos.query with
        | .parked _ (some after) _ =>
            ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
              Packet formulas solver inventory caller memos metadata oldAfter ∧
              EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap after
        | .narrowed _ _ reached queries _ candidate _ =>
            ∃ final : Memos, Post formulas solver inventory caller reached final ∧
              final.query = queries ∧
              match candidate with
              | none => True
              | some after =>
                  ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
                    Packet formulas solver inventory reached final metadata oldAfter ∧
                    EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap after
        | _ => True) ∧
      ∀ extra selected,
        SourceFlatPruningRestart.decision stop order metadata flat = some (.expand selected) →
        PrefixMeaning formulas solver (bound + extra) selected caller before flat
          (run holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) selected caller flat memos.query) := by
  obtain ⟨bound, original, actual⟩ := packet_prefix_complete holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before flat related packet
  refine ⟨bound, ⟨original, actual⟩, ?_⟩
  intro extra selected chosen
  have oldChosen := (SourceFlatPruningRestart.decision_related related stop order metadata).symm.trans chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have semantic := SourcePruningEnumerationSelectedStep.prefix_semantics holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory (bound + extra) selected caller before memos
    packet.context
    (SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory stop order metadata
      caller memos before selected packet oldChosen) realized (original extra selected oldChosen)
  exact related_prefix_meaning formulas solver (bound + extra) selected caller before flat related _ _
    (actual extra selected chosen).1 semantic

end MicroCFTA.SourceFlatPruningSelectedPrefix
