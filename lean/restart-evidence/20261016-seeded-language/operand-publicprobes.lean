import MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage

open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

#print axioms SourceCurrentAllocatedSeededOperandLanguage.Operand.effects
#print axioms SourceCurrentAllocatedSeededOperandLanguage.Operand.included
#check @SourceCurrentAllocatedSeededOperandLanguage.Operand.effects
#check @SourceCurrentAllocatedSeededOperandLanguage.Operand.included

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def external : Value Symbol Guard := .reference (.uninterned 999)
private def fixtureForest (value : Value Symbol Guard) : List (Value Symbol Guard) := [value, external]
private def reached (before : Checked width) : Checked width :=
  SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨before.native.machine.heap, before.operations⟩

private theorem actual (before : Checked width) (value : Value Symbol Guard) :
    Operand [0] (fixtureForest value) before value (reached before) :=
  .force value before.native.machine.heap (.selected rfl .root)

private theorem supported (u : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (value : Value Symbol Guard) (closed : value.free = []) : PathSupport u anchor [0] (fixtureForest value) := by
  refine ⟨[0], rfl, ?_⟩
  change ∀ child, some value = some child → _
  intro child found
  cases found
  exact Or.inl closed

example (before : Checked 8) (value : Value Symbol Guard) :
    Operand [0] (fixtureForest value) before value (reached before) := actual before value

example (value : Value Symbol Guard) : ¬MergedColdReaderClosedInputs.ClosedValues (fixtureForest value) := by
  intro closed
  have impossible := closed external (by simp [fixtureForest])
  cases impossible

example (u : Value Symbol Guard → Bool) (anchor : State Symbol Guard) :
    PathSupport u anchor [0] (fixtureForest .empty) := supported u anchor .empty rfl

example (before : Checked 8) :
    (reached before).operations = before.operations ∧
      (reached before).native.nodes = before.native.nodes ∧
      (reached before).native.edges = before.native.edges ∧
      (reached before).native.machine.domains = before.native.machine.domains := ⟨rfl, rfl, rfl, rfl⟩

example (u : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (before : Checked 8) (value : Value Symbol Guard) (closed : value.free = [])
    (good : Good before) (ready : Ready (physical before))
    (scopes : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (available : Values before.native.machine.heap (fixtureForest value)) (growth : Grows anchor before.native.machine.heap) :
    Good (reached before) ∧ Effects (physical before) (physical (reached before)) ∧
      Extension before.native.machine (reached before).native.machine ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped (reached before).native ∧
      SourceRecursiveIntersectionNative.Idle (reached before).native ∧
      Available (reached before).native.machine.heap value ∧ value.free = [] :=
  SourceCurrentAllocatedSeededOperandLanguage.Operand.effects u anchor anchorSemantic anchorReady
    (actual before value) good ready scopes idle available growth (supported u anchor value closed)

example (u : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (before : Checked 8) (value : Value Symbol Guard) (closed : value.free = [])
    (ready : Ready (physical before))
    (available : Values before.native.machine.heap (fixtureForest value)) (growth : Grows anchor before.native.machine.heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) (fixtureForest value) terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) [0] = some part) : meaning holds ambient value part :=
  SourceCurrentAllocatedSeededOperandLanguage.Operand.included u anchor anchorSemantic anchorReady
    (actual before value) ready available growth (supported u anchor value closed) (by decide)
    holds ambient symbol terms part accepted selected
