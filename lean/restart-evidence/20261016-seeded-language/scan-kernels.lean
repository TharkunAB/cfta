import MicroCFTA.SourceCurrentConjunctionClassScanSoundness
open MicroCFTA MicroCFTA.Language MicroCFTA.EqualityNormalize
open MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedProbeProvenance
open MicroCFTA.InternedNestedProvenance (Values)
open MicroCFTA.SourceCurrentAllocatedNativeInventoryState (Inventory At)
open MicroCFTA.SourceCurrentConjunctionClassScan
open MicroCFTA.SourceCurrentConjunctionClassScanCompletion (Ranges)
open MicroCFTA.InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (inventory : Inventory)
  {budget : Nat} {u reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
  {classes selected : Constraints} {paths : Class} {before after : Checked width} {memo saved : Memo}
  (actual : Scan budget u reaches values classes before memo (some paths) selected after saved)
  (ready : Ready before) (admitted : At formulas solver inventory before)
  (available : Values before.native.machine.heap values)
  (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
  (active : ∀ paths ∈ classes, Nontrivial paths)
  (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
  (ranges : Ranges budget u reaches values classes before memo)

-- The actual selected class refutation excludes satisfaction of the original full conjunction.
example (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬Satisfies (.node symbol terms) classes := by
  intro satisfied
  have refutes := SourceCurrentConjunctionClassScanSoundness.stopped_refutes formulas solver inventory actual
    ready admitted available proper active correct ranges ambient symbol terms accepted
  exact refutes (satisfied paths (stopped_member actual))

-- A stopped scan derives an actual final inventory and final loaded-field readiness.
example : ∃ next, At formulas solver next after ∧ Ready after ∧
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved := by
  obtain ⟨next, finalReady, finalAdmission, _, _, finalCorrect, _, _⟩ :=
    SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory actual
      ready admitted available proper active correct ranges
  exact ⟨next, finalAdmission, finalReady, finalCorrect⟩

-- Returned fourth-memo entries remain literal entries after the complete reached prefix.
example (key : InternedBinderProtocol.NodeRef) (entry : Value Symbol Guard × Bool)
    (found : memo key = some entry) : saved key = some entry := by
  obtain ⟨_, _, _, _, _, _, retained, _⟩ := SourceCurrentConjunctionClassScanSoundness.verified
    formulas solver inventory actual ready admitted available proper active correct ranges
  exact retained key entry found
end
