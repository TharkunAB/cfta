import MicroCFTA.SourceCurrentConjunctionScanClassPass

#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPass.from_scan
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPass.finite
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.from_scan
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.finite

namespace MicroCFTA.ScanClassPassIndependentProbe
open Language InternedConstructorTemplates SourceCurrentConjunctionScanClassPass
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "meaning" => InternedGuardedLanguage.meaning
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

-- A stopped zero-child branch retains the literal Scan return and both memo outputs.
example {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo : Memo}
    {paths : EqualityNormalize.Class} {selected : EqualityNormalize.Constraints}
    (scan : SourceCurrentConjunctionClassScan.Scan budget source reaches [] (records.map SourceEqualityClassOrder.Record.paths)
      before fourth (some paths) selected after savedFourth)
    {memos final : Memos} (scanReads : SourceCurrentConjunctionClassScanGlobalMemos.ScanReads scan memos final)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ actual : Reduction budget records [] before fourth memo (some paths) [] after savedFourth memo,
      Reads formulas solver actual memos final :=
  ⟨.stopped scan, .stopped scanReads⟩

-- Erasure of zero child slots still denotes the empty ordered forest.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      (EqualityLeafProjectionRuntimeEmpty.erase ([] : List (Value Symbol Guard))) [] := .nil

-- The receipt's conditional exactness uses all original records, rather than only kept classes.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option EqualityNormalize.Class} {final : Memos}
    (receipt : Receipt formulas solver inventory records values results before after fourth savedFourth memo saved outcome final)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : ∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) :
    results.length = values.length ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final ∧
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :=
  ⟨receipt.length, receipt.globals, (receipt.language ambient symbol terms).2 satisfied⟩

end MicroCFTA.ScanClassPassIndependentProbe
