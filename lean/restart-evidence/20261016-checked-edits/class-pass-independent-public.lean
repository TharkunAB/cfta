import MicroCFTA.SourceCurrentAllocatedClassPass

open MicroCFTA
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass

#print axioms SourceCurrentAllocatedClassPass.Fold.verified
#print axioms SourceCurrentAllocatedClassPass.fold_complete
#print axioms SourceCurrentAllocatedClassPass.Pass.verified
#print axioms SourceCurrentAllocatedClassPass.pass_complete
#print axioms SourceCurrentAllocatedClassPass.Receipt.fourth_correct
#check @SourceCurrentAllocatedClassPass.Fold.verified
#check @SourceCurrentAllocatedClassPass.fold_complete
#check @SourceCurrentAllocatedClassPass.Pass.verified
#check @SourceCurrentAllocatedClassPass.pass_complete
#check @SourceCurrentAllocatedClassPass.Receipt.fourth_correct

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Class" => SourceCurrentAllocatedClassEdits.Class
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

-- The actual two-class graph captures the tail's literal forest and warm tables.
theorem two_class_actual_capture {head tail : SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    (actual : Fold [head, tail] values before memo results after saved) :
    ∃ middle step current,
      Class tail values before memo middle step current ∧ Class head middle step current results after saved := by
  cases actual with
  | cons tailActual headActual =>
      cases tailActual with
      | cons nilActual tailClass =>
          cases nilActual
          exact ⟨_, _, _, tailClass, headActual⟩

-- No classes leave the whole checked state and merge table unchanged.
example {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    (actual : Fold [] values before memo results after saved) :
    results = values ∧ after = before ∧ saved = memo := by
  cases actual
  exact ⟨rfl, rfl, rfl⟩

-- The empty pass still performs the literal final propagation in the same state.
example {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    (actual : Pass [] values before memo results after saved) :
    results = EqualityLeafProjectionRuntimeEmpty.propagate values ∧ after = before ∧ saved = memo := by
  cases actual with
  | done folded =>
      cases folded
      exact ⟨rfl, rfl, rfl⟩

-- An empty pass retains the identical global bundle, with no helper calls.
example {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {actual : Pass [] values before memo results after saved} {memos final : Memos}
    (reads : PassReads formulas solver actual memos final) : final = memos := by
  cases reads with
  | done read => cases read; rfl

-- Literal empty propagation also erases an unrelated open sibling without allocation.
example (input : Value Symbol Guard) :
    EqualityLeafProjectionRuntimeEmpty.propagate [.empty, input] = [.empty, .empty] := rfl

variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)

-- Finite two-class execution derives both successive inventories at the actual states.
theorem two_class_inventory_carry (inventory : Inventory)
    (head tail : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo)
    (ranges : Ranges [head, tail] values before memo)
    (coherent : ∀ record ∈ [head, tail], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [head, tail], EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ [head, tail], ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ middle step current middleInventory results after saved finalInventory,
      Fold [tail] values before memo middle step current ∧
      Class head middle step current results after saved ∧
      At formulas solver middleInventory step ∧ At formulas solver finalInventory after ∧
      Extends memo current ∧ Extends current saved ∧ Ready after := by
  cases ranges with
  | cons tailRanges headRanges =>
      obtain ⟨middle, step, current, middleInventory, currentMemos, tailActual, _, first⟩ :=
        fold_complete formulas solver inventory tailRanges
          (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => active record (List.mem_cons_of_mem _ member)) ready admitted available
          (fun record member => domains record (List.mem_cons_of_mem _ member)) stored covered memos valid
      obtain ⟨results, after, saved, finalInventory, _, headActual, _, last⟩ :=
        SourceCurrentAllocatedClassEdits.finite formulas solver middleInventory head
          (coherent head (by simp)) (active head (by simp)) middle step current first.ready first.admitted
          first.available (fun path member => first.domains _ (domains head (by simp) path member))
          first.stored first.covered (headRanges middle step current tailActual) currentMemos first.globals.valid
      exact ⟨middle, step, current, middleInventory, results, after, saved, finalInventory,
        tailActual, headActual, first.admitted, last.admitted, first.retained, last.retained, last.ready⟩

-- Initial obligations derive pass narrowing and all-class conditional equivalence.
theorem finite_pass_language (inventory : Inventory)
    (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo)
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved, Pass records values before memo results after saved ∧
      ∀ ambient symbol terms,
        (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
        ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
          (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
  obtain ⟨results, after, saved, _, _, actual, _, receipt⟩ := pass_complete formulas solver inventory
    ranges coherent active ready admitted available domains stored covered memos valid
  exact ⟨results, after, saved, actual, receipt.language⟩

-- Any annotated actual pass derives its receipt at the literal returned full state.
example (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final :=
  Pass.verified formulas solver inventory reads coherent active ready admitted available domains stored covered valid

-- Heap growth retains the same immutable fourth table.
example {inventory : Inventory} {records values results} {before after : Checked width}
    {memo saved : Memo} {memos final : Memos}
    (receipt : Receipt formulas solver inventory records values before memo results after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth :=
  receipt.fourth_correct formulas solver fourth correct

-- Finite execution derives fourth-table retention without a final receipt premise.
example (inventory : Inventory)
    (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo)
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    ∃ results after saved, Pass records values before memo results after saved ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth := by
  obtain ⟨results, after, saved, _, _, actual, _, receipt⟩ := pass_complete formulas solver inventory
    ranges coherent active ready admitted available domains stored covered memos valid
  exact ⟨results, after, saved, actual, receipt.fourth_correct formulas solver fourth correct⟩

#print axioms two_class_actual_capture
#print axioms two_class_inventory_carry
#print axioms finite_pass_language
