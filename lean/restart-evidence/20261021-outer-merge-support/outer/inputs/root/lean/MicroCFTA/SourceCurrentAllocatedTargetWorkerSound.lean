import MicroCFTA.SourceCurrentAllocatedTargetWorker
import MicroCFTA.SourceCurrentAllocatedMergeWorkerSound
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentAllocatedTargetComplete
import MicroCFTA.SourceCurrentAllocatedTargetWorkerNative

/-!
# Current target returns derive their actual checked graphs

Projection and allocated merge returns derive their graphs directly.
Native returns use initial physical readiness, idle tables, resident
closed operands, and reached word ranges. Fold induction derives those
facts at each actual tail return. No final invariant or completed callback
is an input. Failed stages cannot enter a successful continuation.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentAllocatedTargetWorker
open SourceCurrentAllocatedTargetGraph (Operand Fold Target FoldRanges TargetRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat}

/-- Successful sequencing identifies both actual intermediate state components. -/
theorem bind_done (first : Outcome width)
    (next : Value Symbol Guard → Checked width → Memo → Outcome width)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧
        next value middle current = .done result after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual; exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

/-- Successful projection retains the literal forest graph and unchanged merge table. -/
theorem projection_sound [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (result : Value Symbol Guard)
    (after : Checked width) (saved : Memo)
    (done : projection fuel readFuel path values before memo = .done result after saved) :
    ∃ heap, SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap ∧
      after = advancePhysical before ⟨heap, before.operations⟩ ∧ saved = memo := by
  cases actual : SourceEqualityProjectionWorker.forest fuel readFuel path values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [projection, actual] at done; cases done
  | done value heap =>
      simp only [projection, actual] at done
      cases done
      exact ⟨heap, SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ actual, rfl, rfl⟩

/-- Successful merge retains the same actual allocated Call and checked advancement. -/
theorem merge_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (mergeFuel selectionFuel : Nat) (value : Value Symbol Guard)
    (before : Checked width) (memo : Memo) (result : Value Symbol Guard)
    (after : Checked width) (saved : Memo)
    (done : merge mergeFuel selectionFuel value before memo = .done result after saved) :
    SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear value before memo result after saved := by
  cases actual : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
      mergeFuel selectionFuel value (physical before) memo with
  | failed => simp only [merge, actual] at done; cases done
  | done output returned current =>
      simp only [merge, actual] at done
      cases done
      exact .done (SourceCurrentAllocatedMergeWorkerSound.call_sound actual)

/-- An operand return derives projection followed by its literal allocated merge. -/
theorem operand_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : operand projectionFuel readFuel mergeFuel selectionFuel path values before memo = .done result after saved) :
    Operand path values before memo result after saved := by
  obtain ⟨projected, middle, current, projectedDone, mergedDone⟩ := (bind_done _ _ result after saved).mp done
  obtain ⟨heap, actualProjection, rfl, rfl⟩ :=
    projection_sound projectionFuel readFuel path values before memo projected middle current projectedDone
  exact .force actualProjection (merge_sound mergeFuel selectionFuel projected _ _ result after saved mergedDone)

/-- Initial physical checks turn a completed native observation into the actual Step. -/
theorem leaf_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode emptyDomain left right)) before)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : leaf fuel left right before memo = .done result after saved) :
    SourceCurrentAllocatedTargetQuery.Step left right before result after ∧ saved = memo := by
  cases actual : SourceEqualityNativeDemand.execute fuel (.code (requestNode emptyDomain left right)) before with
  | yielded | failed | constraintError | blocked => simp only [leaf, actual] at done; cases done
  | done output final =>
      simp only [leaf, actual] at done
      cases done
      exact ⟨SourceCurrentAllocatedTargetWorkerNative.of_done fuel left right before result after
        good idle leftAvailable rightAvailable leftClosed rightClosed ranges actual, rfl⟩

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

/-- Initial invariants derive physical checks at the same actual right-fold prefixes. -/
theorem fold_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, Domain path values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : FoldRanges values seed paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : fold projectionFuel readFuel mergeFuel selectionFuel nativeFuel values seed paths before memo = .done result after saved) :
    Fold values seed paths before memo result after saved := by
  induction paths generalizing inventory before memo memos result after saved with
  | nil => exact .nil (operand_sound projectionFuel readFuel mergeFuel selectionFuel seed values before memo result after saved done)
  | cons path paths ih =>
      obtain ⟨head, middle, current, operandDone, later⟩ := (bind_done _ _ result after saved).mp done
      have own := operand_sound projectionFuel readFuel mergeFuel selectionFuel path values before memo head middle current operandDone
      obtain ⟨currentMemos, first⟩ := SourceCurrentAllocatedTargetGraph.Operand.verified
        formulas solver inventory own ready admitted available (domains _ (by simp)) stored covered memos valid
      obtain ⟨tail, final, completed, restDone, stepDone⟩ := (bind_done _ _ result after saved).mp later
      have rest := ih inventory middle current first.ready first.admitted first.originals (tail_all domains)
        first.stored first.covered (ranges.1 _ _ _ own) currentMemos first.globals tail final completed restDone
      obtain ⟨next, finalMemos, _, remaining⟩ := SourceCurrentAllocatedTargetComplete.Fold.verified
        formulas solver inventory rest first.ready first.admitted first.originals (tail_all domains)
        first.stored first.covered (ranges.1 _ _ _ own) currentMemos first.globals
      obtain ⟨step, rfl⟩ := leaf_sound nativeFuel head tail final completed remaining.ready.good remaining.ready.idle
        (remaining.effects.keeps.available head first.available) remaining.available first.closed remaining.closed
        (ranges.2 _ _ _ _ _ _ own rest) result after saved stepDone
      exact .cons own rest step

/-- A completed target has the same current graph under its initial reached-check domain. -/
theorem target_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : target projectionFuel readFuel mergeFuel selectionFuel nativeFuel values paths before memo = .done result after saved) :
    Target values paths before memo result after saved := by
  cases paths with
  | nil => cases done; exact .nil
  | cons seed paths =>
      exact .nonempty (fold_sound formulas solver inventory projectionFuel readFuel mergeFuel selectionFuel nativeFuel
        values seed paths before memo ready admitted available domains stored covered ranges memos valid result after saved done)

end MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
