import MicroCFTA.SourceSizedPrefixProductOrdinary
import MicroCFTA.SourcePruningEnumerationConstructedResources

/-!
# Initial admission for the ranked size-product construction

Original row annotations supply the cached equality gate.
The actual constructed root retains its finite ordinary height bound.
The literal public-query and SCC/memo correspondence remain separate.
-/
namespace MicroCFTA.SourceSizedPrefixProductInitial
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)
open SourceSizedDecided (Row)

section Origins
variable {Q Symbol Guard : Type}
private theorem child_guards (valid : Guard → Prop) (child : Q → Syntax Symbol Guard)
    (states : List Q) (checked : ∀ current ∈ states, ∀ guard ∈ guards (child current), valid guard) :
    ∀ guard ∈ childGuards (states.map child), valid guard := by
  induction states with
  | nil => simp [childGuards]
  | cons current rest ih =>
      intro guard member
      simp only [List.map_cons, childGuards, List.mem_append] at member
      rcases member with first | later
      · exact checked current List.mem_cons_self guard first
      · exact ih (fun item listed => checked item (List.mem_cons_of_mem _ listed)) guard later

private theorem layer_guards (valid : Guard → Prop) (rows : List (Row Q Symbol Guard))
    (child : Q → Syntax Symbol Guard) (checked : ∀ row ∈ rows, valid row.constraint)
    (children : ∀ row ∈ rows, ∀ current ∈ row.children, ∀ guard ∈ guards (child current), valid guard) :
    ∀ guard ∈ edgeGuards (SourceRankedRowsOrdinaryConstruction.layer rows child), valid guard := by
  induction rows with
  | nil => simp [SourceRankedRowsOrdinaryConstruction.layer, edgeGuards]
  | cons row rest ih =>
      intro guard member
      simp only [SourceRankedRowsOrdinaryConstruction.layer, List.map_cons, edgeGuards,
        List.mem_cons, List.mem_append] at member
      rcases member with rfl | first | later
      · exact checked row List.mem_cons_self
      · exact child_guards valid child row.children (children row List.mem_cons_self) guard first
      · exact ih (fun item listed => checked item (List.mem_cons_of_mem _ listed))
          (fun item listed => children item (List.mem_cons_of_mem _ listed)) guard later

/-- Every unfolded guard comes from a complete original row annotation. -/
theorem guards_expression (valid : Guard → Prop) (source : Q → List (Row Q Symbol Guard))
    (checked : ∀ current row, row ∈ source current → valid row.constraint) (fuel : Nat) (root : Q) :
    ∀ guard ∈ guards (SourceRankedRowsOrdinaryConstruction.expression source fuel root), valid guard := by
  induction fuel generalizing root with
  | zero => simp [SourceRankedRowsOrdinaryConstruction.expression, guards]
  | succ fuel ih =>
      change ∀ guard ∈ edgeGuards (SourceRankedRowsOrdinaryConstruction.layer (source root)
        (SourceRankedRowsOrdinaryConstruction.expression source fuel)), valid guard
      exact layer_guards valid (source root) _ (checked root) (fun _ _ child _ => ih child)

private theorem product_guards (valid : Guard → Prop) (original : Q → List (Row Q Symbol Guard))
    (checked : ∀ current row, row ∈ original current → valid row.constraint)
    (minimum : Q → Option Nat) (equalSizes : Guard → List Nat → Bool) (root : Q) (bound : Int) :
    ∀ current row, row ∈ SourceSizedPrefixProductRank.rows original minimum equalSizes root bound current → valid row.constraint := by
  have ofClass : ∀ current size row,
      row ∈ SourceSizedPrefixProductRank.rowOf original minimum equalSizes current size → valid row.constraint := by
    intro current size row member
    obtain ⟨originalRow, present, _allocation, _filter, _label, same, _rest⟩ :=
      SourceSizedPrefixProductRank.rowOf_origin original minimum equalSizes current size row member
    exact same.symm ▸ checked current originalRow present
  intro current row member
  cases current with
  | none =>
      simp only [SourceSizedPrefixProductRank.rows, List.mem_flatMap] at member
      obtain ⟨offset, _range, selected⟩ := member
      exact ofClass root (offset + 1) row selected
  | some pair =>
      rcases pair with ⟨state, size⟩
      exact ofClass state size row member
end Origins

open SourcePruningEnumerationNodes
open SourceCurrentAllocatedPartialInitialization (inventory caller globals)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
variable {Q Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Original row guards and cache validity derive the actual bounded-root startup. -/
theorem initial_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (original : Q → List (Row Q Symbol Guard)) (minimum : Q → Option Nat)
    (equalSizes : Guard → List Nat → Bool) (root : Q) (bound : Int)
    (normalized : ∀ current row, row ∈ original current → SourceEqualityGuardReadback.Cached row.constraint.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    let expression := SourceSizedPrefixProductOrdinary.expression original minimum equalSizes root bound
    let final := (SourceEqualityOriginalAllocationPreparation.prepare (guards expression) cache).2
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      InternedNestedFacts.Facts heap ∧ Available heap value ∧ value.free = [] ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ MergedOrdinaryHeight.height value ≤ bound.toNat + 1 ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ guards expression) heap ∧
      ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      let startup : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false, fun _ => none⟩
      SourcePruningEnumerationRecursive.Packet formulas solver (inventory expression value heap built)
        (caller width final heap) globals metadata startup ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩ (caller width final heap).checked ∧
      EnumerationValidity.Canonical startup.core ∧
      startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 := by
  let expression := SourceSizedPrefixProductOrdinary.expression original minimum equalSizes root bound
  have cached : ∀ guard ∈ guards expression, SourceEqualityGuardReadback.Cached guard.equalities := by
    change ∀ guard ∈ guards (SourceRankedRowsOrdinaryConstruction.expression
      (SourceSizedPrefixProductRank.rows original minimum equalSizes root bound) (bound.toNat + 2) none),
      SourceEqualityGuardReadback.Cached guard.equalities
    exact guards_expression _ _ (product_guards _ original normalized minimum equalSizes root bound) _ _
  obtain ⟨value, heap, built, facts, available, free, domain, height⟩ :=
    SourceSizedPrefixProductOrdinary.closed original minimum equalSizes root bound
  obtain ⟨other, after, observed, known, _annotated⟩ := SourceEqualityAnnotationConstruction.closed
    (fun guard => guard ∈ guards expression) expression
    (SourceEqualityConstraintOrigins.allowed _ expression (fun _ member => member))
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (built.symm.trans observed)
  obtain ⟨other, after, observed, _available, _free, handle, encoded, decoded,
    packet, canonical, stored, mass, _waiting, _flags⟩ :=
    SourcePruningEnumerationConstructedInitial.prepared_initial_packet (width := width)
      formulas solver cache valid expression cached metadata emptyPending
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (built.symm.trans observed)
  refine ⟨value, heap, built, facts, available, free, domain, height, known,
    handle, encoded, decoded, packet, ?_, canonical, stored, mass⟩
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩

end MicroCFTA.SourceSizedPrefixProductInitial
