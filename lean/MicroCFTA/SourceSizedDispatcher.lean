import MicroCFTA.SourceSizedDispatchGraph
import MicroCFTA.SourceSizedTrimGuards

/-!
# The public two-branch Sized dispatcher

Both branches return the same four query functions. The plain-constraint
scan derives the guard-erasure fact. The product-minimum scan derives run
uniqueness. A failed scan uses the reference residual-guard precheck.
The row argument is the canonical ordering of the original raw rows.
-/
namespace MicroCFTA.SourceSizedDispatcher
open Language RecursiveSize SizedRank SourceSizedDecided
open SourceSymbolicIndex SourceObservations SourceGuards

/-- The four source queries, including their signed sizes and ranks. -/
structure Api (Symbol : Type) where
  terms : Int → List (Term Symbol)
  count : Int → Nat
  unrank : Int → Int → Option (Term Symbol)
  rank : Term Symbol → Option Position

/-- Reference queries read one first-occurrence distinct class sequence. -/
def referenceApi [DecidableEq Symbol] (rows : Automaton State Symbol) (root : State) : Api Symbol where
  terms := SourceSizedQueries.termsSigned (fun size => SourceSizedReference.classes rows size root)
  count := SourceSizedQueries.countSigned (fun size => SourceSizedReference.classes rows size root)
  unrank := SourceSizedQueries.unrankSigned (fun size => SourceSizedReference.classes rows size root)
  rank := SourceSizedQueries.rank (fun size => SourceSizedReference.classes rows size root) nodeSize

/-- Optimized queries read the original count table and bottom-up inverse. -/
def optimizedApi [DecidableEq Symbol] (rows : Automaton State Symbol) (root : State) : Api Symbol where
  terms := fun size => SourceSizedDispatch.terms rows root size.toNat
  count := fun size => countAt rows size.toNat root
  unrank := SourceSizedDispatch.select rows root
  rank := fun term => TablePosition.positionsOf rows term root

/-- Empty size zero lets signed reference queries use natural-size projection. -/
theorem reference_terms_toNat [DecidableEq Symbol]
    (rows : Automaton State Symbol) (root : State) (size : Int) :
    SourceSizedQueries.termsSigned (fun size => SourceSizedReference.classes rows size root) size =
      SourceSizedReference.classes rows size.toNat root := by
  unfold SourceSizedQueries.termsSigned
  split
  · rename_i nonpositive
    have zero : size.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [zero, SourceSizedReference.classes_zero]
  · rfl

/-- A passing direct graph gate makes the complete optimized record equal to the reference. -/
theorem optimizedApi_eq_reference [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : SourceSizedDispatchGraph.unambiguousRows rows states complete = true) (root : State) :
    optimizedApi rows root = referenceApi rows root := by
  obtain ⟨listed, counted, selected, ranked⟩ :=
    SourceSizedDispatchGraph.optimized_reference rows plain states complete passed root
  change Api.mk _ _ _ _ = Api.mk _ _ _ _
  congr 1
  · funext size
    rw [listed, reference_terms_toNat]
  · funext size
    dsimp only [optimizedApi, referenceApi, SourceSizedQueries.countSigned]
    rw [counted, reference_terms_toNat]
  · funext size rank
    dsimp only [optimizedApi, referenceApi, SourceSizedQueries.unrankSigned]
    rw [selected, reference_terms_toNat]
    by_cases negative : rank < 0
    · simp [negative, show ¬0 ≤ rank by omega]
    · simp [negative, show 0 ≤ rank by omega]
  · funext term
    exact ranked term

/-- The source identity constraint has no equality class and a Top guard. -/
def noConstraint : Constraint Formula := ⟨some [], .top⟩

/-- The source plain scan compares every original row annotation with noConstraint. -/
noncomputable def plainCheck
    (rows : State → List (Row State (Label Formula) (Constraint Formula))) (states : List State) : Bool := by
  classical
  exact states.all fun state => (rows state).all fun row => decide (row.constraint = noConstraint)

/-- Equality filtering retains the source Bottom shortcut and normalized equality classes. -/
noncomputable def equalityRows [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula))) : Automaton State (Label Formula) :=
  automaton rows SourceSizedEqualities.constraintHolds

/-- Ordinary count-table rows erase a previously checked noConstraint annotation. -/
def ordinaryRows (rows : State → List (Row State Symbol Annotation)) : Automaton State Symbol :=
  automaton rows (fun _ _ => true)

/-- A successful finite plain scan identifies every represented row constraint. -/
theorem checked_constraint
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states)
    (checked : plainCheck rows states = true) (state : State)
    (row : Row State (Label Formula) (Constraint Formula)) (member : row ∈ rows state) :
    row.constraint = noConstraint := by
  classical
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked state (complete state)) row member)

/-- Checked noConstraint rows keep exactly the equality-filtered source sequence. -/
theorem checked_rows [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states)
    (checked : plainCheck rows states = true) : equalityRows rows = ordinaryRows rows := by
  funext state
  apply List.map_congr_left
  intro row member
  unfold Row.edge
  rw [checked_constraint rows states complete checked state row member]
  rfl

/-- Erased noConstraint annotations are plain for every complete candidate. -/
theorem ordinary_plain (rows : State → List (Row State Symbol Annotation)) :
    Decoder.Plain (ordinaryRows rows) := by
  intro state edge member term
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Only the trimmed rows participate in the reference residual-guard scan. -/
noncomputable def residualCheck [DecidableEq State]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (root : State) : Bool :=
  states.all fun state => (SourceSizedTrimGuards.trimmedRows rows states root state).all
    fun row => (SourceCompactGuards.positive row.constraint.guard).isSome

/-- The source reference reports a residual guard before returning its class queries. -/
noncomputable def reference [DecidableEq State] [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (root : State) : Except Unit (Api (Label Formula)) :=
  if residualCheck rows states root then .ok (referenceApi (equalityRows rows) root) else .error ()

/-- The source dispatcher uses the direct count table exactly when both scans pass. -/
noncomputable def sized [DecidableEq State] [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State) : Except Unit (Api (Label Formula)) :=
  if plainCheck rows states &&
      SourceSizedDispatchGraph.unambiguousRows (ordinaryRows rows) states complete then
    .ok (optimizedApi (ordinaryRows rows) root)
  else reference rows states root

/-- Structural trimming only removes original rows. -/
theorem trimmed_subset [DecidableEq State]
    (rows : State → List (Row State Symbol Annotation)) (states : List State) (root state : State) :
    SourceSizedTrimGuards.trimmedRows rows states root state ⊆ rows state := by
  intro row member
  unfold SourceSizedTrimGuards.trimmedRows at member
  split at member
  · exact (List.mem_filter.mp member).1
  · cases member

/-- A passing plain scan also passes the reference residual-guard precheck. -/
theorem plain_residual [DecidableEq State]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (checked : plainCheck rows states = true) : residualCheck rows states root = true := by
  apply List.all_eq_true.mpr
  intro state _
  apply List.all_eq_true.mpr
  intro row member
  rw [checked_constraint rows states complete checked state row (trimmed_subset rows states root state member)]
  rfl

/-- Both source branches return exactly the same query record and the same residual error. -/
theorem sized_eq_reference [DecidableEq State] [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State) :
    sized rows states complete root = reference rows states root := by
  unfold sized
  split
  · rename_i passed
    have both : plainCheck rows states = true ∧
        SourceSizedDispatchGraph.unambiguousRows (ordinaryRows rows) states complete = true := by
      simpa only [Bool.and_eq_true] using passed
    obtain ⟨plain, unique⟩ := both
    rw [optimizedApi_eq_reference _ (ordinary_plain rows) states complete unique,
      reference, plain_residual rows states complete root plain]
    simp only [↓reduceIte, checked_rows rows states complete plain]
  · rfl

/-- Every successful dispatch exposes the exact reference class queries. -/
theorem sized_success [DecidableEq State] [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (api : Api (Label Formula)) (success : sized rows states complete root = .ok api) :
    residualCheck rows states root = true ∧ api = referenceApi (equalityRows rows) root := by
  rw [sized_eq_reference, reference] at success
  split at success
  · rename_i passed
    exact ⟨passed, (Except.ok.inj success).symm⟩
  · cases success

/-- Successful original-row dispatch accepts exactly the full guarded finite terms at each size. -/
theorem sized_terms_exact [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (active : ∀ state row, row ∈ SourceSizedTrimGuards.trimmedRows rows states root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (api : Api (Label Formula)) (success : sized rows states complete root = .ok api)
    (size : Nat) (term : Term (Label Formula)) :
    term ∈ api.terms (Int.ofNat size) ↔
      Accepts (automaton rows (acceptsConstraint formulas solver)) root term ∧ nodeSize term = size := by
  obtain ⟨checked, rfl⟩ := sized_success rows states complete root api success
  have positive : ∀ state row, row ∈ SourceSizedTrimGuards.trimmedRows rows states root state →
      (SourceCompactGuards.positive row.constraint.guard).isSome = true := by
    intro state row member
    exact List.all_eq_true.mp (List.all_eq_true.mp checked state (complete state)) row member
  change term ∈ SourceSizedQueries.termsSigned
    (fun size => SourceSizedReference.classes (equalityRows rows) size root) (Int.ofNat size) ↔ _
  rw [reference_terms_toNat]
  exact SourceSizedTrimGuards.reference_precheck_exact formulas solver rows states complete root
    active positive size term

/-- Both signed rank inverse laws hold for every successful source dispatcher result. -/
theorem sized_signed_inverses [DecidableEq State] [DecidableEq Formula]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (api : Api (Label Formula)) (success : sized rows states complete root = .ok api)
    (size rank : Int) (term : Term (Label Formula)) :
    (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) = some (size, rank) ↔
      api.unrank size rank = some term := by
  obtain ⟨_, rfl⟩ := sized_success rows states complete root api success
  let classes := fun size => SourceSizedReference.classes (equalityRows rows) size root
  have sized : SourceSizedQueries.Sized classes nodeSize := by
    intro size term member
    exact ((SourceSizedReference.mem_classes_iff _ size root term).mp member).2
  have unique : ∀ size, (classes size).Nodup := fun size => SourceSizedReference.classes_nodup _ size root
  change SourceSizedQueries.rankSigned classes nodeSize term = some (size, rank) ↔
    SourceSizedQueries.unrankSigned classes size rank = some term
  constructor
  · exact SourceSizedQueries.unrankSigned_rankSigned classes (SourceSizedReference.classes_zero _ root)
      nodeSize term size rank
  · exact SourceSizedQueries.rankSigned_unrankSigned classes nodeSize sized unique term size rank

end MicroCFTA.SourceSizedDispatcher
