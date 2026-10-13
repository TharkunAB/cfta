import MicroCFTA.SourceSizedDispatch
import MicroCFTA.SourceSizedQueries
import MicroCFTA.SourceSizedRows

/-!
# Direct graph dispatch for Sized

The optimized branch reads the same sorted original rows as the reference.
The finite synchronous product supplies the overlap test. A successful test
derives unique runs, so the count table and the reference have the same
sequence. No interned constructor or representation adapter is used.
-/
namespace MicroCFTA.SourceSizedDispatchGraph
open Language RecursiveSize SizedRank SourceSizedDispatch

/-- The finite synchronous product contains every pair of source states. -/
def pairs (states : List State) : List (State × State) :=
  states.flatMap fun left => states.map fun right => (left, right)

/-- The validated source domain gives a complete finite product domain. -/
theorem pairs_complete (states : List State) (complete : ∀ state, state ∈ states)
    (pair : State × State) : pair ∈ pairs states := by
  exact List.mem_flatMap.mpr ⟨pair.1, complete _, List.mem_map.mpr ⟨pair.2, complete _, rfl⟩⟩

/-- A pair has common terms when its product minimum-size entry exists. -/
def overlap [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) (complete : ∀ state, state ∈ states)
    (left right : State) : Bool :=
  (MinimumSize.minimumSizes (Language.intersect rows rows) (pairs states)
    (pairs_complete states complete) (left, right)).isSome

/-- The source overlap scan checks all different alternatives in each row. -/
def unambiguousRows [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) (complete : ∀ state, state ∈ states) : Bool :=
  !(states.any fun state => AutomatonAmbiguity.ambiguous (overlap rows states complete) (rows state))

/-- Every common accepted term produces the product minimum used by the source gate. -/
theorem overlap_covers [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) (complete : ∀ state, state ∈ states)
    (left right : State) (term : Term Symbol)
    (first : Accepts rows left term) (second : Accepts rows right term) :
    overlap rows states complete left right = true := by
  obtain ⟨size, found, _⟩ := MinimumSize.minimumSizes_complete
    (Language.intersect rows rows) (pairs states) (pairs_complete states complete)
    (intersect_complete rows rows first right second)
  simp [overlap, found]

/-- Successful overlap tests also have finite witnesses on plain rows. -/
theorem overlap_witness [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (left right : State) (found : overlap rows states complete left right = true) :
    ∃ term, Accepts rows left term ∧ Accepts rows right term := by
  obtain ⟨size, minimum⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨term, accepted, _⟩ := MinimumSize.minimumSizes_sound
    (Language.intersect rows rows) (AutomatonAmbiguity.intersect_plain rows plain)
    (pairs states) (pairs_complete states complete) (left, right) size minimum
  exact ⟨term, (accepts_intersect_iff rows rows left right term).mp accepted⟩

/-- The computed finite row scan derives disjoint alternative languages. -/
theorem gate_disjoint [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true) (state : State) :
    RecursiveUnambiguous.DisjointRows rows state := by
  have scan : (states.any fun state =>
      AutomatonAmbiguity.ambiguous (overlap rows states complete) (rows state)) = false := by
    simpa [unambiguousRows] using passed
  exact AutomatonAmbiguity.compact_disjoint (Accepts rows) (overlap rows states complete)
    (overlap_covers rows states complete) (rows state)
    (by simpa using List.any_eq_false.mp scan state (complete state))

/-- The direct graph gate derives distinct terms in every class. -/
theorem gate_unique [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true) : Unambiguous rows := by
  intro state size
  exact RecursiveUnambiguous.enumerate_nodup rows plain (fun _ => True) (by simp)
    (fun state _ => gate_disjoint rows states complete passed state) size state trivial

/-- The source product-minimum loop completes on its finite state-pair table. -/
theorem gate_minimum_terminates [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (states : List State) (complete : ∀ state, state ∈ states) :
    ∃ fuel, MinimumSize.sweep (Language.intersect rows rows) (pairs states)
        (MinimumSize.sweeps (Language.intersect rows rows) (pairs states) fuel (fun _ => none)) =
      MinimumSize.sweeps (Language.intersect rows rows) (pairs states) fuel (fun _ => none) :=
  MinimumSize.minimumSizes_terminates _ _ (pairs_complete states complete)

/-- A successful direct graph gate connects all four optimized queries to the reference sequence. -/
theorem optimized_reference [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true) (root : State) :
    (∀ size, terms rows root size = SourceSizedReference.classes rows size root) ∧
    (∀ size, countAt rows size root = (SourceSizedReference.classes rows size root).length) ∧
    (∀ size rank, select rows root size rank =
      if 0 ≤ rank then (SourceSizedReference.classes rows size.toNat root)[rank.toNat]? else none) ∧
    (∀ term, TablePosition.positionsOf rows term root =
      (rankOf (SourceSizedReference.classes rows (nodeSize term) root) term).map
        (fun rank => (⟨nodeSize term, rank⟩ : Position))) := by
  have unique := gate_unique rows plain states complete passed
  have reference := SourceSizedReference.classes_eq_enumerate rows plain unique
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro size
    rw [terms_exact, reference]
  · intro size
    rw [countAt_correct, reference]
  · intro size rank
    rw [select_exact, reference]
  · intro term
    rw [TablePosition.positionsOf_eq_termPosition rows plain unique, termPosition, reference]
    rfl

/-- Successful direct graph selection and bottom-up ranking are mutual inverses. -/
theorem optimized_inverses [DecidableEq State] [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true)
    (root : State) (position : Position) (term : Term Symbol) :
    TablePosition.positionsOf rows term root = some position ↔
      select rows root (Int.ofNat position.size) (Int.ofNat position.rank) = some term := by
  rw [RecursiveUnambiguous.positionsOf_inverse rows plain root
    (gate_unique rows plain states complete passed root)]
  rw [select_exact]
  simp [replayPosition, decode_compileAt]

end MicroCFTA.SourceSizedDispatchGraph
