import MicroCFTA.SourceSizedGroupedClasses
import MicroCFTA.SourceSizedMinimumAttainment
import MicroCFTA.SourceSizedPrefixComputedMinimum

/-!
# Computed structural minima for actual grouped classes

Valid shared rows can replace each child state by one least guarded term.
This replacement satisfies every equality group and cannot increase size.
Guard erasure therefore preserves productivity and the least node count.

The final theorems use the actual minimum iteration and the finite input
derived from successful conjunction preparation. They need no caller-supplied
finite carrier, productivity result, or minimum certificate. Native Map keys
and lazy-index execution remain separate. Source request sizes are unbounded.
-/

namespace MicroCFTA.SourceSizedGroupedMinimum

open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys
open SourceSizedConjunctionLanguage (graph)
open SourceSizedMinimumConvergence (minimumSizes)
open SourceSizedPrefixComputedMinimum (minimumNat minimumNat_embedded)

private theorem least_term (domain : Term Symbol → Prop) (inhabited : ∃ term, domain term) :
    ∃ chosen, domain chosen ∧ ∀ other, domain other → nodeSize chosen ≤ nodeSize other := by
  classical
  have bounded : ∀ size, ∀ term, domain term → nodeSize term = size →
      ∃ chosen, domain chosen ∧ ∀ other, domain other → nodeSize chosen ≤ nodeSize other := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro term accepted sized
        by_cases smaller : ∃ other, domain other ∧ nodeSize other < size
        · obtain ⟨other, acceptedOther, below⟩ := smaller
          exact ih (nodeSize other) below other acceptedOther rfl
        · refine ⟨term, accepted, ?_⟩
          intro other acceptedOther
          have noSmaller : ¬ nodeSize other < size :=
            fun below => smaller ⟨other, acceptedOther, below⟩
          omega
  obtain ⟨term, accepted⟩ := inhabited
  exact bounded (nodeSize term) term accepted rfl

private theorem related_member_left {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : All₂ relation left right)
    (owner : A) (present : owner ∈ left) : ∃ value ∈ right, relation owner value := by
  induction related with
  | nil => cases present
  | @cons first value rest tail head paired ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨value, by simp, head⟩
      · obtain ⟨chosen, chosenIn, related⟩ := ih later
        exact ⟨chosen, List.mem_cons_of_mem value chosenIn, related⟩

private theorem all₂_map (states : List State) (choose : State → Term Symbol)
    (domain : State → Term Symbol → Prop) (each : ∀ state ∈ states, domain state (choose state)) :
    All₂ domain states (states.map choose) := by
  induction states with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (each first (by simp))
        (ih (fun state present => each state (List.mem_cons_of_mem first present)))

private theorem forest_map_le (choose : State → Term Symbol)
    {states : List State} {terms : List (Term Symbol)}
    (related : All₂ (fun state term => nodeSize (choose state) ≤ nodeSize term) states terms) :
    forestSize (states.map choose) ≤ forestSize terms := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      change nodeSize (choose _) + forestSize _ ≤ nodeSize _ + forestSize _
      omega

/-- Removing direct-child equality guards retains every already guarded run. -/
theorem guarded_to_erased [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (state : State) (term : Term Symbol) (accepted : Accepts (graph rows) state term) :
    Accepts (automaton rows (fun _ _ => true)) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Accepts (automaton rows (fun _ _ => true))) states terms) with
  | @node state edge terms stored _children _guard ih =>
      obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp stored
      exact .node (row.edge (fun _ _ => true)) terms
        (List.mem_map.mpr ⟨row, rowIn, rfl⟩) ih rfl
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- One least guarded term per shared child state satisfies every group and
has size at most the original guard-erased run. -/
theorem erased_to_guarded [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧
        SourceSizedConjunctionSharing.Shared row)
    (state : State) (term : Term Symbol)
    (accepted : Accepts (automaton rows (fun _ _ => true)) state term) :
    ∃ guarded, Accepts (graph rows) state guarded ∧ nodeSize guarded ≤ nodeSize term := by
  classical
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (fun state term =>
      ∃ guarded, Accepts (graph rows) state guarded ∧ nodeSize guarded ≤ nodeSize term) states terms) with
  | @node state edge terms stored _children _guard ih =>
      obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp stored
      let preferred := fun child =>
        if inhabited : ∃ value, Accepts (graph rows) child value then
          Classical.choose (least_term (Accepts (graph rows) child) inhabited)
        else .node row.label []
      have preferred_spec (child : State) (inhabited : ∃ value, Accepts (graph rows) child value) :
          Accepts (graph rows) child (preferred child) ∧
            ∀ other, Accepts (graph rows) child other → nodeSize (preferred child) ≤ nodeSize other := by
        simpa only [preferred, dite_eq_left inhabited] using
          Classical.choose_spec (least_term (Accepts (graph rows) child) inhabited)
      have replacements : All₂ (fun child original =>
          Accepts (graph rows) child (preferred child) ∧ nodeSize (preferred child) ≤ nodeSize original)
          row.children terms := by
        apply ih.imp
        intro child original witness
        obtain ⟨guarded, acceptedGuarded, bounded⟩ := witness
        have minimal := preferred_spec child ⟨guarded, acceptedGuarded⟩
        exact ⟨minimal.1, Nat.le_trans (minimal.2 guarded acceptedGuarded) bounded⟩
      have childrenAccepted : All₂ (Accepts (graph rows)) row.children (row.children.map preferred) := by
        apply all₂_map
        intro child childIn
        obtain ⟨_, _, evidence⟩ := related_member_left replacements child childIn
        exact evidence.1
      have childSize := forest_map_le preferred (replacements.imp (fun _ _ evidence => evidence.2))
      have rowFacts := facts state row rowIn
      have groupsEqual : CompactGroups.GroupsEqual
          (CompactEdgeRanks.childValue (.node row.label []) (row.children.map preferred))
          (CompactGroups.childGroups row.children.length row.constraint) := by
        intro group groupIn left leftIn right rightIn
        have same := rowFacts.2 group groupIn left leftIn right rightIn
        simpa only [CompactEdgeRanks.childValue, List.getElem?_map] using
          congrArg (fun read : Option State => (read.map preferred).getD (.node row.label [])) same
      have equalities := (CompactGroups.childGroups_exact _ row.children.length row.constraint rowFacts.1).mp groupsEqual
      have guard := (SourceSizedConjunctionSemantics.holds_node row.label (row.children.map preferred)
        row.constraint (by simpa only [List.length_map] using rowFacts.1)).mpr equalities
      refine ⟨.node row.label (row.children.map preferred),
        .node (row.edge SourceSizedConjunctionSemantics.holds) _
          (List.mem_map.mpr ⟨row, rowIn, rfl⟩) childrenAccepted guard, ?_⟩
      simp only [nodeSize]
      change forestSize (row.children.map preferred) + 1 ≤ forestSize terms + 1
      omega
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

section Prepared

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Actual preparation supplies the finite input consumed by the minimum pass. -/
def preparedInput (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output) :
    SourceSizedPreprocessing.Input (SourceDenseRows.Member (SourceDenseRows.keys output)) Symbol (List (List Nat)) :=
  SourceSizedStructuralKeys.input output [root]
    (SourceSizedConjunctionPreparation.validation original root output success)

private theorem prepared_readback
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (holds : List (List Nat) → Term Symbol → Bool)
    (key : SourceDenseRows.Member (SourceDenseRows.keys output)) (term : Term Symbol) :
    Accepts (automaton (preparedInput original root output success).rows holds) key term ↔
      Accepts (automaton (lookup output) holds) key.val term :=
  SourceSizedFiniteKeys.accepts_exact output
    (SourceSizedStructuralKeys.validated_closed output [root]
      (SourceSizedConjunctionPreparation.validation original root output success)) holds key term

/-- The actual computed minimum is attained in the grouped worker and bounds
every grouped member at that declared key. -/
theorem prepared_minimumNat_is_least
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : SourceDenseRows.Member (SourceDenseRows.keys output)) (size : Nat)
    (found : minimumNat (preparedInput original root output success) key = some size) :
    (∃ term, term ∈ SourceSizedGroupedClasses.run (lookup output) size key.val) ∧
      ∀ requested term, term ∈ SourceSizedGroupedClasses.run (lookup output) requested key.val → size ≤ requested := by
  let input := preparedInput original root output success
  have foundInput : minimumNat input key = some size := found
  have signed : minimumSizes input key = some (size : Int) := by
    have embedded := congrFun (minimumNat_embedded input) key
    rw [foundInput] at embedded
    exact embedded.symm
  have least := SourceSizedMinimumAttainment.minimum_is_least input key (size : Int) signed
  obtain ⟨originalTerm, accepted, exactSize⟩ := least.1
  have originalAccepted := (prepared_readback original root output success (fun _ _ => true) key originalTerm).mp accepted
  obtain ⟨guarded, guardedAccepted, notLarger⟩ := erased_to_guarded (lookup output)
    (SourceSizedConjunctionSharing.preparation_facts original root output success) key.val originalTerm originalAccepted
  have guardedFinite := (prepared_readback original root output success
    SourceSizedConjunctionSemantics.holds key guarded).mpr guardedAccepted
  have lower := least.2 guarded (guarded_to_erased input.rows key guarded guardedFinite)
  have exactGuarded : nodeSize guarded = size := by omega
  refine ⟨⟨guarded, (SourceSizedGroupedClasses.prepared_run_iff original root output success
    size key.val guarded).mpr ⟨guardedAccepted, exactGuarded⟩⟩, ?_⟩
  intro requested term member
  have accepted := ((SourceSizedGroupedClasses.prepared_run_iff original root output success
    requested key.val term).mp member)
  have finite := (prepared_readback original root output success
    SourceSizedConjunctionSemantics.holds key term).mpr accepted.1
  have bounded := least.2 term (guarded_to_erased input.rows key term finite)
  omega

/-- Absence from the actual minimum table is exactly absence of all grouped members. -/
theorem prepared_minimumNat_none_iff
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : SourceDenseRows.Member (SourceDenseRows.keys output)) :
    minimumNat (preparedInput original root output success) key = none ↔
      ∀ size, SourceSizedGroupedClasses.run (lookup output) size key.val = [] := by
  let input := preparedInput original root output success
  constructor
  · intro absent size
    change minimumNat input key = none at absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro term member
    have accepted := ((SourceSizedGroupedClasses.prepared_run_iff original root output success
      size key.val term).mp member).1
    have finite := (prepared_readback original root output success
      SourceSizedConjunctionSemantics.holds key term).mpr accepted
    obtain ⟨value, found, _⟩ := SourceSizedMinimumStructuralBound.erased_lower_bound input key term
      (guarded_to_erased input.rows key term finite)
    simp only [minimumNat, found, Option.map_some, reduceCtorEq] at absent
  · intro empty
    change minimumNat input key = none
    cases found : minimumNat input key with
    | none => rfl
    | some size =>
        obtain ⟨term, member⟩ := (prepared_minimumNat_is_least original root output success key size found).1
        rw [empty size] at member
        cases member

end Prepared

end MicroCFTA.SourceSizedGroupedMinimum
