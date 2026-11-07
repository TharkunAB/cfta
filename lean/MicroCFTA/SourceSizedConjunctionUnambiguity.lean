import MicroCFTA.SourceSizedScopedUnambiguity
import MicroCFTA.SourceSizedConjunctionPreparation

/-!
# The scoped source gate separates computed conjunction alternatives

The Boolean gate checks all erased rows of the query-root trimmed table.
Classification preserves those ordered row shapes. A conjunction row that
accepts a term selects one source row per owner that accepts the same term.
Disjoint source row occurrences therefore separate the computed alternatives.

Repeated rows remain in every list. The argument does not assume distinct
source rows or an already unambiguous output. It proves local alternative
disjointness with the output class guards retained. Uniqueness inside the
grouped child product and its counting interface remain separate.
-/
namespace MicroCFTA.SourceSizedConjunctionUnambiguity
open Language SourceSizedDecided SourceSizedFiniteKeys SourceSizedConjunctionWorklist
open SourceSizedConjunctionLanguage (graph)

variable {State Symbol Payload Formula : Type}

/-- Interpret the actual row shapes after source constraint erasure. -/
def erased (rows : State → List (Row State Symbol Payload)) : Automaton State Symbol :=
  automaton rows (fun _ _ => true)

/-- Successful complete classification retains every erased edge in its original order. -/
theorem classified_erased_eq [DecidableEq State]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    erased (lookup classified) = erased (lookup original) := by
  funext state
  change (lookup classified state).map (fun row => (⟨row.label, row.children, fun _ => true⟩ : Edge State Symbol)) =
    (lookup original state).map (fun row => (⟨row.label, row.children, fun _ => true⟩ : Edge State Symbol))
  have same := congrArg
    (List.map (fun shape : Symbol × List State =>
      (⟨shape.1, shape.2, fun _ => true⟩ : Edge State Symbol)))
    (SourceSizedConjunctionClassified.lookup_shapes original classified classification state)
  simpa only [List.map_map, Function.comp_def] using same

private theorem lookup_absent {Key : Type} [DecidableEq Key]
    (table : Table Key Symbol Payload) (key : Key) (absent : key ∉ table.map Prod.fst) :
    lookup table key = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  unfold lookup at member
  obtain ⟨entry, entryIn, selected⟩ := List.mem_flatMap.mp member
  by_cases same : entry.1 = key
  · exact absent (List.mem_map.mpr ⟨entry, entryIn, same⟩)
  · simp only [ite_eq_right same, List.not_mem_nil] at selected

private theorem ordered_disjoint_transfer {Source Target : Type}
    (source : Automaton Source Symbol) (target : Automaton Target Symbol) (encode : Source → Target)
    (readback : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (state : Source) (separate : RecursiveUnambiguous.DisjointRows source state) :
    RecursiveUnambiguous.DisjointRows target (encode state) := by
  have copied : SymbolicGraphView.RowsCorrespond source target encode := by
    intro current edge
    rw [readback]
    simp only [List.mem_map]
    constructor
    · rintro ⟨before, beforeIn, same⟩
      exact ⟨before, beforeIn, same.symm⟩
    · rintro ⟨before, beforeIn, same⟩
      exact ⟨before, beforeIn, same.symm⟩
  have transfer (edge : Edge Source Symbol) (term : Term Symbol)
      (accepted : AutomatonAmbiguity.EdgeLanguage (Accepts target)
        (SymbolicGraphView.renameEdge encode edge) term) :
      AutomatonAmbiguity.EdgeLanguage (Accepts source) edge term := by
    obtain ⟨terms, same, children, guard⟩ := accepted
    exact ⟨terms, same,
      ((SymbolicGraphView.all₂_map_iff (Accepts target) encode edge.children terms).mp children).imp
        (fun child value run => (SymbolicGraphView.rowsCorrespond_exact source target encode copied child value).mp run),
      guard⟩
  unfold RecursiveUnambiguous.DisjointRows
  rw [readback]
  apply List.pairwise_map.mpr
  apply separate.imp
  intro first second apart term left right
  exact apart term (transfer first term left) (transfer second term right)

/-- The actual finite scoped Boolean gate separates erased rows at every raw state. -/
theorem scoped_erased_disjoint [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (table : Table State Symbol Payload) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true) (state : State) :
    RecursiveUnambiguous.DisjointRows
      (erased (lookup (SourceSizedScopedTrimInventory.trimmedTable table root))) state := by
  let input := SourceSizedScopedUnambiguity.input table root validated
  let source := automaton input.rows (fun _ _ => true)
  let target := erased (lookup (SourceSizedScopedTrimInventory.trimmedTable table root))
  by_cases present : state ∈ SourceDenseRows.keys (SourceSizedScopedTrimInventory.trimmedTable table root)
  · let finiteState : SourceDenseRows.Member
        (SourceDenseRows.keys (SourceSizedScopedTrimInventory.trimmedTable table root)) := ⟨state, present⟩
    have separate := SourceSizedCurrentUnambiguity.gate_disjoint source input.states input.complete passed finiteState
    exact ordered_disjoint_transfer source target Subtype.val
      (SourceSizedScopedUnambiguity.input_readback table root validated) finiteState separate
  · have absent : state ∉ (SourceSizedScopedTrimInventory.trimmedTable table root).map Prod.fst := by
      intro member
      exact present ((SourceDenseRows.mem_keys _ state).mpr member)
    have empty := lookup_absent (SourceSizedScopedTrimInventory.trimmedTable table root) state absent
    simp only [RecursiveUnambiguous.DisjointRows, erased, automaton, empty, List.map_nil]
    exact .nil

/-- Actual classification preserves the complete scoped erased-row disjointness result. -/
theorem scoped_classified_disjoint [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable
      (SourceSizedScopedTrimInventory.trimmedTable table root) = some classified) (state : State) :
    RecursiveUnambiguous.DisjointRows (erased (lookup classified)) state := by
  rw [classified_erased_eq _ classified classification]
  exact scoped_erased_disjoint table root validated passed state

private theorem products_separate {Owner Item Value : Type}
    (choices : Owner → List Item) (predicate : Item → Value → Prop) (owners : List Owner)
    (separate : ∀ owner ∈ owners, (choices owner).Pairwise
      (fun first second => ∀ value, predicate first value → ¬predicate second value)) :
    (products choices owners).Pairwise (fun first second => ∀ value,
      (∀ item ∈ first, predicate item value) → ¬(∀ item ∈ second, predicate item value)) := by
  induction owners with
  | nil => simp [products]
  | cons owner owners ih =>
      have tail := ih (fun next present => separate next (List.mem_cons_of_mem _ present))
      change ((choices owner).flatMap fun item => (products choices owners).map (item :: ·)).Pairwise _
      apply List.pairwise_flatMap.mpr
      constructor
      · intro head _
        apply List.pairwise_map.mpr
        apply tail.imp
        intro first second apart value left right
        exact apart value
          (fun item present => left item (List.mem_cons_of_mem _ present))
          (fun item present => right item (List.mem_cons_of_mem _ present))
      · apply (separate owner (by simp)).imp_of_mem
        intro first second _ _ apart left leftIn right rightIn value acceptedLeft acceptedRight
        obtain ⟨leftTail, _, rfl⟩ := List.mem_map.mp leftIn
        obtain ⟨rightTail, _, rfl⟩ := List.mem_map.mp rightIn
        exact apart value (acceptedLeft first (by simp)) (acceptedRight second (by simp))

private theorem branches_separate {Item Output Value : Type}
    (heads : List Item) (tails : Item → List (List Item)) (build : Item → List Item → Output)
    (source : Item → Value → Prop) (target : Output → Value → Prop)
    (headSeparate : heads.Pairwise (fun first second => ∀ value, source first value → ¬source second value))
    (tailSeparate : ∀ head ∈ heads, (tails head).Pairwise (fun first second => ∀ value,
      (∀ item ∈ first, source item value) → ¬(∀ item ∈ second, source item value)))
    (transfer : ∀ head ∈ heads, ∀ tail ∈ tails head, ∀ value,
      target (build head tail) value → ∀ item ∈ head :: tail, source item value) :
    (heads.flatMap fun head => (tails head).map (build head)).Pairwise
      (fun first second => ∀ value, target first value → ¬target second value) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro head headIn
    apply List.pairwise_map.mpr
    apply (tailSeparate head headIn).imp_of_mem
    intro first second firstIn secondIn apart value left right
    exact apart value
      (fun item present => transfer head headIn first firstIn value left item (List.mem_cons_of_mem _ present))
      (fun item present => transfer head headIn second secondIn value right item (List.mem_cons_of_mem _ present))
  · apply headSeparate.imp_of_mem
    intro first second firstIn secondIn apart left leftIn right rightIn value acceptedLeft acceptedRight
    obtain ⟨leftTail, leftTailIn, rfl⟩ := List.mem_map.mp leftIn
    obtain ⟨rightTail, rightTailIn, rfl⟩ := List.mem_map.mp rightIn
    exact apart value
      (transfer first firstIn leftTail leftTailIn value acceptedLeft first (by simp))
      (transfer second secondIn rightTail rightTailIn value acceptedRight second (by simp))

/-- Guard erasure after class interpretation retains the exact original erased row shapes. -/
theorem graph_erased [DecidableEq Symbol] (rows : State → List (Row State Symbol (List (List Nat)))) :
    Productivity.eraseGuards (graph rows) = erased rows := by
  funext state
  change ((rows state).map (fun row => row.edge SourceSizedConjunctionSemantics.holds)).map
      (fun edge => {edge with guard := fun _ => true}) =
    (rows state).map (fun row => (⟨row.label, row.children, fun _ => true⟩ : Edge State Symbol))
  simp only [List.map_map, Function.comp_def, Row.edge]

/-- The actual scoped gate derives distinct erased size classes throughout its retained table. -/
theorem scoped_erased_unique [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (table : Table State Symbol Payload) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true) :
    SizedRank.Unambiguous (erased (lookup (SourceSizedScopedTrimInventory.trimmedTable table root))) := by
  intro state size
  exact RecursiveUnambiguous.enumerate_nodup _ (SourceSizedDispatcher.ordinary_plain _)
    (fun _ => True) (by intro _ _ _ _ _ _; trivial)
    (fun current _ => scoped_erased_disjoint table root validated passed current) size state trivial

/-- Classified trimmed rows retain distinct raw size classes with their class payloads unchanged. -/
theorem scoped_classified_unique [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable
      (SourceSizedScopedTrimInventory.trimmedTable table root) = some classified) :
    SizedRank.Unambiguous (graph (lookup classified)) := by
  have unique : SizedRank.Unambiguous (erased (lookup classified)) := by
    rw [classified_erased_eq _ classified classification]
    exact scoped_erased_unique table root validated passed
  intro state size
  have distinct := unique state size
  rw [← graph_erased (lookup classified), SourceSizedTrimRunClasses.enumerate_eraseGuards] at distinct
  exact distinct

private theorem all₂_imp_on_left {A B : Type} {relation result : A → B → Prop}
    {left : List A} {right : List B} (related : All₂ relation left right)
    (change : ∀ item ∈ left, ∀ value, relation item value → result item value) : All₂ result left right := by
  induction related with
  | nil => exact .nil
  | @cons item value rest values head tail ih =>
      exact .cons (change item (by simp) value head)
        (ih (fun other present chosen accepted => change other (List.mem_cons_of_mem _ present) chosen accepted))

/-- Every accepted computed intersection selects source rows that accept the same erased term. -/
theorem selected_erased [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State Symbol) (ready : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst)
    (first : Row State Symbol (List (List Nat))) (others : List (Row State Symbol (List (List Nat))))
    (selected : first :: others ∈ SourceSizedConjunctionTuples.tuples (lookup classified) key)
    (term : Term Symbol)
    (accepted : AutomatonAmbiguity.EdgeLanguage (Accepts (graph (lookup returned)))
      ((SourceSizedConjunctionRows.intersection first others).edge SourceSizedConjunctionSemantics.holds) term) :
    ∀ row ∈ first :: others,
      AutomatonAmbiguity.EdgeLanguage (Accepts (erased (lookup classified))) (row.edge (fun _ _ => true)) term := by
  obtain ⟨terms, rfl, children, guard⟩ := accepted
  have outputIn : SourceSizedConjunctionRows.intersection first others ∈ lookup returned key := by
    rw [SourceSizedConjunctionLanguage.prepare_lookup classified root returned ready key present]
    exact (SourceSizedConjunctionRows.mem_rows _ _ _).mpr ⟨first, others, selected, rfl⟩
  have valid := SourceSizedConjunctionClassified.lookup_bounded original classified classification
  have domains : All₂ (fun child value => ∀ state ∈ child, Accepts (graph (lookup classified)) state value)
      (SourceSizedConjunctionRows.intersection first others).children terms :=
    all₂_imp_on_left children (fun child childIn value run state stateIn =>
      (SourceSizedConjunctionLanguage.prepare_language classified valid root returned ready child
        (SourceSizedConjunctionLanguage.prepare_children classified root returned ready key _ outputIn child childIn)
        value).mp run state stateIn)
  have firstArity : first.children.length = terms.length :=
    (SourceSizedConjunctionRows.intersection_arity first others).symm.trans children.length_eq
  have arities : ∀ row ∈ first :: others, row.children.length = terms.length := by
    intro row rowIn
    exact (SourceSizedConjunctionTuples.common_shape (lookup classified) key _ selected row first rowIn (by simp)).2.trans
      firstArity
  have tupleValid : ∀ row ∈ first :: others, CompactGroups.ValidClasses row.children.length row.constraint := by
    intro row rowIn
    obtain ⟨owner, _, stored⟩ := SourceSizedConjunctionTuples.row_origin (lookup classified) key _ selected row rowIn
    exact valid owner row stored
  have every := (SourceSizedConjunctionSemantics.intersection_node_iff first others
    (Accepts (graph (lookup classified))) first.label terms arities tupleValid).mp ⟨domains, guard⟩
  intro row rowIn
  have rowChildren := (every row rowIn).1.imp (fun state value run =>
    graph_erased (lookup classified) ▸ Productivity.eraseGuards_accepts _ run)
  refine ⟨terms, ?_, rowChildren, rfl⟩
  have label := (SourceSizedConjunctionTuples.common_shape (lookup classified) key _ selected row first rowIn (by simp)).1
  simp only [Row.edge, SourceSizedConjunctionRows.intersection_label, label]

/-- Actual preparation separates its output alternatives from disjoint erased source alternatives. -/
theorem prepare_disjoint_of_erased [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (separate : ∀ state, RecursiveUnambiguous.DisjointRows (erased (lookup classified)) state)
    (root : State) (returned : Stored State Symbol) (ready : prepare classified root = .ready returned)
    (key : List State) : RecursiveUnambiguous.DisjointRows (graph (lookup returned)) key := by
  by_cases present : key ∈ returned.map Prod.fst
  · let sourcePredicate := fun row : Row State Symbol (List (List Nat)) =>
      AutomatonAmbiguity.EdgeLanguage (Accepts (erased (lookup classified))) (row.edge (fun _ _ => true))
    let targetPredicate := fun row : Row (List State) Symbol (List (List Nat)) =>
      AutomatonAmbiguity.EdgeLanguage (Accepts (graph (lookup returned)))
        (row.edge SourceSizedConjunctionSemantics.holds)
    have sourceSeparate (state : State) : (lookup classified state).Pairwise
        (fun first second => ∀ term, sourcePredicate first term → ¬sourcePredicate second term) :=
      List.pairwise_map.mp (separate state)
    change ((lookup returned key).map (Row.edge SourceSizedConjunctionSemantics.holds)).Pairwise _
    rw [SourceSizedConjunctionLanguage.prepare_lookup classified root returned ready key present]
    apply List.pairwise_map.mpr
    change (SourceSizedConjunctionRows.rows (lookup classified) key).Pairwise
      (fun first second => ∀ term, targetPredicate first term → ¬targetPredicate second term)
    cases key with
    | nil => exact .nil
    | cons owner owners =>
        apply branches_separate (lookup classified owner)
          (fun first => products (fun state => (lookup classified state).filter
            (SourceSizedConjunctionTuples.sameToken first)) owners)
          SourceSizedConjunctionRows.intersection sourcePredicate targetPredicate (sourceSeparate owner)
        · intro first _
          apply products_separate
          intro state _
          exact (sourceSeparate state).filter (SourceSizedConjunctionTuples.sameToken first)
        · intro first firstIn others othersIn term accepted
          apply selected_erased original classified classification root returned ready (owner :: owners) present
            first others ?_ term accepted
          exact List.mem_flatMap.mpr ⟨first, firstIn, List.mem_map.mpr ⟨others, othersIn, rfl⟩⟩
  · have empty := lookup_absent returned key present
    simp only [RecursiveUnambiguous.DisjointRows, graph, automaton, empty, List.map_nil]
    exact .nil

/-- The actual scoped Boolean gate and classification/exploration receipts separate computed rows. -/
theorem scoped_prepare_disjoint [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable
      (SourceSizedScopedTrimInventory.trimmedTable table root) = some classified)
    (returned : Stored State Symbol) (ready : prepare classified root = .ready returned)
    (key : List State) : RecursiveUnambiguous.DisjointRows (graph (lookup returned)) key :=
  prepare_disjoint_of_erased (SourceSizedScopedTrimInventory.trimmedTable table root) classified classification
    (scoped_classified_disjoint table root validated passed classified classification) root returned ready key

private theorem permutation_disjoint {Key : Type} (source target : Automaton Key Symbol)
    (permutation : ∀ key, (target key).Perm (source key))
    (separate : ∀ key, RecursiveUnambiguous.DisjointRows source key) (key : Key) :
    RecursiveUnambiguous.DisjointRows target key := by
  have language := SourceCyclicAutomaton.permutation_language source target permutation
  let apart := fun first second : Edge Key Symbol => ∀ term,
    AutomatonAmbiguity.EdgeLanguage (Accepts target) first term →
      ¬AutomatonAmbiguity.EdgeLanguage (Accepts target) second term
  have transfer (edge : Edge Key Symbol) (term : Term Symbol)
      (accepted : AutomatonAmbiguity.EdgeLanguage (Accepts target) edge term) :
      AutomatonAmbiguity.EdgeLanguage (Accepts source) edge term := by
    obtain ⟨terms, same, children, guard⟩ := accepted
    exact ⟨terms, same, children.imp (fun child value run => (language child value).mp run), guard⟩
  have before : (source key).Pairwise apart := (separate key).imp (by
    intro first second different term left right
    exact different term (transfer first term left) (transfer second term right))
  have symmetric : ∀ {first second}, apart first second → apart second first := by
    intro first second different term left right
    exact different term right left
  exact ((permutation key).pairwise_iff symmetric).mpr before

/-- Decorated sorting and symbol restoration preserve the source-derived alternative separation. -/
theorem sorted_scoped_disjoint [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable
      (SourceSizedScopedTrimInventory.trimmedTable table root) = some classified)
    (returned : Stored State Symbol) (ready : prepare classified root = .ready returned)
    (key : List State) :
    RecursiveUnambiguous.DisjointRows
      (graph (lookup (SourceSizedConjunctionSorted.sortedTable classified root returned ready))) key := by
  have readback : lookup (SourceSizedConjunctionSorted.sortedTable classified root returned ready) =
      SourceSizedConjunctionSorted.sortedRows classified root returned ready :=
    funext (SourceSizedConjunctionSorted.sortedTable_lookup classified root returned ready)
  rw [readback]
  apply permutation_disjoint (graph (lookup returned))
    (graph (SourceSizedConjunctionSorted.sortedRows classified root returned ready))
  · intro current
    exact (SourceSizedConjunctionSorted.sorted_permutation classified root returned ready current).map
      (Row.edge SourceSizedConjunctionSemantics.holds)
  · exact scoped_prepare_disjoint table root validated passed classified classification returned ready

/-- The actual complete preparation result has disjoint guarded alternatives at every key. -/
theorem preparation_disjoint [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output) (key : List State) :
    RecursiveUnambiguous.DisjointRows (graph (lookup output)) key := by
  obtain ⟨classified, classification, returned, ready, same⟩ :=
    SourceSizedConjunctionPreparation.success_origin (SourceSizedScopedTrimInventory.trimmedTable table root) root output success
  rw [same]
  exact sorted_scoped_disjoint table root validated passed classified classification returned ready key

end MicroCFTA.SourceSizedConjunctionUnambiguity
