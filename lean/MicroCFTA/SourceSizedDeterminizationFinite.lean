import MicroCFTA.SourceSizedStructuralKeys
import MicroCFTA.SourceSizedDeterminizationQueries

/-!
# Finite canonical input from subset discovery

Successful discovery supplies every emitted child key. The original
states and discovered subsets supply the output table's finite keys.
Current structural validation succeeds without a uniform symbol arity.
The derived finite input then computes the dense canonical row sort.
No caller supplies an output carrier, child closure, or row permutation.

These results concern the finite-list source model. Ordered Haskell map
and set readback and current public Sized routing remain separate.
The discovery bound counts checking rounds. It does not bound total work.
-/
namespace MicroCFTA.SourceSizedDeterminizationFinite
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows Std
open SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
variable [Ord (Sum State (List State))]

/-- Output keys contain each original root and each discovered subset. -/
def carrier (states : List State) (known : List (List State)) : List (Sum State (List State)) :=
  CanonicalClasses.sortedSet (states.map Sum.inl ++ known.map Sum.inr)

/-- Each original state is a declared Left key. -/
theorem left_mem (states : List State) (known : List (List State)) (state : State)
    (present : state ∈ states) : Sum.inl state ∈ carrier states known := by
  simp only [carrier, CanonicalClasses.mem_sortedSet, List.mem_append, List.mem_map]
  exact .inl ⟨state, present, rfl⟩

/-- Each discovered subset is a declared Right key. -/
theorem right_mem (states : List State) (known : List (List State)) (key : List State)
    (present : key ∈ known) : Sum.inr key ∈ carrier states known := by
  simp only [carrier, CanonicalClasses.mem_sortedSet, List.mem_append, List.mem_map]
  exact .inr ⟨key, present, rfl⟩

/-- Output key normalization removes duplicates without an extra premise. -/
theorem carrier_distinct (states : List State) (known : List (List State)) :
    (carrier states known).Nodup := CanonicalClasses.sortedSet_nodup _

/-- Every nonempty output row has a declared owner. -/
theorem rows_supported (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) (state : Sum State (List State))
    (edge : Edge (Sum State (List State)) Symbol)
    (present : edge ∈ SourceSizedDeterminizationRows.rows states source choices state) :
    state ∈ carrier states known := by
  cases state with
  | inl state =>
      obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp present
      have owner := of_decide_eq_true (List.mem_filter.mp selected).2
      exact left_mem states known state (List.mem_filter.mp owner).1
  | inr key =>
      obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp present
      have sourceChoice := (List.mem_filter.mp selected).1
      have targetEq := of_decide_eq_true (List.mem_filter.mp selected).2
      have targetKnown := closed.targets choice sourceChoice
      apply right_mem states known key
      simpa [targetEq] using targetKnown

/-- Closed discovery declares every positional child of every output row. -/
theorem children_supported (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) (state : Sum State (List State))
    (edge : Edge (Sum State (List State)) Symbol)
    (present : edge ∈ SourceSizedDeterminizationRows.rows states source choices state)
    (child : Sum State (List State)) (childIn : child ∈ edge.children) :
    child ∈ carrier states known := by
  cases state <;>
    (obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp present
     obtain ⟨key, keyIn, rfl⟩ := List.mem_map.mp childIn
     exact right_mem states known key
       (closed.children choice (List.mem_filter.mp selected).1 key keyIn))

/-- Store an emitted plain edge as a source row with a trivial constraint. -/
def packed (edge : Edge (Sum State (List State)) Symbol) :
    Row (Sum State (List State)) Symbol Unit :=
  ⟨edge.label, edge.children, ()⟩

/-- Packing retains the complete ordered alternative list. -/
def packedRows (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) :
    Sum State (List State) → List (Row (Sum State (List State)) Symbol Unit) :=
  fun state => (SourceSizedDeterminizationRows.rows states source choices state).map packed

omit [Ord (Sum State (List State))] in
/-- Every emitted edge already has the packed row's true guard. -/
theorem packed_readback (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) :
    automaton (packedRows states source choices) (fun _ _ => true) =
      SourceSizedDeterminizationRows.rows states source choices := by
  funext state
  cases state <;>
    simp only [automaton, packedRows, SourceSizedDeterminizationRows.rows,
      List.map_map, Function.comp_def, packed, SourceSizedDeterminizationRows.wrap, Row.edge] <;> rfl

/-- Construct the full explicit output table from its derived keys. -/
def table (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol)) :
    Table (Sum State (List State)) Symbol Unit :=
  (carrier states known).map fun state => (state, packedRows states source choices state)

/-- Explicit table construction retains exactly the derived key list. -/
theorem table_keys (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol)) :
    (table states source known choices).map Prod.fst = carrier states known := by
  simp [table, List.map_map, Function.comp_def]

private theorem lookup_map {Key Value : Type} [DecidableEq Key]
    (keys : List Key) (distinct : keys.Nodup) (rows : Key → List Value) (state : Key) :
    (keys.map (fun key => (key, rows key))).flatMap (fun entry =>
      if entry.1 = state then entry.2 else []) = if state ∈ keys then rows state else [] := by
  induction keys with
  | nil => simp
  | cons key rest ih =>
      have fresh := List.nodup_cons.mp distinct
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih fresh.2]
      by_cases same : key = state
      · subst state
        simp [fresh.1]
      · simp [same, Ne.symm same]

/-- Full table lookup equals the emitted row function, including outside keys. -/
theorem lookup_table (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) (state : Sum State (List State)) :
    lookup (table states source known choices) state = packedRows states source choices state := by
  unfold lookup table
  rw [lookup_map _ (carrier_distinct states known)]
  by_cases present : state ∈ carrier states known
  · simp [present]
  · have empty : packedRows states source choices state = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row rowIn
      obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp rowIn
      exact present (rows_supported states source known choices closed state edge edgeIn)
    simp [present, empty]

/-- Interpreted explicit rows equal the emitted graph at every state. -/
theorem interpreted_rows (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) :
    FTAValidation.rowFor (interpreted (table states source known choices) (fun _ _ => true)) =
      SourceSizedDeterminizationRows.rows states source choices := by
  funext state
  rw [interpreted_lookup, lookup_table states source known choices closed]
  exact congrFun (packed_readback states source choices) state

/-- Discovery derives raw child closure of the explicit output table. -/
theorem table_closed (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) :
    SourceSizedFiniteKeys.Closed (table states source known choices) := by
  intro state row rowIn child childIn
  rw [lookup_table states source known choices closed] at rowIn
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp rowIn
  apply (mem_keys _ child).mpr
  rw [table_keys]
  exact children_supported states source known choices closed state edge edgeIn child childIn

/-- Current validation succeeds from discovery and the original root membership. -/
theorem validation_succeeds (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : SourceSizedDeterminizationClosure.Closed states source known choices)
    (root : State) (present : root ∈ states) :
    SourceFTAValidation.validateRows (.inl root)
        (interpreted (table states source known choices) (fun _ _ => true)) =
      .ok (interpreted (table states source known choices) (fun _ _ => true)) := by
  apply SourceSizedStructuralKeys.validation_of_closed
  · apply (mem_keys (table states source known choices) (Sum.inl root)).mpr
    rw [table_keys]
    exact left_mem states known root present
  · exact table_closed states source known choices closed

/-- The source builder's normalization and validation also succeed. -/
theorem construction_succeeds (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : SourceSizedDeterminizationClosure.Closed states source known choices)
    (root : State) (present : root ∈ states) :
    SourceFTAValidation.mkFTA (.inl root)
        (interpreted (table states source known choices) (fun _ _ => true)) =
      .ok (FTAValidation.normalizeRows
        (interpreted (table states source known choices) (fun _ _ => true))) := by
  apply (SourceFTAValidation.mkFTA_exact _ _).mpr
  exact (SourceFTAValidation.validateRows_exact _ _).mp
    (validation_succeeds states source known choices closed root present)

variable [Ord Symbol]

/-- Successful execution constructs the complete finite canonical worker input. -/
def input (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.input (table states source known choices) (.inl root)
    (validation_succeeds states source known choices
      (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned) root present)

/-- Canonical class computation terminates on the input derived from discovery. -/
theorem canonical_completes (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    ∃ classes, CanonicalClasses.canonical
      (SourceSizedPreprocessing.graph (input limit states source known choices returned root present)) =
        some classes := by
  exact CanonicalClasses.canonical_terminates _

/-- Dense canonical sorting computes the original-key output rows. -/
def sortedRows (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.nativeSorted (table states source known choices) (.inl root)
    (validation_succeeds states source known choices
      (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned) root present)

/-- Dense source sorting equals sorting the derived finite input row for row. -/
theorem sorted_readback [TransOrd Symbol] [LawfulEqOrd Symbol]
    (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states)
    (state : Member (SourceDenseRows.keys (table states source known choices))) :
    (SourceSizedPreprocessing.sortedRows
      (input limit states source known choices returned root present) state).map forget =
        sortedRows limit states source known choices returned root present state.val :=
  SourceSizedStructuralKeys.sorted_readback (table states source known choices) (.inl root)
    (validation_succeeds states source known choices
      (SourceSizedDeterminizationRun.compile_closed limit states source known choices returned) root present) state

/-- The derived canonical sort supplies its own row-permutation proof. -/
theorem sorted_permutation (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) (state : Sum State (List State)) :
    (automaton (sortedRows limit states source known choices returned root present)
      (fun _ _ => true) state).Perm (SourceSizedDeterminizationRows.rows states source choices state) := by
  have closed := SourceSizedDeterminizationRun.compile_closed limit states source known choices returned
  have valid := validation_succeeds states source known choices closed root present
  have perm := SourceSizedStructuralKeys.sorted_automaton_perm
    (table states source known choices) (.inl root) valid (fun _ _ => true) state
  rw [interpreted_rows states source known choices closed] at perm
  exact perm

/-- Derived finite canonical sorting retains all exact signed optimized query laws. -/
theorem queries_exact (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (sortedRows limit states source known choices returned root present) (fun _ _ => true))
        (.inl root)) (Accepts source root) :=
  SourceSizedDeterminizationQueries.ordered_queries_exact limit states source plain supported known choices returned
    _ (sorted_permutation limit states source known choices returned root present) root

end MicroCFTA.SourceSizedDeterminizationFinite
