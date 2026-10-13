import MicroCFTA.SourceDenseRowsCanonical
import MicroCFTA.SourceSizedTableEvaluation

/-!
# Cyclic queries after the shared row adapter

The finite carrier is the actual row-map key inventory. The compiler checks
the empty root, free variables, constraints, and ambiguity before canonical
preparation. Dense numbering supplies the canonical classes. Stable sorting
retains the original symbols, constraints, and ordered child references.
The prior arbitrary sorted-row premise is derived by this construction.
-/
namespace MicroCFTA.SourceCyclicRows
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceDenseRows
open RecursiveSize SizedRank RecursiveUnambiguous Std
attribute [local instance] lexOrd

variable {State : Type} {keys : List State}

/-- A closed finite row-map view before cyclic prechecks and canonical sorting. -/
structure Input (keys : List State) (Formula : Type) where
  root : Member keys
  emptyRoot : Bool
  freeVariables : List Nat
  rows : Member keys → List (SourceCyclicAutomaton.Row (Member keys) Formula)
  emptyRows : emptyRoot = true → rows root = []
  active : ∀ state edge, edge ∈ rows state → SourceCompactGuards.ActiveOption edge.constraint.equalities

/-- The source accepted language retains every original constraint. -/
noncomputable def original [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input keys Formula) : Automaton (Member keys) (Label Formula) :=
  fun state => (input.rows state).map (SourceCyclicAutomaton.guarded formulas solver)

/-- The source triple key reads no constraint field. -/
def rowKey (order : Label Formula → Key) (classes : Node → Nat)
    (row : SourceCyclicAutomaton.Row Node Formula) : (Nat × Key) × List Nat :=
  ((row.children.length, order row.symbol), row.children.map classes)

/-- Sort complete source rows, retaining constraint and child-list payloads. -/
def sortRows [Ord Key] (input : Input keys Formula) (order : Label Formula → Key)
    (classes : Member keys → Nat) : Member keys → List (SourceCyclicAutomaton.Row (Member keys) Formula) :=
  fun state => (input.rows state).mergeSort fun first second =>
    (compare (rowKey order classes first) (rowKey order classes second)).isLE

/-- The exact canonical sort constructs the ordered-row contract of the cyclic compiler. -/
def preparedInput [Ord Key] (input : Input keys Formula) (order : Label Formula → Key)
    (classes : Member keys → Nat) : SourceCyclicAutomaton.Input (Member keys) Formula where
  root := input.root
  emptyRoot := input.emptyRoot
  freeVariables := input.freeVariables
  nodes := keys.attach
  rows := input.rows
  ordered := sortRows input order classes
  permutation := fun _ => List.mergeSort_perm _ _
  complete := by intro state edge member; simp
  emptyRows := input.emptyRows
  active := input.active

/-- Finite row keys derive the complete synchronous-product inventory. -/
def pairs (keys : List State) : List (Member keys × Member keys) :=
  keys.attach.flatMap fun first => keys.attach.map fun second => (first, second)

theorem pairs_complete (keys : List State) (pair : Member keys × Member keys) : pair ∈ pairs keys := by
  exact List.mem_flatMap.mpr ⟨pair.1, by simp, List.mem_map.mpr ⟨pair.2, by simp, rfl⟩⟩

/-- Mapping retained guards commutes with the actual stable source sort. -/
theorem guarded_sort [DecidableEq Formula] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (classes : Member keys → Nat) :
    SourceCyclicAutomaton.ordered formulas solver (preparedInput input order classes) =
      SourceDenseRowsCanonical.sortRows (original formulas solver input) order classes := by
  funext state
  unfold SourceCyclicAutomaton.ordered preparedInput sortRows SourceDenseRowsCanonical.sortRows original
  apply List.map_mergeSort
  intro first _ second _
  rfl

/-- Compute canonical classes on the dense finite state domain. -/
noncomputable def canonical [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) : Option (Member keys → Nat) :=
  (CanonicalClasses.canonical (SourceDenseRowsCanonical.denseGraph keys (original formulas solver input) order)).map
    fun classes state => classes (number keys state)

/-- The dense canonical stage finishes for every finite row-map inventory. -/
theorem canonical_finite [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) : ∃ classes, canonical formulas solver input order = some classes := by
  obtain ⟨classes, finished⟩ := CanonicalClasses.canonical_terminates
    (SourceDenseRowsCanonical.denseGraph keys (original formulas solver input) order)
  exact ⟨fun state => classes (number keys state), by simp [canonical, finished]⟩

/-- Completed dense classes retain the exact row sequence proved by the shared preparation worker. -/
theorem prepared_exact [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (classes : Member keys → Nat)
    (finished : canonical formulas solver input order = some classes) :
    SourceDenseRowsCanonical.prepare keys (original formulas solver input) order =
      some (SourceCyclicAutomaton.ordered formulas solver (preparedInput input order classes)) := by
  obtain ⟨dense, computed, same⟩ := Option.map_eq_some_iff.mp finished
  rw [← same, guarded_sort]
  simp [SourceDenseRowsCanonical.prepare, computed]

/-- The actual precheck order does not demand canonical preparation after a rejected input. -/
noncomputable def compile [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) :
    Option (Except SourceCyclicAutomaton.Error (Automaton (Member keys) (Label Formula))) :=
  let base := preparedInput input order (fun _ => 0)
  if input.emptyRoot then some (.ok (fun _ => []))
  else if !input.freeVariables.isEmpty then some (.error .openAutomaton)
  else if SourceCyclicAutomaton.hasConstraints base then some (.error .constrainedEdges)
  else if SourceCyclicAutomaton.hasAmbiguity formulas solver base (pairs keys) (pairs_complete keys) then
    some (.error .ambiguousAutomaton)
  else (canonical formulas solver input order).map fun classes =>
    .ok (SourceCyclicAutomaton.ordered formulas solver (preparedInput input order classes))

/-- A completed canonical stage identifies the exact previously verified cyclic compiler result. -/
theorem compile_equation [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (classes : Member keys → Nat)
    (finished : canonical formulas solver input order = some classes) :
    compile formulas solver input order = some (SourceCyclicAutomaton.compile formulas solver
      (preparedInput input order classes) (pairs keys) (pairs_complete keys)) := by
  unfold compile SourceCyclicAutomaton.compile
  have lift {Value : Type} (condition : Prop) [Decidable condition] (yes no : Value) :
      some (if condition then yes else no) = if condition then some yes else some no := by
    by_cases condition <;> simp [*]
  simp only [finished, Option.map_some, lift]
  rfl

/-- All finite source prechecks and the dense canonical stage have a completed result. -/
theorem compile_finite [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) : ∃ result, compile formulas solver input order = some result := by
  obtain ⟨classes, finished⟩ := canonical_finite formulas solver input order
  exact ⟨_, compile_equation formulas solver input order classes finished⟩

/-- Successful actual preparation derives plainness, distinct classes, and original acceptance. -/
theorem compile_exact [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (output : Automaton (Member keys) (Label Formula))
    (success : compile formulas solver input order = some (.ok output)) :
    Decoder.Plain output ∧ SizedRank.Unambiguous output ∧
      ∀ term, Accepts output input.root term ↔ Accepts (original formulas solver input) input.root term := by
  obtain ⟨classes, finished⟩ := canonical_finite formulas solver input order
  rw [compile_equation formulas solver input order classes finished] at success
  exact SourceCyclicAutomaton.compile_exact formulas solver (preparedInput input order classes)
    (pairs keys) (pairs_complete keys) output (Option.some.inj success)

/-- Each successful current import has a finite optimized query of exactly the distinct source class. -/
theorem class_correct [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (output : Automaton (Member keys) (Label Formula))
    (success : compile formulas solver input order = some (.ok output)) (size : Nat) :
    SourceSizedTableEvaluation.Evaluation output (size + 1) size input.root
      (countAt output size input.root) (compileAt output size input.root) ∧
      (RecursiveSize.enumerate output size input.root).Nodup ∧
      (∀ term, term ∈ RecursiveSize.enumerate output size input.root ↔
        Accepts (original formulas solver input) input.root term ∧ nodeSize term = size) ∧
      countAt output size input.root = (RecursiveSize.enumerate output size input.root).length ∧
      (∀ rank, Decoder.decode (compileAt output size input.root) rank = (RecursiveSize.enumerate output size input.root)[rank]?) := by
  obtain ⟨plain, unique, language⟩ := compile_exact formulas solver input order output success
  refine ⟨SourceSizedTableEvaluation.finite_bound output size input.root, unique input.root size, ?_,
    countAt_correct output size input.root, ?_⟩
  · intro term
    rw [mem_enumerate_iff output plain, language]
  · intro rank
    rw [Decoder.decode_correct, values_compileAt]

/-- Both rank inverse laws and exact language rejection hold after the actual dense preparation. -/
theorem query_inverses [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input keys Formula)
    (order : Label Formula → Key) (output : Automaton (Member keys) (Label Formula))
    (success : compile formulas solver input order = some (.ok output)) :
    (∀ position term, TablePosition.positionsOf output term input.root = some position ↔
      replayPosition output input.root position = some term) ∧
    (∀ bound rank, (∃ term, selectAtMost output input.root bound rank = some term) ↔ rank < countAtMost output bound input.root) ∧
    (∀ bound rank term, rankAtMost output input.root bound term = some rank ↔ selectAtMost output input.root bound rank = some term) ∧
    (∀ bound term, rankAtMost output input.root bound term = none ↔
      ¬(Accepts (original formulas solver input) input.root term ∧ nodeSize term ≤ bound)) := by
  obtain ⟨classes, finished⟩ := canonical_finite formulas solver input order
  rw [compile_equation formulas solver input order classes finished] at success
  exact SourceCyclicAutomaton.exact_index_api formulas solver (preparedInput input order classes)
    (pairs keys) (pairs_complete keys) output (Option.some.inj success)

end MicroCFTA.SourceCyclicRows
