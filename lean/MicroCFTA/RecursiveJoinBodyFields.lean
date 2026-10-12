import MicroCFTA.RecursiveJoinCompiledFields
import MicroCFTA.KeyedNaryFields

/-!
# Callback composition for typed join bodies

A body retains a structural callback compiler next to its typed lowering.
Each constructor derives forward field agreement, restricted inverse laws,
and callback causality from its children. The laws are local to one body.
-/
namespace MicroCFTA.RecursiveJoinBodyFields
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveFieldBounds
open RecursiveJoinRecordBridge RecursiveJoinFields
open RecursiveJoinComposition (Body Compiled)
open RecursiveNaryCausality (Agree)
open RecursiveCallbackDistinct (Distinct)

/-- Grouped provenance identifies the whole ordered term class. -/
theorem realized_classes (classes : GroupedRecord.Classes (EngineTerm Symbol)) (field : Finite Symbol)
    (realizes : Realizes classes (termIndex field)) (size : Nat) :
    Decoder.values (classes size).members.plan = finiteClass field size := by
  apply List.ext_getElem?
  intro rank
  rw [← Decoder.decode_correct, ← RecursiveNaryInverse.select_class field (realized_indexed _ _ realizes) ⟨size, rank⟩]
  exact realizes.2 ⟨size, rank⟩

/-- Ordered classes and a local interval law determine count and decoder correspondence. -/
theorem realizes_of_classes (classes : GroupedRecord.Classes (EngineTerm Symbol)) (field : Finite Symbol)
    (indexed : FiniteIndex field)
    (same : ∀ size, Decoder.values (classes size).members.plan = finiteClass field size) :
    Realizes classes (termIndex field) := by
  constructor
  · intro size
    rw [Decoder.count_correct, same, finite_length]
    rfl
  · intro position
    rw [Decoder.decode_correct, same, ← RecursiveNaryInverse.select_class field indexed position]
    rfl

/-- A body stores derived local callback laws under arbitrary recursive root fields. -/
structure CheckedBody (Key Root Symbol Value : Type) where
  body : Body Key Root Symbol Value
  compile : (Key → Finite Symbol) → Finite Symbol
  indexed : ∀ roots, (∀ key, FiniteIndex (roots key)) → FiniteIndex (compile roots)
  realizes : ∀ environment roots,
    (∀ key, Realizes (environment key) (termIndex (roots key))) →
    Realizes (KeyedSource.record body.term environment) (termIndex (compile roots))
  exact : ∀ roots, (∀ key, FiniteIndex (roots key)) → ∀ limit,
    (∀ key, ExactBelow limit (roots key)) → ExactBelow limit (compile roots)
  agree : ∀ limit left right, (∀ key, Agree limit (left key) (right key)) →
    Agree limit (compile left) (compile right)
  candidates : Prop
  bounded : ∀ roots, (∀ key, RecursiveNaryChoice.Bounded (roots key)) → candidates →
    RecursiveNaryChoice.Bounded (compile roots)
  ordered : ∀ roots,
    (∀ key view wanted, ((roots key).positions view wanted).Pairwise (fun a b => before a b)) → candidates →
    ∀ view wanted, ((compile roots).positions view wanted).Pairwise (fun a b => before a b)
  distinct : ∀ roots, (∀ key, RecursiveNaryChoice.Bounded (roots key)) →
    (∀ key, RecursiveNaryChoice.Unique (roots key)) → candidates → RecursiveNaryChoice.Unique (compile roots)

/-- Existing keyed constructors provide structural fields from local finite-leaf inverse laws. -/
def ofNary [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (recipe : KeyedNaryAlignment.Recipe Key Root Symbol Value)
    (leaves : KeyedNaryFields.LeavesExact callbacks recipe) : CheckedBody Key Root Symbol Value where
  body := RecursiveJoinComposition.ofNary recipe
  compile := fun roots => KeyedNaryFields.compile callbacks roots recipe
  indexed := fun roots indexed => KeyedNaryFields.compiled_indexed callbacks roots indexed recipe
  realizes := by
    intro environment roots realized
    have indexed := fun key => realized_indexed _ _ (realized key)
    apply realizes_of_classes _ _ (KeyedNaryFields.compiled_indexed callbacks roots indexed recipe)
    intro size
    rw [KeyedNaryFields.compiled_classes callbacks roots indexed recipe size, KeyedSource.record_values]
    congr 1
    funext key size
    exact realized_classes _ _ (realized key) size
  exact := fun roots indexed limit exact => KeyedNaryFields.compiled_exact_below callbacks roots indexed limit exact recipe leaves
  agree := fun limit left right same => KeyedNaryFields.compiled_agree callbacks left right same recipe
  candidates := KeyedNaryFields.LeavesBounded callbacks recipe ∧
    KeyedNaryFields.LeavesOrdered callbacks recipe ∧ KeyedNaryFields.LeavesDistinct callbacks recipe
  bounded := fun roots bounded leaves => KeyedNaryFields.compiled_bounded callbacks roots bounded recipe leaves.1
  ordered := fun roots ordered leaves => KeyedNaryFields.compiled_ordered callbacks roots ordered recipe leaves.2.1
  distinct := fun roots bounded distinct leaves => KeyedNaryFields.compiled_distinct callbacks roots bounded distinct recipe leaves.1 leaves.2.2

/-- A user-value map does not change term fields or callbacks. -/
def map (transform : Value → Result) (inner : CheckedBody Key Root Symbol Value) : CheckedBody Key Root Symbol Result where
  body := RecursiveJoinComposition.map transform id inner.body
  compile := inner.compile
  indexed := inner.indexed
  realizes := by
    intro environment roots realizes
    have same := inner.realizes environment roots realizes
    constructor
    · exact same.1
    · intro position
      simpa [RecursiveJoinComposition.map, KeyedSource.record, GroupedRecord.map,
        SamplerReplay.mapRecord, Decoder.decode] using same.2 position
  exact := inner.exact
  agree := inner.agree
  candidates := inner.candidates
  bounded := inner.bounded
  ordered := inner.ordered
  distinct := inner.distinct

/-- A size guard encloses any join body and preserves its structural callback. -/
def pay [DecidableEq Symbol] (inner : CheckedBody Key Root Symbol Value) : CheckedBody Key Root Symbol Value where
  body := RecursiveJoinComposition.pay inner.body
  compile := fun roots => RecursiveFieldCombinators.pay (inner.compile roots)
  indexed := fun _ _ => RecursiveFieldCombinators.field_indexed _
  realizes := by
    intro environment roots realized
    apply realizes_of_classes _ _ (RecursiveFieldCombinators.field_indexed _)
    intro size
    have same := realized_classes _ _ (inner.realizes environment roots realized)
    cases size <;> simp [RecursiveJoinComposition.pay, KeyedSource.record, GroupedRecord.pay,
      RecursiveNaryFields.local_class, classTerms, same,
      GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values]
  exact := fun roots indexed limit exact => RecursiveFieldBounds.field_exact_below _ _
    (inner.exact roots indexed limit exact) (inner.indexed roots indexed)
  agree := fun limit left right same => RecursiveNaryCausality.local_fields (.pay (.finite _ _ (inner.agree limit left right same)))
  candidates := inner.candidates
  bounded := fun roots bounded leaves => RecursiveFieldCombinators.field_bounded _ (inner.bounded roots bounded leaves)
  ordered := fun roots ordered leaves => RecursiveFieldCombinators.field_ordered _ (inner.ordered roots ordered leaves)
  distinct := fun roots bounded distinct leaves => RecursiveFieldCombinators.field_distinct _
    (inner.bounded roots bounded leaves) (inner.distinct roots bounded distinct leaves)

/-- A source label adds its private wrapper and one size unit around any join body. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : CheckedBody Key Root Symbol Value) : CheckedBody Key Root Symbol Value where
  body := RecursiveJoinComposition.label symbol inner.body
  compile := fun roots => RecursiveFieldCombinators.label symbol (inner.compile roots)
  indexed := fun _ _ => RecursiveFieldCombinators.field_indexed _
  realizes := by
    intro environment roots realized
    apply realizes_of_classes _ _ (RecursiveFieldCombinators.field_indexed _)
    intro size
    have same := realized_classes _ _ (inner.realizes environment roots realized)
    cases size <;> simp [RecursiveJoinComposition.label, RecursiveJoinComposition.pay, RecursiveJoinComposition.map,
      KeyedSource.record, GroupedRecord.pay, GroupedRecord.map, SamplerReplay.mapRecord,
      RecursiveNaryFields.local_class, classTerms, same,
      GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values]
  exact := fun roots indexed limit exact => RecursiveFieldBounds.field_exact_below _ _
    (inner.exact roots indexed limit exact) (inner.indexed roots indexed)
  agree := fun limit left right same => RecursiveNaryCausality.local_fields (.label symbol (.finite _ _ (inner.agree limit left right same)))
  candidates := inner.candidates
  bounded := fun roots bounded leaves => RecursiveFieldCombinators.field_bounded _ (inner.bounded roots bounded leaves)
  ordered := fun roots ordered leaves => RecursiveFieldCombinators.field_ordered _ (inner.ordered roots ordered leaves)
  distinct := fun roots bounded distinct leaves => RecursiveFieldCombinators.field_distinct _
    (inner.bounded roots bounded leaves) (inner.distinct roots bounded distinct leaves)

/-- Ordinary application retains Apply when it encloses or occurs inside a grouped join. -/
def ap [DecidableEq Symbol] (functions : CheckedBody Key Root Symbol (A → B)) (arguments : CheckedBody Key Root Symbol A) :
    CheckedBody Key Root Symbol B where
  body := RecursiveJoinComposition.ap functions.body arguments.body
  compile := fun roots => RecursiveFieldCombinators.ap (functions.compile roots) (arguments.compile roots)
  indexed := fun _ _ => RecursiveFieldCombinators.field_indexed _
  realizes := by
    intro environment roots realized
    apply realizes_of_classes _ _ (RecursiveFieldCombinators.field_indexed _)
    intro size
    have fsame := realized_classes _ _ (functions.realizes environment roots realized)
    have asame := realized_classes _ _ (arguments.realizes environment roots realized)
    simp [RecursiveJoinComposition.ap, RecursiveJoinComposition.combine, KeyedSource.record,
      GroupedRecord.productClasses_values, GroupedRecord.map, SamplerReplay.mapRecord, Decoder.values,
      RecursiveNaryFields.local_class, classTerms, fsame, asame]
  exact := fun roots indexed limit exact => RecursiveFieldBounds.field_exact_below _ _
    ⟨functions.exact roots indexed limit exact, arguments.exact roots indexed limit exact⟩
    ⟨functions.indexed roots indexed, arguments.indexed roots indexed⟩
  agree := fun limit left right same => RecursiveNaryCausality.local_fields
    (.ap (.finite _ _ (functions.agree limit left right same)) (.finite _ _ (arguments.agree limit left right same)))
  candidates := functions.candidates ∧ arguments.candidates
  bounded := fun roots bounded leaves => RecursiveFieldCombinators.field_bounded _
    ⟨functions.bounded roots bounded leaves.1, arguments.bounded roots bounded leaves.2⟩
  ordered := fun roots ordered leaves => RecursiveFieldCombinators.field_ordered _
    ⟨functions.ordered roots ordered leaves.1, arguments.ordered roots ordered leaves.2⟩
  distinct := fun roots bounded distinct leaves => RecursiveFieldCombinators.field_distinct _
    ⟨functions.bounded roots bounded leaves.1, arguments.bounded roots bounded leaves.2⟩
    ⟨functions.distinct roots bounded distinct leaves.1, arguments.distinct roots bounded distinct leaves.2⟩

/-- Term lowering preserves every flat branch wrapper around a composite join body. -/
theorem alternatives_term (branches : List (Body Key Root Symbol Value)) :
    (RecursiveJoinComposition.alternatives branches).term =
      KeyedNaryAlignment.alternatives (branches.map (fun body => body.term)) := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second rest => simpa only [RecursiveJoinComposition.alternatives, RecursiveJoinComposition.choice,
          List.map_cons, KeyedNaryAlignment.alternatives] using congrArg (KeyedSource.Recipe.choice first.term) ih

/-- Flat choice retains its source numbering and derives all child callback laws. -/
def nary (count : Nat) (branches : Fin count → CheckedBody Key Root Symbol Value) : CheckedBody Key Root Symbol Value where
  body := RecursiveJoinComposition.nary count (fun index => (branches index).body)
  compile := fun roots => RecursiveNaryChoice.field (List.ofFn fun index => (branches index).compile roots)
  indexed := by
    intro roots indexed
    apply RecursiveNaryChoice.field_indexed
    intro child member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact (branches index).indexed roots indexed
  realizes := by
    intro environment roots realized
    have indexed := fun index => (branches index).indexed roots (fun key => realized_indexed _ _ (realized key))
    have children : ∀ child ∈ List.ofFn (fun index => (branches index).compile roots), FiniteIndex child := by
      intro child member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact indexed index
    apply realizes_of_classes _ _ (RecursiveNaryChoice.field_indexed _ children)
    intro size
    rw [RecursiveNaryFields.choice_class _ children]
    simp only [RecursiveJoinComposition.nary, alternatives_term, KeyedSource.record_values,
      KeyedNaryAlignment.alternatives_values, List.map_ofFn, RecursiveNaryChoice.classTerms,
      RecursiveNaryChoice.groups, List.flatMap]
    congr 1
    apply List.ext_getElem?
    intro rank
    by_cases within : rank < count
    · simp [within, RecursiveJoinComposition.map, RecursiveNaryChoice.wrap,
        KeyedNaryAlignment.branchTerm, ← KeyedSource.record_values,
        KeyedSource.record, GroupedRecord.map, SamplerReplay.mapRecord, Decoder.values,
        realized_classes _ _ ((branches ⟨rank, within⟩).realizes environment roots realized) size]
    · simp [within]
  exact := by
    intro roots indexed limit exact
    apply RecursiveNaryFieldBounds.field_exact_below
    · intro child member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact (branches index).indexed roots indexed
    · intro child member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact (branches index).exact roots indexed limit exact
  agree := by
    intro limit left right same
    apply RecursiveNaryCausality.choice_fields
    have related : ∀ indexes : List (Fin count), RecursiveRankMass.Related (Agree limit)
        (indexes.map fun index => (branches index).compile left)
        (indexes.map fun index => (branches index).compile right) := by
      intro indexes
      induction indexes with
      | nil => exact .nil
      | cons index rest ih => exact .cons ((branches index).agree limit left right same) ih
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using related (List.ofFn id)
  candidates := ∀ index, (branches index).candidates
  bounded := by
    intro roots bounded leaves
    apply RecursiveNaryChoice.field_bounded
    intro child member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact (branches index).bounded roots bounded (leaves index)
  ordered := fun _ _ _ => RecursiveNaryChoice.positions_ordered _
  distinct := by
    intro roots bounded distinct leaves
    apply RecursiveNaryChoice.field_unique
    · intro child member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact (branches index).bounded roots bounded (leaves index)
    · intro child member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact (branches index).distinct roots bounded distinct (leaves index)

/-- Heterogeneous checked arguments retain their callback compiler at every position. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : CheckedBody Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Erase callback certificates but retain each typed argument and source term recipe. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinComposition.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.body rest.lower

/-- Compile every argument field under the same mutual recursive environment. -/
def Chain.fields (roots : Key → Finite Symbol) : Chain Key Root Symbol Operand Result → List (Finite Symbol)
  | .nil => []
  | .cons argument rest => argument.compile roots :: rest.fields roots

/-- Every argument contributes its complete local source interval. -/
theorem Chain.indexed (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol)
    (indexed : ∀ key, FiniteIndex (roots key)) : ∀ argument ∈ arguments.fields roots, FiniteIndex argument := by
  induction arguments with
  | nil => simp [Chain.fields]
  | cons argument rest ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact argument.indexed roots indexed
      · exact ih child later

/-- Each chain argument inherits only the restricted recursive inverse contract. -/
theorem Chain.exact (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol)
    (indexed : ∀ key, FiniteIndex (roots key)) (limit : Nat) (exact : ∀ key, ExactBelow limit (roots key)) :
    ∀ argument ∈ arguments.fields roots, ExactBelow limit argument := by
  induction arguments with
  | nil => simp [Chain.fields]
  | cons argument rest ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact argument.exact roots indexed limit exact
      · exact ih child later

/-- The typed term fold realizes each directly selected prefix before the next argument. -/
theorem Chain.realizes (arguments : Chain Key Root Symbol Operand Result)
    (environment : Key → GroupedRecord.Classes (EngineTerm Symbol)) (roots : Key → Finite Symbol)
    (realized : ∀ key, Realizes (environment key) (termIndex (roots key)))
    (source : Compiled Key Root Symbol Operand (Accumulated Symbol)) (index : ValueIndex (Accumulated Symbol))
    (sourceRealized : Realizes (KeyedSource.record source.term environment) index) :
    Realizes (KeyedSource.record (RecursiveJoinComposition.accumulate source arguments.lower).term environment)
      (RecursiveJoinFields.accumulate index (arguments.fields roots)) := by
  induction arguments generalizing index with
  | nil => exact sourceRealized
  | cons argument rest ih =>
      exact ih _ _ (product_realizes _ _ _ _ _ sourceRealized (argument.realizes environment roots realized))

/-- Callback causality composes through every heterogeneous argument. -/
theorem Chain.agree (arguments : Chain Key Root Symbol Operand Result) (limit : Nat) (left right : Key → Finite Symbol)
    (same : ∀ key, Agree limit (left key) (right key)) :
    All₂ (Agree limit) (arguments.fields left) (arguments.fields right) := by
  induction arguments with
  | nil => exact .nil
  | cons argument rest ih => exact .cons (argument.agree limit left right same) ih

/-- Each argument retains only its finite leaves' candidate obligations. -/
def Chain.Candidates : Chain Key Root Symbol Operand Result → Prop
  | .nil => True
  | .cons argument rest => argument.candidates ∧ rest.Candidates

/-- Bounds for all candidate flags compose through heterogeneous arguments. -/
theorem Chain.bounded (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol)
    (bounded : ∀ key, RecursiveNaryChoice.Bounded (roots key)) (leaves : arguments.Candidates) :
    ∀ argument ∈ arguments.fields roots, RecursiveNaryChoice.Bounded argument := by
  induction arguments with
  | nil => simp [Chain.fields]
  | cons argument rest ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact argument.bounded roots bounded leaves.1
      · exact ih leaves.2 child later

/-- Distinct candidate positions compose through heterogeneous arguments. -/
theorem Chain.distinct (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol)
    (bounded : ∀ key, RecursiveNaryChoice.Bounded (roots key))
    (distinct : ∀ key, RecursiveNaryChoice.Unique (roots key)) (leaves : arguments.Candidates) :
    ∀ argument ∈ arguments.fields roots, RecursiveNaryChoice.Unique argument := by
  induction arguments with
  | nil => simp [Chain.fields]
  | cons argument rest ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact argument.distinct roots bounded distinct leaves.1
      · exact ih leaves.2 child later

/-- Every grouped join derives its structural callback laws from its operation and arguments. -/
def join (component : Nat) (operation : CheckedBody Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    CheckedBody Key Root Symbol Result where
  body := RecursiveJoinComposition.join component operation.body arguments.lower
  compile := fun roots => RecursiveJoinCallbacks.field component (operation.compile roots) (arguments.fields roots)
  indexed := fun roots indexed => RecursiveJoinCallbacks.field_indexed component _ _
    (operation.indexed roots indexed) (arguments.indexed roots indexed)
  realizes := by
    intro environment roots realized
    exact map_realizes _ _ _ (arguments.realizes environment roots realized _ _
      (map_realizes _ _ _ (operation.realizes environment roots realized)))
  exact := fun roots indexed limit exact => RecursiveJoinLocal.field_exact_below limit component _ _
    (operation.indexed roots indexed) (arguments.indexed roots indexed)
    (operation.exact roots indexed limit exact) (arguments.exact roots indexed limit exact)
  agree := fun limit left right same => RecursiveJoinLocal.field_agree limit component _ _ _ _
    (operation.agree limit left right same) (arguments.agree limit left right same)
  candidates := operation.candidates ∧ arguments.Candidates
  bounded := fun roots bounded leaves => RecursiveJoinCallbacks.field_bounded component _ _
    (fun term => operation.bounded roots bounded leaves.1 .whole [term])
    (fun argument member term => arguments.bounded roots bounded leaves.2 argument member .whole [term])
  ordered := fun _ _ _ => RecursiveJoinCallbacks.field_ordered component _ _
  distinct := fun roots bounded distinct leaves => RecursiveJoinCallbacks.field_distinct component _ _
    (fun term => operation.bounded roots bounded leaves.1 .whole [term])
    (fun argument member term => arguments.bounded roots bounded leaves.2 argument member .whole [term])
    (fun term => operation.distinct roots bounded distinct leaves.1 .whole [term])
    (fun argument member term => arguments.distinct roots bounded distinct leaves.2 argument member .whole [term])

end MicroCFTA.RecursiveJoinBodyFields
