import MicroCFTA.RecursiveJoinInspection

/-!
# Inspection fields alongside typed recursive join bodies

The diagnostic compiler follows each source constructor independently of
value, term, mass, and callback fields. Heterogeneous chains retain all
argument inspections in source order. Group names do not alter generation.
-/
namespace MicroCFTA.RecursiveJoinInspectionBody
open Language GeneratorCombinators
open RecursiveCallbackTermination (EngineTerm)
open RecursiveJoinInspection (Inspection)

/-- Finite source inspections remain independently supplied diagnostic records. -/
abbrev LeafInspections (Symbol : Type) := {Value : Type} → FiniteSource.Source (Value × EngineTerm Symbol) → Inspection Symbol

/-- Source keyed bodies compile their diagnostic fields without reading a generated member. -/
def compile (leaves : LeafInspections Symbol) (roots : Key → Inspection Symbol) :
    KeyedNaryAlignment.Recipe Key Root Symbol Value → Inspection Symbol
  | .finite source | .retained _ _ source => leaves source
  | .occurrence key => roots key
  | .map _ inner | .pay inner => compile leaves roots inner
  | .label symbol inner => RecursiveJoinInspection.label symbol (compile leaves roots inner)
  | .choice _ branches => RecursiveJoinInspection.choice (List.ofFn fun index => compile leaves roots (branches index))
  | .ap functions arguments => RecursiveJoinInspection.ap (compile leaves roots functions) (compile leaves roots arguments)

/-- Each finite leaf supplies only the validity of its own diagnostic descriptor. -/
def LeavesValid (inspections : LeafInspections Symbol) : KeyedNaryAlignment.Recipe Key Root Symbol Value → Prop
  | .finite source | .retained _ _ source => RecursiveJoinInspection.Valid (inspections source).layer
  | .occurrence _ => True
  | .map _ inner | .pay inner | .label _ inner => LeavesValid inspections inner
  | .choice _ branches => ∀ index, LeavesValid inspections (branches index)
  | .ap functions arguments => LeavesValid inspections functions ∧ LeavesValid inspections arguments

/-- Constructor compilation derives descriptor validity from finite leaves and recursive occurrences. -/
theorem compile_valid (inspections : LeafInspections Symbol) (roots : Key → Inspection Symbol)
    (rootValid : ∀ key, RecursiveJoinInspection.Valid (roots key).layer)
    (recipe : KeyedNaryAlignment.Recipe Key Root Symbol Value) (leaves : LeavesValid inspections recipe) :
    RecursiveJoinInspection.Valid (compile inspections roots recipe).layer := by
  induction recipe with
  | finite source | retained mass positive source => exact leaves
  | occurrence key => exact rootValid key
  | map transform inner ih | pay inner ih => exact ih leaves
  | label symbol inner ih => exact RecursiveJoinInspection.label_valid symbol _
  | ap functions arguments ihf iha =>
      simpa only [compile, RecursiveJoinInspection.ap, RecursiveJoinInspection.Valid] using
        And.intro (ihf leaves.1) (iha leaves.2)
  | choice count branches ih =>
      apply RecursiveJoinInspection.choice_valid
      intro inspection member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact ih index (leaves index)

/-- Each body keeps its checked generator and the independent diagnostic compiler. -/
structure Body (Key Root Symbol Value : Type) where
  checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value
  inspect : (Key → Inspection Symbol) → Inspection Symbol
  valid : ∀ roots, (∀ key, RecursiveJoinInspection.Valid (roots key).layer) →
    RecursiveJoinInspection.Valid (inspect roots).layer

/-- Existing source bodies retain their finite inspection producer at each leaf. -/
def ofNary [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (inspections : LeafInspections Symbol) (recipe : KeyedNaryAlignment.Recipe Key Root Symbol Value)
    (exact : KeyedNaryFields.LeavesExact callbacks recipe) (valid : LeavesValid inspections recipe) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.ofNary callbacks recipe exact, fun roots => compile inspections roots recipe,
    fun roots rootValid => compile_valid inspections roots rootValid recipe valid⟩

/-- Group naming updates only the diagnostic name read by surrounding joins. -/
def named (name : Option String) (body : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨body.checked, fun roots => RecursiveJoinInspection.named name (body.inspect roots), body.valid⟩

/-- User maps preserve the complete source inspection record. -/
def map (transform : Value → Result) (body : Body Key Root Symbol Value) : Body Key Root Symbol Result :=
  ⟨RecursiveJoinBodyFields.map transform body.checked, body.inspect, body.valid⟩

/-- Paying size preserves both graph and optional name. -/
def pay [DecidableEq Symbol] (body : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.pay body.checked, body.inspect, body.valid⟩

/-- Labels execute diagnostic source closing and preserve the operand's name. -/
def label [DecidableEq Symbol] (symbol : Symbol) (body : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.label symbol body.checked, fun roots => RecursiveJoinInspection.label symbol (body.inspect roots),
    fun roots _ => RecursiveJoinInspection.label_valid symbol (body.inspect roots)⟩

/-- Ordinary application retains both diagnostic operands and clears its result name. -/
def ap [DecidableEq Symbol] (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A) : Body Key Root Symbol B :=
  ⟨RecursiveJoinBodyFields.ap functions.checked arguments.checked,
    fun roots => RecursiveJoinInspection.ap (functions.inspect roots) (arguments.inspect roots),
    fun roots rootValid => by
      simpa only [RecursiveJoinInspection.ap, RecursiveJoinInspection.Valid] using
        And.intro (functions.valid roots rootValid) (arguments.valid roots rootValid)⟩

/-- Flat choice keeps branch order and computes its common diagnostic name. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.nary count (fun index => (branches index).checked),
    fun roots => RecursiveJoinInspection.choice (List.ofFn fun index => (branches index).inspect roots), by
      intro roots rootValid
      apply RecursiveJoinInspection.choice_valid
      intro inspection member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact (branches index).valid roots rootValid⟩

/-- A heterogeneous chain retains one inspection producer per typed argument. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Erase diagnostic fields without changing the checked argument chain. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinBodyFields.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.checked rest.lower

/-- Diagnostic arguments are read once each in their original signature order. -/
def Chain.inspections (roots : Key → Inspection Symbol) : Chain Key Root Symbol Operand Result → List (Inspection Symbol)
  | .nil => []
  | .cons argument rest => argument.inspect roots :: rest.inspections roots

/-- The heterogeneous argument list derives each descriptor invariant independently. -/
theorem Chain.valid (roots : Key → Inspection Symbol)
    (rootValid : ∀ key, RecursiveJoinInspection.Valid (roots key).layer)
    (arguments : Chain Key Root Symbol Operand Result) :
    ∀ argument ∈ arguments.inspections roots, RecursiveJoinInspection.Valid argument.layer := by
  induction arguments with
  | nil => simp [inspections]
  | cons argument rest ih =>
      intro inspection member
      simp only [inspections, List.mem_cons] at member
      rcases member with rfl | member
      · exact argument.valid roots rootValid
      · exact ih inspection member

/-- Each join builds its checked fields and its independently named diagnostic graph. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Body Key Root Symbol Result :=
  ⟨RecursiveJoinBodyFields.join component operation.checked arguments.lower,
    fun roots => RecursiveJoinInspection.join component (operation.inspect roots) (arguments.inspections roots),
    fun roots rootValid => RecursiveJoinInspection.join_valid component _ _
      (operation.valid roots rootValid) (arguments.valid roots rootValid)⟩

/-- The complete diagnostic family uses one separate source binder with the same key mapping. -/
def family (token : Nat) (code : Key → Nat) (keys : List Key) (names : Key → Option String)
    (program : Key → Body Key Root Symbol Root) : RecursiveJoinInspection.Graph Symbol :=
  RecursiveJoinInspection.family token code keys names (fun roots key => (program key).inspect roots)

/-- Every body in the diagnostic knot derives its closing invariant from its actual occurrences. -/
theorem family_body_valid (token : Nat) (code : Key → Nat) (names : Key → Option String)
    (program : Key → Body Key Root Symbol Root) (key : Key) :
    RecursiveJoinInspection.Valid ((program key).inspect
      (fun key => RecursiveJoinInspection.occurrence token (code key) (names key))).layer :=
  (program key).valid _ (fun key => RecursiveJoinInspection.occurrence_valid token (code key) (names key))

/-- A diagnostic name cannot change any generation field or any callback contract. -/
theorem named_checked (name : Option String) (body : Body Key Root Symbol Value) :
    (named name body).checked = body.checked := rfl

/-- Names and diagnostic root environments cannot enter the independently tied value family. -/
theorem named_family (names : Key → Option String) (program : Key → Body Key Root Symbol Root) :
    (fun key => (named (names key) (program key)).checked.body.value) =
      (fun key => (program key).checked.body.value) := rfl

/-- Nullary joins retain their operation inspection without inventing an argument key. -/
theorem join_nil (component : Nat) (operation : Body Key Root Symbol Value) (roots : Key → Inspection Symbol) :
    (join component operation .nil).inspect roots = RecursiveJoinInspection.join component (operation.inspect roots) [] := rfl

/-- Every joined inspection erases to the exact unreduced source join constructor. -/
theorem join_graph (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result)
    (roots : Key → Inspection Symbol) :
    RecursiveJoinInspection.erase ((join component operation arguments).inspect roots).graph =
      SupportJoin.joinNode component (RecursiveJoinInspection.erase (operation.inspect roots).graph)
        ((arguments.inspections roots).map fun argument => RecursiveJoinInspection.erase argument.graph) :=
  RecursiveJoinInspection.erase_join component (operation.inspect roots) (arguments.inspections roots)

end MicroCFTA.RecursiveJoinInspectionBody
