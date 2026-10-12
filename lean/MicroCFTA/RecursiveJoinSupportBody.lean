import MicroCFTA.RecursiveJoinSupportView

/-!
# Typed source bodies with independently assembled support graphs

Every constructor builds its graph from operand supports. Local language
laws relate that graph to the independent term recipe under arbitrary
recursive family languages. No complete recursive language law is assumed.
-/
namespace MicroCFTA.RecursiveJoinSupportBody
open Language GeneratorCombinators BinderLanguage SupportGraph
open RecursiveCallbackTermination (EngineTerm)
open RecursiveJoinSupportSemantics (denotes)

/-- Each keyed occurrence restricts the same open family reference. -/
def rootLanguage (token : Nat) (code : Key → Nat) (environment : Env (Label Symbol))
    (key : Key) : EngineTerm Symbol → Prop :=
  meaning environment (restrictKey (code key) (.ref token))

/-- The source occurrence is an ordinary constrained root for all closing operations. -/
def occurrenceView (token key : Nat) : RecursiveJoinSupportView.View Symbol :=
  RecursiveJoinSupportView.ordinary ⟨.atKey, fun term => PathsEqual term [0] [1, 0]⟩
    [singleton (.node (.key key) []), .ref token] (by rfl)

/-- A support body retains a checked term compiler and a separately constructed open graph. -/
structure Body (Key Root Symbol Value : Type) where
  checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value
  support : Nat → (Key → Nat) → RecursiveJoinSupportView.View Symbol
  exact : ∀ token code environment term,
    meaning environment (support token code).graph term ↔
      denotes checked.body.term (rootLanguage token code environment) term

/-- One finite leaf supplies its original support and a local finite-language correspondence. -/
def finite [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (source : FiniteSource.Source (Value × EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite (Key := Key) (Root := Root) source))
    (view : RecursiveJoinSupportView.View Symbol)
    (supports : ∀ environment term, meaning environment view.graph term ↔
      ∃ size, term ∈ FiniteSource.classMembers (.map Prod.snd source) size) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.ofNary callbacks (.finite source) inverse
  support := fun _ _ => view
  exact := fun _ _ => supports

/-- A retained mass changes no member of its finite support language. -/
def retained [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (mass : Nat → Rat) (positive : ∀ size, 0 < mass size)
    (source : FiniteSource.Source (Value × EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite (Key := Key) (Root := Root) source))
    (view : RecursiveJoinSupportView.View Symbol)
    (supports : ∀ environment term, meaning environment view.graph term ↔
      ∃ size, term ∈ FiniteSource.classMembers (.map Prod.snd source) size) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.ofNary callbacks (.retained mass positive source) inverse
  support := fun _ _ => view
  exact := fun _ _ => supports

/-- Recursive occurrences use the source AtKey equality against the shared family reference. -/
def occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol) (key : Key) : Body Key Root Symbol Root where
  checked := RecursiveJoinBodyFields.ofNary callbacks (.occurrence key) True.intro
  support := fun token code => occurrenceView token (code key)
  exact := by intro token code environment term; rfl

/-- User-value maps retain the original support graph. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.map transform inner.checked
  support := inner.support
  exact := by
    intro token code environment term
    simpa [RecursiveJoinBodyFields.map, RecursiveJoinComposition.map, denotes] using
      inner.exact token code environment term

/-- Pay changes the size field and retains the support language. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.pay inner.checked
  support := inner.support
  exact := inner.exact

/-- Source labels close the actual private support layer and add one size unit. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.label symbol inner.checked
  support := fun token code => RecursiveJoinSupportView.label symbol (inner.support token code)
  exact := by
    intro token code environment term
    rw [RecursiveJoinSupportView.label_exact]
    simp only [RecursiveJoinBodyFields.label, RecursiveJoinComposition.label, RecursiveJoinComposition.pay,
      RecursiveJoinComposition.map, denotes, inner.exact]

/-- Application keeps separate function and argument support operands. -/
def ap [DecidableEq Symbol] (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A) : Body Key Root Symbol B where
  checked := RecursiveJoinBodyFields.ap functions.checked arguments.checked
  support := fun token code => RecursiveJoinSupportView.ap (functions.support token code) (arguments.support token code)
  exact := by
    intro token code environment term
    change meaning environment (edge .apply [(functions.support token code).graph, (arguments.support token code).graph]) term ↔ _
    rw [SupportSpine.apply_exact]
    simp only [functions.exact, arguments.exact, RecursiveJoinBodyFields.ap, RecursiveJoinComposition.ap,
      RecursiveJoinComposition.combine, denotes]
    constructor
    · rintro ⟨function, argument, acceptedFunction, acceptedArgument, rfl⟩
      exact ⟨_, argument, ⟨function, acceptedFunction, rfl⟩, acceptedArgument, rfl⟩
    · rintro ⟨_, argument, ⟨function, acceptedFunction, rfl⟩, acceptedArgument, rfl⟩
      exact ⟨function, argument, acceptedFunction, acceptedArgument, rfl⟩

/-- Flat choice preserves each source branch wrapper around its complete support. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.nary count (fun index => (branches index).checked)
  support := fun token code => RecursiveJoinSupportView.choice (List.ofFn fun index => (branches index).support token code)
  exact := by
    intro token code environment term
    change meaning environment (.alternatives ((List.ofFn fun index => (branches index).support token code).mapIdx
      fun index body => edge (.choice index) [body.graph])) term ↔ _
    rw [RecursiveJoinSupportView.choice_exact]
    simp only [RecursiveJoinBodyFields.nary, RecursiveJoinComposition.nary,
      RecursiveJoinBodyFields.alternatives_term, List.map_ofFn,
      RecursiveJoinSupportSemantics.denotes_alternatives, List.mem_ofFn,
      RecursiveJoinComposition.map]
    constructor
    · rintro ⟨index, inside, original, accepted, rfl⟩
      have bound : index < count := by simpa using inside
      refine ⟨_, ⟨⟨index, bound⟩, rfl⟩, original, ?_, rfl⟩
      exact ((branches ⟨index, bound⟩).exact token code environment original).mp (by simpa using accepted)
    · rintro ⟨_, ⟨index, rfl⟩, original, accepted, rfl⟩
      refine ⟨index.val, by simp, original, ?_, rfl⟩
      simpa using ((branches index).exact token code environment original).mpr accepted

/-- Heterogeneous support arguments retain each independent typed operand. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Erase support fields and retain the original checked argument chain. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinBodyFields.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.checked rest.lower

/-- The ordered source support operands of one matched chain. -/
def Chain.views (token : Nat) (code : Key → Nat) : Chain Key Root Symbol Operand Result → List (RecursiveJoinSupportView.View Symbol)
  | .nil => []
  | .cons argument rest => argument.support token code :: rest.views token code

/-- Each argument has its own independently compiled term recipe. -/
def Chain.recipes : Chain Key Root Symbol Operand Result → List (KeyedSource.Recipe Key (EngineTerm Symbol) (EngineTerm Symbol))
  | .nil => []
  | .cons argument rest => argument.checked.body.term :: rest.recipes

/-- The source term product accumulates an operation and an ordered argument forest. -/
def fold (source : KeyedSource.Recipe Key Root (EngineTerm Symbol × List (EngineTerm Symbol))) :
    List (KeyedSource.Recipe Key Root (EngineTerm Symbol)) → KeyedSource.Recipe Key Root (EngineTerm Symbol × List (EngineTerm Symbol))
  | [] => source
  | argument :: rest => fold (.ap (.map (fun before after => (before.1, before.2 ++ [after])) source) argument) rest

/-- Typed lowering retains exactly the source support term fold. -/
theorem Chain.fold_term (arguments : Chain Key Root Symbol Operand Result)
    (source : RecursiveJoinComposition.Compiled Key Root Symbol Operand (RecursiveJoinFields.Accumulated Symbol)) :
    (RecursiveJoinComposition.accumulate source arguments.lower.lower).term = fold source.term arguments.recipes := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih => exact ih _

/-- The accumulated term language is precisely the Cartesian product of all operand languages. -/
theorem fold_exact (arguments : List (KeyedSource.Recipe Key Root (EngineTerm Symbol)))
    (source : KeyedSource.Recipe Key Root (EngineTerm Symbol × List (EngineTerm Symbol)))
    (environment : Key → Root → Prop) (payload : EngineTerm Symbol × List (EngineTerm Symbol)) :
    denotes (fold source arguments) environment payload ↔
      ∃ initial terms, denotes source environment initial ∧ RecursiveRankMass.Related (fun recipe term => denotes recipe environment term) arguments terms ∧
        payload = (initial.1, initial.2 ++ terms) := by
  induction arguments generalizing source payload with
  | nil =>
      constructor
      · intro accepted; exact ⟨payload, [], accepted, .nil, by simp⟩
      · rintro ⟨initial, terms, accepted, related, rfl⟩
        cases related
        simpa [fold] using accepted
  | cons argument rest ih =>
      rw [fold, ih]
      constructor
      · rintro ⟨_, terms, ⟨_, first, ⟨initial, accepted, rfl⟩, firstAccepted, rfl⟩, related, rfl⟩
        exact ⟨initial, first :: terms, accepted, .cons firstAccepted related, by simp [List.append_assoc]⟩
      · rintro ⟨initial, terms, accepted, related, rfl⟩
        cases related with
        | cons head tail =>
            exact ⟨_, _, ⟨_, _, ⟨initial, accepted, rfl⟩, head, rfl⟩, tail, by simp [List.append_assoc]⟩

/-- Heterogeneous operand support and independent term languages agree pointwise. -/
theorem Chain.exact (arguments : Chain Key Root Symbol Operand Result) (token : Nat) (code : Key → Nat)
    (environment : Env (Label Symbol)) (terms : List (EngineTerm Symbol)) :
    All₂ (meaning environment) ((arguments.views token code).map (·.graph)) terms ↔
      RecursiveRankMass.Related (fun recipe term => denotes recipe (rootLanguage token code environment) term) arguments.recipes terms := by
  induction arguments generalizing terms with
  | nil => cases terms <;> constructor <;> intro accepted <;> cases accepted <;> exact .nil
  | cons argument rest ih =>
      cases terms with
      | nil => constructor <;> intro accepted <;> cases accepted
      | cons first terms =>
          constructor <;> intro accepted
          · cases accepted with
            | cons head tail => exact .cons ((argument.exact token code environment first).mp head) ((ih terms).mp tail)
          · cases accepted with
            | cons head tail => exact .cons ((argument.exact token code environment first).mpr head) ((ih terms).mpr tail)

/-- A matched recursive join assembles the complete source support and exact term product. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Body Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.join component operation.checked arguments.lower
  support := fun token code => RecursiveJoinSupportView.join component (operation.support token code) (arguments.views token code)
  exact := by
    intro token code environment term
    change meaning environment (SupportJoin.joinNode component (operation.support token code).graph
      ((arguments.views token code).map (·.graph))) term ↔ _
    rw [SupportJoin.join_exact]
    simp only [SupportGraph.forest_all₂, arguments.exact]
    simp only [operation.exact, RecursiveJoinBodyFields.join, RecursiveJoinComposition.join,
      RecursiveJoinComposition.map, denotes]
    rw [arguments.fold_term]
    dsimp only
    simp only [fold_exact, denotes]
    constructor
    · rintro ⟨operationTerm, terms, accepted, related, rfl⟩
      refine ⟨(operationTerm, terms), ?_, rfl⟩
      exact ⟨(operationTerm, []), terms, ⟨operationTerm, accepted, rfl⟩, related, rfl⟩
    · rintro ⟨payload, ⟨initial, terms, ⟨operationTerm, accepted, initialEq⟩, related, payloadEq⟩, termEq⟩
      subst initial payload term
      exact ⟨operationTerm, terms, accepted, related, rfl⟩

end MicroCFTA.RecursiveJoinSupportBody
