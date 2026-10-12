import MicroCFTA.RecursiveJoinRecordBridge
import MicroCFTA.KeyedNarySource

/-!
# Compositional typed lowering for recursive grouped joins

The three source recipes retain independent value and term fields. Local
constructor proofs establish their projections, mass laws, and guards.
Grouped application evaluates user functions. The term map constructs JoinN.
-/
namespace MicroCFTA.RecursiveJoinComposition
open Language GeneratorCombinators
open KeyedNaryAlignment (EngineTerm)
open RecursiveJoinMass (Projects mapClasses product product_projects)
open KeyedTermMass (SameGroup map_left_group map_right_group)
open GroupedRecord (Classes)

/-- A typed lowering carries only local laws under arbitrary correlated environments. -/
structure Compiled (Key Root Symbol Value TermValue : Type) where
  value : KeyedSource.Recipe Key Root Value
  term : KeyedSource.Recipe Key (EngineTerm Symbol) TermValue
  paired : KeyedSource.Recipe Key (Root × EngineTerm Symbol) (Value × TermValue)
  values : ∀ (environment : Key → Classes (Root × EngineTerm Symbol)) (target : Key → Classes Root),
    (∀ key size, Projects Prod.fst (environment key size) (target key size)) →
    ∀ size, Projects Prod.fst (KeyedSource.record paired environment size) (KeyedSource.record value target size)
  terms : ∀ (environment : Key → Classes (Root × EngineTerm Symbol)) (target : Key → Classes (EngineTerm Symbol)),
    (∀ key size, Projects Prod.snd (environment key size) (target key size)) →
    ∀ size, Projects Prod.snd (KeyedSource.record paired environment size) (KeyedSource.record term target size)
  minimum : KeyedSource.minimumExpr paired = KeyedSource.minimumExpr value ∧
    KeyedSource.minimumExpr term = KeyedSource.minimumExpr value
  guards : ∀ known, KeyedSource.guarded paired known = KeyedSource.guarded value known ∧
    KeyedSource.guarded term known = KeyedSource.guarded value known

/-- A body exposes one user value and one private engine term. -/
abbrev Body (Key Root Symbol Value : Type) := Compiled Key Root Symbol Value (EngineTerm Symbol)

/-- The existing n-ary compiler supplies local laws for every existing body constructor. -/
def ofNary (recipe : KeyedNaryAlignment.Recipe Key Root Symbol Value) : Body Key Root Symbol Value where
  value := KeyedNaryAlignment.valueRecipe recipe
  term := KeyedNaryAlignment.termRecipe recipe
  paired := KeyedNaryAlignment.pairedRecipe recipe
  values := by
    intro environment target aligned size
    refine ⟨KeyedNaryMass.body_values recipe environment target (fun key size => (aligned key size).1) size, ?_⟩
    rw [KeyedSource.record_values, KeyedSource.record_values, KeyedNaryAlignment.body_values]
    congr 1
    funext key size
    exact (aligned key size).2
  terms := by
    intro environment target aligned size
    refine ⟨KeyedNaryMass.body_terms recipe environment target (fun key size => (aligned key size).1) size, ?_⟩
    rw [KeyedSource.record_values, KeyedSource.record_values, KeyedNaryAlignment.body_terms]
    congr 1
    funext key size
    exact (aligned key size).2
  minimum := KeyedNaryAlignment.minimum_expressions recipe
  guards := KeyedNaryAlignment.body_guards recipe

/-- Commuting maps preserve all local group projections. -/
theorem projects_map_both (source : GroupedRecord.Group A) (target : GroupedRecord.Group B)
    (project : A → B) (first : A → C) (second : B → D) (result : C → D)
    (aligned : Projects project source target) (commutes : ∀ entry, result (first entry) = second (project entry)) :
    Projects result (GroupedRecord.map first source) (GroupedRecord.map second target) := by
  refine ⟨map_right_group _ _ _ (map_left_group _ _ _ aligned.1), ?_⟩
  simp only [GroupedRecord.map, SamplerReplay.mapRecord, Decoder.values, List.map_map]
  rw [aligned.2, List.map_map]
  congr 1
  funext entry
  exact (commutes entry).symm

/-- Independent value and term maps preserve all local compilation laws. -/
def map (valueMap : Value → Result) (termMap : TermValue → TermResult)
    (inner : Compiled Key Root Symbol Value TermValue) : Compiled Key Root Symbol Result TermResult where
  value := .map valueMap inner.value
  term := .map termMap inner.term
  paired := .map (fun (entry : Value × TermValue) => (valueMap entry.1, termMap entry.2)) inner.paired
  values := fun environment target aligned size =>
    projects_map_both _ _ Prod.fst _ _ Prod.fst (inner.values environment target aligned size) (fun _ => rfl)
  terms := fun environment target aligned size =>
    projects_map_both _ _ Prod.snd _ _ Prod.snd (inner.terms environment target aligned size) (fun _ => rfl)
  minimum := inner.minimum
  guards := inner.guards

/-- A source Cartesian product combines values and terms in the same mixed-radix order. -/
def combine (valueCombine : A → B → C) (termCombine : TA → TB → TC)
    (left : Compiled Key Root Symbol A TA) (right : Compiled Key Root Symbol B TB) :
    Compiled Key Root Symbol C TC where
  value := .ap (.map valueCombine left.value) right.value
  term := .ap (.map termCombine left.term) right.term
  paired := .ap (.map (fun first second => (valueCombine first.1 second.1, termCombine first.2 second.2)) left.paired) right.paired
  values := by
    intro environment target aligned size
    exact product_projects _ _ Prod.fst Prod.fst Prod.fst _ _ _ _
      (left.values environment target aligned) (right.values environment target aligned) (fun _ _ => rfl) size
  terms := by
    intro environment target aligned size
    exact product_projects _ _ Prod.snd Prod.snd Prod.snd _ _ _ _
      (left.terms environment target aligned) (right.terms environment target aligned) (fun _ _ => rfl) size
  minimum := by
    simp only [KeyedSource.minimumExpr, left.minimum.1, left.minimum.2, right.minimum.1, right.minimum.2]
    trivial
  guards := by
    intro known
    simp only [KeyedSource.guarded, KeyedSource.minimumExpr,
      left.minimum.1, left.minimum.2, right.minimum.1, right.minimum.2,
      (left.guards known).1, (left.guards known).2, (right.guards known).1, (right.guards known).2]
    trivial

/-- Empty recursive classes satisfy every projection. -/
theorem projects_empty (transform : A → B) :
    Projects transform (GroupedRecord.empty : GroupedRecord.Group A) (GroupedRecord.empty : GroupedRecord.Group B) :=
  ⟨KeyedTermMass.empty_group, rfl⟩

/-- A size guard can enclose any composite join body. -/
def pay (inner : Compiled Key Root Symbol Value TermValue) : Compiled Key Root Symbol Value TermValue where
  value := .pay inner.value
  term := .pay inner.term
  paired := .pay inner.paired
  values := by
    intro environment target aligned size
    cases size with
    | zero => exact projects_empty _
    | succ size => exact inner.values environment target aligned size
  terms := by
    intro environment target aligned size
    cases size with
    | zero => exact projects_empty _
    | succ size => exact inner.terms environment target aligned size
  minimum := by simp only [KeyedSource.minimumExpr, inner.minimum.1, inner.minimum.2]; trivial
  guards := fun _ => ⟨rfl, rfl⟩

/-- Ordered binary merging preserves complete local projection records. -/
theorem projects_choice (transform : A → B)
    (left right : GroupedRecord.Group A) (first second : GroupedRecord.Group B)
    (leftProjects : Projects transform left first) (rightProjects : Projects transform right second) :
    Projects transform (GroupedRecord.merge [left, right]) (GroupedRecord.merge [first, second]) := by
  refine ⟨KeyedTermMass.merge_same _ _ (.cons leftProjects.1 (.cons rightProjects.1 .nil)), ?_⟩
  simp only [GroupedRecord.merge_values, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  rw [leftProjects.2, rightProjects.2]

/-- Unwrapped alternatives merge by retained key mass in their existing source order. -/
def choice (left right : Compiled Key Root Symbol Value TermValue) : Compiled Key Root Symbol Value TermValue where
  value := .choice left.value right.value
  term := .choice left.term right.term
  paired := .choice left.paired right.paired
  values := fun environment target aligned size => projects_choice _ _ _ _ _
    (left.values environment target aligned size) (right.values environment target aligned size)
  terms := fun environment target aligned size => projects_choice _ _ _ _ _
    (left.terms environment target aligned size) (right.terms environment target aligned size)
  minimum := by
    simp only [KeyedSource.minimumExpr, left.minimum.1, left.minimum.2, right.minimum.1, right.minimum.2]
    trivial
  guards := by
    intro known
    simp only [KeyedSource.guarded, (left.guards known).1, (left.guards known).2, (right.guards known).1, (right.guards known).2]
    trivial

/-- Lower an ordered list without extra private term constructors. -/
def alternatives : List (Body Key Root Symbol Value) → Body Key Root Symbol Value
  | [] => ofNary (.choice 0 Fin.elim0)
  | [first] => first
  | first :: second :: rest => choice first (alternatives (second :: rest))

/-- Flat source choice fixes each branch wrapper before the mass-aware lowering. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  alternatives (List.ofFn fun index => map id (KeyedNaryAlignment.branchTerm index.val) (branches index))

/-- Source application keeps its ordinary Apply constructor when requested. -/
def ap (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A) : Body Key Root Symbol B :=
  combine (fun function argument => function argument) (fun function argument => .node .apply [function, argument]) functions arguments

/-- Labels add the source term wrapper and one size unit around any join body. -/
def label (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  pay (map id (SupportTerms.labelTerm symbol) inner)

/-- Every argument in a join chain can have a different user-value type. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- The fold evaluates functions and retains the complete ordered argument forest. -/
def accumulate (source : Compiled Key Root Symbol Operand (RecursiveJoinFields.Accumulated Symbol)) :
    Chain Key Root Symbol Operand Result → Compiled Key Root Symbol Result (RecursiveJoinFields.Accumulated Symbol)
  | .nil => source
  | .cons argument rest => accumulate
      (combine (fun function value => function value) (fun before after => (before.1, before.2 ++ [after])) source argument) rest

/-- Grouped joins construct exact JoinN, CenterKeyed, and ArgKeyed wrappers. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Body Key Root Symbol Result :=
  map id (fun payload => SupportJoin.joinTerm component payload.1 payload.2)
    (accumulate (map id (fun term => (term, [])) operation) arguments)

/-- A nullary join keeps the operation's size, count, and source rank. -/
theorem join_nil (component : Nat) (operation : Body Key Root Symbol Value)
    (environment : Key → Classes (Root × EngineTerm Symbol)) (size : Nat) :
    Decoder.values (KeyedSource.record (join component operation .nil).paired environment size).members.plan =
      (Decoder.values (KeyedSource.record operation.paired environment size).members.plan).map
        (fun entry => (entry.1, SupportJoin.joinTerm component entry.2 [])) := by
  simp [join, accumulate, map, KeyedSource.record, GroupedRecord.map, SamplerReplay.mapRecord, Decoder.values, List.map_map]

end MicroCFTA.RecursiveJoinComposition
