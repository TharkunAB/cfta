import Lean

/-!
# Erasure: Lean types as Hectare's first-order types

Hectare's automaton (`Data.CFTA.Gen.Synthesis` in `cfta-generator`) has
first-order types: type variables, function types, and type constructors with
arguments. A Lean type becomes such a type after these rules:

* The reducible definitions are unfolded at each node (`whnfR`), so `Unit` is
  `PUnit` and `optParam α d` is `α`.
* At the top of a constant's type, an implicit or strict-implicit binder whose
  type is a universe (`{α : Type u}`) becomes a Hectare type variable, which
  Hectare instantiates at each use. An instance-implicit binder (`[BEq α]`) is
  dropped: the class constraint is erased. An implicit binder of a value
  (`{n : Nat}`) is dropped.
* An explicit binder becomes a function argument. An explicit binder of a
  universe (an explicit type argument) or of a proposition (a proof argument)
  gives no Hectare type: Hectare cannot propose types or proofs.
* A type constructor keeps its arguments that are types; the arguments that are
  values (indices such as the `n` of `Fin n`) and propositions are dropped. So a
  dependent binder `(n : Nat) → Fin n` erases to `Nat -> Fin`: an
  over-approximation, which Lean's check then refines.
* `List`, `Prod`, and `PUnit` become Hectare's `List`, `Pair`, and `Unit`, as on
  the GHC side; another type constructor keeps its name, with each `.` replaced
  by `_`.
* A free variable of the query's context (a type parameter of the goal) becomes
  a constant type, named by the caller, so that Hectare treats it as rigid.
* An applied type variable (`m α`), a nested binder that is not explicit (a
  higher-rank type), a dependent function type inside a type, a universe, and a
  result that is a proposition or a universe give no Hectare type.

The erased types only propose candidates. Lean checks every candidate with its
real type, so an erased type that is too general or too specific costs time or
completeness, never soundness.
-/

namespace Oracle

open Lean Meta

/-- A first-order type of Hectare: a type variable, a function type, or a type
constructor with its arguments. -/
inductive HType where
  /-- A type variable, which Hectare instantiates at each use. -/
  | var (name : String)
  /-- A function type. -/
  | fn (argument result : HType)
  /-- A type constructor with its arguments. -/
  | con (name : String) (arguments : List HType)
  deriving BEq, Inhabited

/-- The type in the syntax of Hectare's `parseType`, fully parenthesized. -/
partial def HType.render : HType → String
  | .var name => name
  | .fn argument result => s!"({argument.render} -> {result.render})"
  | .con "List" [element] => s!"[{element.render}]"
  | .con "Pair" [first, second] => s!"({first.render}, {second.render})"
  | .con "Unit" [] => "()"
  | .con name [] => name
  | .con name arguments => "(" ++ " ".intercalate (name :: arguments.map HType.render) ++ ")"

/-- The result of a type after its function arguments. -/
def HType.result : HType → HType
  | .fn _ result => result.result
  | other => other

/-- The function arguments of a type. -/
def HType.parameters : HType → List HType
  | .fn argument result => argument :: result.parameters
  | _ => []

/-- The type variables of a type. -/
partial def HType.variables : HType → List String
  | .var name => [name]
  | .fn argument result => argument.variables ++ result.variables
  | .con _ arguments => arguments.flatMap HType.variables

/-- Whether the result of a type is a type variable that no parameter has, as in
`α` and `α → β`. With its class context erased, such a component (`default`,
`HAdd.hAdd`, `cast`) fits every hole, so the candidates that it makes flood the
search. -/
def HType.anyResult (t : HType) : Bool :=
  match t.result with
  | .var name => !(t.parameters.flatMap HType.variables).contains name
  | _ => false

/-- The name of a type constructor in Hectare: the special names of the GHC
side, or the Lean name with each `.` replaced by `_`, with a `@` in front when
it does not start with an uppercase letter. -/
def constructorName (name : Name) : String :=
  match name with
  | ``List => "List"
  | ``Prod => "Pair"
  | ``PUnit => "Unit"
  | _ =>
    let text := (name.toString (escape := false)).replace "." "_"
    if text.front.isUpper then text else "@" ++ text

/-- Whether an expression is a type, not a value or a proposition: its type is
`Type u` or `Sort (u + 1)`. -/
def isTypeArgument (e : Expr) : MetaM Bool := do
  match ← whnfR (← inferType e) with
  | .sort level => return !level.isAlwaysZero
  | _ => return false

/-- Whether an expression is a universe, as `Type u` or `Prop`. -/
def isUniverse (e : Expr) : MetaM Bool := do
  return (← whnfR e).isSort

/-- A Lean type as a Hectare type, or an explanation of why it has none. The
first map names the bound type variables, the second the rigid free variables
of the query's context. -/
partial def eraseType (bound rigid : FVarIdMap String) (t : Expr) : MetaM (Except String HType) := do
  let t ← whnfR t
  match t with
  | .fvar id =>
    match bound.get? id, rigid.get? id with
    | some name, _ => return .ok (.var name)
    | none, some name => return .ok (.con name [])
    | none, none => return .error "a free variable that is not a type variable"
  | .forallE _ domain body info =>
    if !info.isExplicit then return .error "a higher-rank type"
    if body.hasLooseBVars then return .error "a dependent function type inside a type"
    match ← eraseType bound rigid domain, ← eraseType bound rigid body with
    | .ok argument, .ok result => return .ok (.fn argument result)
    | .error e, _ | _, .error e => return .error e
  | .sort _ => return .error "a universe"
  | _ =>
    match t.getAppFn with
    | .const name _ =>
      let mut arguments := #[]
      for argument in t.getAppArgs do
        if ← isTypeArgument argument then
          match ← eraseType bound rigid argument with
          | .ok erased => arguments := arguments.push erased
          | .error e => return .error e
      return .ok (.con (constructorName name) arguments.toList)
    | .fvar _ => return .error "an applied type variable"
    | _ => return .error "an unsupported type"

/-- The Hectare type of a constant's type, or an explanation of why it has
none; see the module documentation for the rules. -/
def eraseConstantType (type : Expr) : MetaM (Except String HType) :=
  withReducible <| forallTelescopeReducing type fun xs body => do
    let mut bound : FVarIdMap String := {}
    let mut parameters := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if ← isUniverse decl.type then
        if decl.binderInfo.isExplicit then return .error "an explicit type argument"
        bound := bound.insert x.fvarId! s!"t{bound.size}"
      else if decl.binderInfo.isInstImplicit then
        continue
      else if ← isProp decl.type then
        return .error "a proof argument"
      else if decl.binderInfo.isExplicit then
        parameters := parameters.push decl.type
      -- An implicit value binder is dropped.
    if ← isProp body then return .error "a proposition"
    if ← isUniverse body then return .error "a type former"
    let mut erased := #[]
    for parameter in parameters do
      match ← eraseType bound {} parameter with
      | .ok argument => erased := erased.push argument
      | .error e => return .error e
    match ← eraseType bound {} body with
    | .ok result => return .ok (erased.foldr .fn result)
    | .error e => return .error e

end Oracle
