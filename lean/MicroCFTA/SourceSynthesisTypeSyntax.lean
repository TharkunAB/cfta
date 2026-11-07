import MicroCFTA.SourceEqualityConstraintOrigins

/-!
# Original synthesis types in the existing constructor syntax

The data and FirstOrder type constructors follow Gen.Synthesis. String
represents Text. Curried domains use finite entries here. This file does not
implement the native Map representation or curried type construction.
The supplied top guard is the source noConstraint value. The default type
universe retains its smart Mu binder. These laws concern original syntax.
They do not describe native construction or later intersections.
-/
namespace MicroCFTA.SourceSynthesisTypeSyntax
open InternedNestedConstruction (Syntax EdgeSyntax Scoped ManyScoped EdgesScoped)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)

/-- Source types retain variable names, arrows, and ordered constructor arguments. -/
inductive Ty where
  | tVar (name : String)
  | tFun (argument result : Ty)
  | tCons (name : String) (arguments : List Ty)

/-- Source domains distinguish defaultable heads from complete types. -/
inductive Domain where
  | headDomain (defaultable : Bool) (types : List Ty)
  | typeDomain (types : List Ty)

/-- Source defaulting retains all heads or the selected list default. -/
inductive Defaulting where
  | anyHead
  | onlyDefault

/-- Finite domain entries represent map data; native map lookup remains separate. -/
inductive Encoding where
  | firstOrder
  | curried (defaulting : Defaulting) (domains : List (String × Domain))

/-- Library fields retain source group, member, argument-only, and pruning order. -/
structure Library where
  libraryGroups : List (String × Ty × List String)
  libraryArgumentOnly : List (String × Ty)
  libraryAvoid : List (List String × Option (List String))
  libraryEncoding : Encoding

/-- A source query retains its ordered arguments and goal type. -/
structure Query where
  queryArguments : List (String × Ty)
  queryGoal : Ty

/-- Use the existing source constructor syntax, including lexical Mu references. -/
abbrev Expr (Guard : Type) := Syntax String Guard

/-- The first four source variables have fixed names; other names keep the prefix. -/
def variableSymbol : String → String
  | "a" => "var1"
  | "b" => "var2"
  | "c" => "var3"
  | "d" => "var4"
  | name => "var_" ++ name

private def variableOccurrences : Ty → List String
  | .tVar name => [name]
  | .tFun argument result => variableOccurrences argument ++ variableOccurrences result
  | .tCons _ arguments => arguments.flatMap variableOccurrences

/-- Keep each variable once, at its first occurrence, as source nubOrd does. -/
def typeVariables (typ : Ty) : List String := (variableOccurrences typ).eraseDups

/-- Source constructor discovery excludes every Fun name, independently of arity. -/
def constructorsOf : Ty → List (String × Nat)
  | .tVar _ => []
  | .tFun argument result => constructorsOf argument ++ constructorsOf result
  | .tCons name arguments =>
      (if name = "Fun" then [] else [(name, arguments.length)]) ++ arguments.flatMap constructorsOf

/-- The source arrow marker is an unconstrained leaf. -/
def arrowMarker (top : Guard) : Expr Guard := .node [.mk "(->)" top []]

/-- The source arrow has its marker before its argument and result types. -/
def arrowType (top : Guard) (argument result : Expr Guard) : Expr Guard :=
  .node [.mk "->" top [arrowMarker top, argument, result]]

/-- Encode a rigid source type; only Fun with exactly two arguments is an arrow. -/
def typeNode (top : Guard) : Ty → Expr Guard
  | .tVar name => .node [.mk (variableSymbol name) top []]
  | .tFun argument result => arrowType top (typeNode top argument) (typeNode top result)
  | .tCons name [argument, result] =>
      if name = "Fun" then arrowType top (typeNode top argument) (typeNode top result)
      else .node [.mk name top [typeNode top argument, typeNode top result]]
  | .tCons name arguments => .node [.mk name top (arguments.map (typeNode top))]

/-- Keep the source universe alternatives and recursive child positions in order. -/
def allTypesBody (top : Guard) (constructors : List (String × Nat)) : Expr Guard :=
  .union ([arrowType top (.var 0) (.var 0)] ++
    ["var1", "var2", "var3", "var4"].map (fun name => .node [.mk name top []]) ++
    constructors.map (fun (name, arity) => .node [.mk name top (List.replicate arity (.var 0))]))

/-- Source createMu applies cleanup, so the existing smart binder flag is true. -/
def allTypes (top : Guard) (constructors : List (String × Nat)) : Expr Guard :=
  .binder true (allTypesBody top constructors)

/-- A literal variable remains an ordinary rigid leaf. -/
theorem typeNode_tVar (top : Guard) (name : String) :
    typeNode top (.tVar name) = .node [.mk (variableSymbol name) top []] := by
  simp only [typeNode]

/-- A literal function uses the source marker and ordered type children. -/
theorem typeNode_tFun (top : Guard) (argument result : Ty) :
    typeNode top (.tFun argument result) = arrowType top (typeNode top argument) (typeNode top result) := by
  simp only [typeNode]

/-- The source Fun alias applies at exactly two arguments. -/
theorem typeNode_tCons_fun (top : Guard) (argument result : Ty) :
    typeNode top (.tCons "Fun" [argument, result]) =
      arrowType top (typeNode top argument) (typeNode top result) := by
  simp only [typeNode, ↓reduceIte]

mutual
/-- Test the absence of binders throughout the original constructor syntax. -/
def noBinders : Expr Guard → Bool
  | .empty | .var _ => true
  | .node rows => edgeNoBinders rows
  | .union children => childNoBinders children
  | .binder _ _ => false

private def childNoBinders : List (Expr Guard) → Bool
  | [] => true
  | first :: rest => noBinders first && childNoBinders rest

private def edgeNoBinders : List (EdgeSyntax String Guard) → Bool
  | [] => true
  | .mk _ _ children :: rest => childNoBinders children && edgeNoBinders rest
end

private def Rigid (top : Guard) (depth : Nat) (expression : Expr Guard) : Prop :=
  noBinders expression = true ∧ Scoped depth expression ∧
    ∀ guard ∈ guards expression, guard = top

private theorem childrenRigid (top : Guard) (depth : Nat) (children : List (Expr Guard))
    (checked : ∀ child ∈ children, Rigid top depth child) :
    childNoBinders children = true ∧ ManyScoped depth children ∧
      ∀ guard ∈ childGuards children, guard = top := by
  induction children with
  | nil => simp [childNoBinders, ManyScoped, childGuards]
  | cons first rest ih =>
      have own := checked first List.mem_cons_self
      have tail := ih (fun child member => checked child (List.mem_cons_of_mem _ member))
      refine ⟨by simp only [childNoBinders, own.1, tail.1, Bool.and_self],
        by simpa only [ManyScoped] using And.intro own.2.1 tail.2.1, ?_⟩
      intro guard member
      rcases List.mem_append.mp member with head | later
      · exact own.2.2 guard head
      · exact tail.2.2 guard later

private theorem nodeRigid (top : Guard) (depth : Nat) (name : String) (children : List (Expr Guard))
    (checked : ∀ child ∈ children, Rigid top depth child) :
    Rigid top depth (.node [.mk name top children]) := by
  obtain ⟨binders, scopeProof, annotations⟩ := childrenRigid top depth children checked
  refine ⟨?_, ?_, ?_⟩
  · simpa only [noBinders, edgeNoBinders, Bool.and_true] using binders
  · simpa only [Scoped, EdgesScoped, and_true] using scopeProof
  · intro guard member
    simp only [guards, edgeGuards, List.append_nil, List.mem_cons] at member
    rcases member with rfl | inherited
    · rfl
    · exact annotations guard inherited

private theorem arrowRigid (top : Guard) (depth : Nat) (argument result : Expr Guard)
    (first : Rigid top depth argument) (second : Rigid top depth result) :
    Rigid top depth (arrowType top argument result) := by
  have marker : Rigid top depth (arrowMarker top) := nodeRigid top depth "(->)" [] (by simp)
  exact nodeRigid top depth "->" _ (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using
    (show ∀ child, child = arrowMarker top ∨ child = argument ∨ child = result → Rigid top depth child from by
      intro child member
      rcases member with rfl | rfl | rfl
      · exact marker
      · exact first
      · exact second))

private theorem typeNodeRigid (top : Guard) (depth : Nat) (typ : Ty) :
    Rigid top depth (typeNode top typ) := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, Rigid top depth (typeNode top typ)) with
  | tVar name => simpa only [typeNode] using nodeRigid top depth (variableSymbol name) [] (by simp)
  | tFun argument result first second => simpa only [typeNode] using arrowRigid top depth _ _ first second
  | tCons name arguments children =>
      have ordinary : Rigid top depth (.node [.mk name top (arguments.map (typeNode top))]) := by
        apply nodeRigid top depth
        intro child member
        obtain ⟨typ, included, rfl⟩ := List.mem_map.mp member
        exact children typ included
      cases arguments with
      | nil => simpa only [typeNode] using ordinary
      | cons first rest =>
          cases rest with
          | nil => simpa only [typeNode] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [typeNode] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · subst name
                    simpa only [typeNode, ↓reduceIte] using
                      arrowRigid top depth _ _ (children first (by simp)) (children second (by simp))
                  · simpa only [typeNode, alias, ↓reduceIte, List.map_cons, List.map_nil] using ordinary
  | nil => rename_i typ member; cases member
  | cons typ types own rest =>
      rename_i other member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact rest other member

/-- Encoding a rigid source type introduces no binder. -/
theorem typeNode_noBinders (top : Guard) (typ : Ty) : noBinders (typeNode top typ) = true :=
  (typeNodeRigid top 0 typ).1

/-- Every literal typeNode guard is the supplied source top value. -/
theorem typeNode_guards (top : Guard) (typ : Ty) :
    ∀ guard ∈ guards (typeNode top typ), guard = top := (typeNodeRigid top 0 typ).2.2

/-- Rigid source types contain no lexical references at any depth. -/
theorem typeNode_scoped (top : Guard) (depth : Nat) (typ : Ty) : Scoped depth (typeNode top typ) :=
  (typeNodeRigid top depth typ).2.1

private theorem allTypesBodyRigid (top : Guard) (constructors : List (String × Nat))
    (depth : Nat) (positive : 0 < depth) : Rigid top depth (allTypesBody top constructors) := by
  have recursive : Rigid top depth (.var 0) :=
    ⟨rfl, by simpa only [Scoped] using positive, by simp [guards]⟩
  have alternatives : ∀ child ∈ ([arrowType top (.var 0) (.var 0)] ++
      ["var1", "var2", "var3", "var4"].map (fun name => Syntax.node [EdgeSyntax.mk name top []]) ++
      constructors.map (fun (name, arity) => Syntax.node [EdgeSyntax.mk name top (List.replicate arity (.var 0))])),
      Rigid top depth child := by
    intro child member
    rcases List.mem_append.mp member with earlier | constructor
    · rcases List.mem_append.mp earlier with first | rigidVariable
      · have same := List.mem_singleton.mp first
        subst child
        exact arrowRigid top depth _ _ recursive recursive
      · obtain ⟨name, _, rfl⟩ := List.mem_map.mp rigidVariable
        exact nodeRigid top depth name [] (by simp)
    · obtain ⟨⟨name, arity⟩, _, rfl⟩ := List.mem_map.mp constructor
      apply nodeRigid top depth name
      intro child member
      have same : child = .var 0 := List.eq_of_mem_replicate member
      subst child
      exact recursive
  obtain ⟨binders, scopeProof, annotations⟩ := childrenRigid top depth _ alternatives
  refine ⟨binders, ?_, annotations⟩
  simpa only [allTypesBody, Scoped] using scopeProof

/-- The source universe body introduces no nested binders. -/
theorem allTypesBody_noBinders (top : Guard) (constructors : List (String × Nat)) :
    noBinders (allTypesBody top constructors) = true := (allTypesBodyRigid top constructors 1 (by decide)).1

/-- Every source universe guard, including those below recursive references, is top. -/
theorem allTypesBody_guards (top : Guard) (constructors : List (String × Nat)) :
    ∀ guard ∈ guards (allTypesBody top constructors), guard = top :=
  (allTypesBodyRigid top constructors 1 (by decide)).2.2

/-- The universe body reads only the recursive lexical variable supplied by its binder. -/
theorem allTypesBody_scoped (top : Guard) (constructors : List (String × Nat)) :
    Scoped 1 (allTypesBody top constructors) := (allTypesBodyRigid top constructors 1 (by decide)).2.1

/-- The actual default universe is closed and retains its original smart binder. -/
theorem allTypes_scoped (top : Guard) (constructors : List (String × Nat)) :
    Scoped 0 (allTypes top constructors) := by
  simpa only [allTypes, Scoped] using allTypesBody_scoped top constructors

/-- Literal guards in the original recursive universe remain exactly top. -/
theorem allTypes_guards (top : Guard) (constructors : List (String × Nat)) :
    ∀ guard ∈ guards (allTypes top constructors), guard = top := allTypesBody_guards top constructors

end MicroCFTA.SourceSynthesisTypeSyntax
