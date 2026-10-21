import MicroCFTA.SourceRecursiveIntersectionCode

/-!
# Compile actual guarded source branches

The compiler retains the source guard order, physical effects, ordered union
and row calls, original binding reads, and optional-binder construction.
Recursive node and edge requests remain explicit instructions.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain

/-- A node request retains its domain and ordered original operands. -/
def requestNode (domain : Interned DomainKey) (left right : Value Symbol Guard) : Code Symbol Guard (Value Symbol Guard) :=
  .node ⟨domain, left, right⟩ .pure

/-- A row request retains its domain and ordered complete edge records. -/
def requestEdge (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) : Code Symbol Guard (EdgeValue Symbol Guard) :=
  .edge ⟨domain, left, right⟩ .pure

/-- Unsupported operands retain their original references. -/
def unsupported (left right : Value Symbol Guard) : Code Symbol Guard A :=
  .fail (.unsupported left.referenceOf right.referenceOf)

/-- Mu entry allocates the actual extended domain before requesting the two original bodies. -/
def compileMu (domain : Interned DomainKey) (left right : Value Symbol Guard) : Code Symbol Guard (Value Symbol Guard) :=
  match identity left, identity right with
  | some first, some second =>
      .enter domain left right first second fun entered =>
        .node ⟨entered, body left, body right⟩ fun value =>
          .optionalBinder (pair first second) value .pure
  | _, _ => unsupported left right

/-- Original free binding lookup precedes the next physical node request. -/
def compileReference (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool) :
    Code Symbol Guard (Value Symbol Guard) :=
  if name ∈ names domain.key then
    .read name fun found => match found with
      | some bound => if left then requestNode domain bound other else requestNode domain other bound
      | none => .fail (.missingPayload name)
  else .fail (.missingBinder name)

/-- Edge compilation checks arity before requesting any child. -/
def compileEdge (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : EdgeRequest Symbol Guard) :
    Code Symbol Guard (EdgeValue Symbol Guard) :=
  if request.left.children.length = request.right.children.length then
    (walk (fun children => requestNode request.domain children.1 children.2) (request.left.children.zip request.right.children)).bind fun values =>
      .work (makeEdge request.left.entry.key.symbol (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) values) .pure
  else .work (makeEdge request.left.entry.key.symbol emptyGuard [.empty]) .pure

/-- Node rows retain the actual hash-join order before canonical node construction. -/
def compileRows [DecidableEq Symbol] (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) :
    Code Symbol Guard (Value Symbol Guard) :=
  (walk (fun rows => requestEdge domain rows.1 rows.2) (pairs left right)).bind fun values => .work (makeNode values) .pure

/-- Compile the full physical source branch selector without evaluating recursive requests. -/
def compileNode [DecidableEq Symbol] (request : NodeRequest Symbol Guard) : Code Symbol Guard (Value Symbol Guard) :=
  let domain := request.domain
  let left := request.left
  let right := request.right
  match decision domain.key left right with
  | .empty => .pure .empty
  | .reset => requestNode IntersectionEmptyDomain.emptyDomain left right
  | .self => .pure left
  | .swap => requestNode domain right left
  | .repeated key => .pure (repeatedValue key)
  | .bothMu | .leftMu | .rightMu => compileMu domain left right
  | .leftUnion => match left with
    | .union _ members _ _ => (walk (fun member => requestNode domain member right) members).bind fun values => .work (makeUnion values) .pure
    | _ => unsupported left right
  | .rightUnion => match right with
    | .union _ members _ _ => (walk (fun member => requestNode domain left member) members).bind fun values => .work (makeUnion values) .pure
    | _ => unsupported left right
  | .leftReference => match left with
    | .reference (.interned name) => compileReference domain name right true
    | _ => unsupported left right
  | .rightReference => match right with
    | .reference (.interned name) => compileReference domain name left false
    | _ => unsupported left right
  | .ordinary => match left, right with
    | .node _ first _ _, .node _ second _ _ => compileRows domain first second
    | _, _ => unsupported left right
  | .unsupported => unsupported left right

/-- Returning the same value and cache is a right identity for source result sequencing. -/
theorem result_bind_pure (result : Result Symbol Guard A) : result.bind (fun value after => .done value after) = result := by
  cases result <;> rfl

/-- A compiled node request interprets to the actual node callback. -/
theorem interpret_requestNode [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes edges (requestNode domain left right) state = nodes ⟨domain, left, right⟩ state := by
  simp only [requestNode, interpret, result_bind_pure]

/-- A compiled edge request interprets to the actual edge callback. -/
theorem interpret_requestEdge [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes edges (requestEdge domain left right) state = edges ⟨domain, left, right⟩ state := by
  simp only [requestEdge, interpret, result_bind_pure]

/-- The complete node callback function agrees at every actual source cache. -/
theorem interpret_requestNode_fun [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) :
    interpret nodes edges (requestNode domain left right) = nodes ⟨domain, left, right⟩ :=
  funext (interpret_requestNode nodes edges domain left right)

/-- The complete edge callback function agrees at every actual source cache. -/
theorem interpret_requestEdge_fun [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) :
    interpret nodes edges (requestEdge domain left right) = edges ⟨domain, left, right⟩ :=
  funext (interpret_requestEdge nodes edges domain left right)

/-- Compiled Mu entry has the exact original domain and optional-binder effects. -/
theorem compileMu_exact [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes edges (compileMu domain left right) state =
      mu (fun domain left right => nodes ⟨domain, left, right⟩) domain left right state := by
  cases first : identity left <;> cases second : identity right <;>
    simp only [compileMu, mu, first, second, unsupported, SourceRecursiveIntersectionKernel.unsupported, interpret, result_bind_pure]

/-- Compiled original binding reads have the exact source request or failure. -/
theorem compileReference_exact [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) :
    interpret nodes edges (compileReference domain name other left) state =
      reference (fun domain left right => nodes ⟨domain, left, right⟩) domain name other left state := by
  cases left <;> by_cases member : name ∈ names domain.key <;> cases found : SourcePreparedSharedRows.read state.heap name <;>
    simp [compileReference, reference, member, found, interpret, interpret_requestNode]

/-- Compiled child requests and edge construction equal the actual guarded source edge worker. -/
theorem compileEdge_exact [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes edges (compileEdge emptyGuard conjoin request) state =
      SourceRecursiveIntersectionKernel.edge emptyGuard conjoin (fun left right => nodes ⟨request.domain, left, right⟩) request.left request.right state := by
  by_cases arity : request.left.children.length = request.right.children.length <;>
    simp only [compileEdge, SourceRecursiveIntersectionKernel.edge, arity, ite_true, ite_false,
      interpret_bind, interpret_walk, interpret_requestNode_fun, interpret, result_bind_pure]

/-- Compiled physical rows equal the source row walk with its actual edge callback. -/
theorem compileRows_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) :
    interpret nodes (fun request => SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (fun left right => nodes ⟨request.domain, left, right⟩) request.left request.right) (compileRows domain left right) state =
      SourceRecursiveIntersectionKernel.node emptyGuard conjoin (fun left right => nodes ⟨domain, left, right⟩) left right state := by
  simp only [compileRows, SourceRecursiveIntersectionKernel.node, interpret_bind, interpret_walk, interpret_requestEdge_fun, interpret, result_bind_pure]

/-- Every compiled physical source branch agrees with the existing full guarded kernel. -/
theorem compileNode_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes (fun request => SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (fun left right => nodes ⟨request.domain, left, right⟩) request.left request.right) (compileNode request) state =
      onNode emptyGuard conjoin (fun domain left right => nodes ⟨domain, left, right⟩) request.domain request.left request.right state := by
  cases selected : decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | bothMu | leftMu | rightMu | unsupported =>
    simp only [compileNode, onNode, selected, interpret, interpret_requestNode, compileMu_exact, unsupported,
      SourceRecursiveIntersectionKernel.unsupported]
  | leftUnion =>
    simp only [compileNode, onNode, selected]
    cases request.left <;> simp only [unsupported, SourceRecursiveIntersectionKernel.unsupported,
      interpret_bind, interpret_walk, interpret_requestNode_fun, interpret, result_bind_pure]
  | rightUnion =>
    simp only [compileNode, onNode, selected]
    cases request.right <;> simp only [unsupported, SourceRecursiveIntersectionKernel.unsupported,
      interpret_bind, interpret_walk, interpret_requestNode_fun, interpret, result_bind_pure]
  | leftReference =>
    simp only [compileNode, onNode, selected]
    cases request.left <;> try rfl
    rename_i name
    cases name <;> simp only [unsupported, SourceRecursiveIntersectionKernel.unsupported, interpret, compileReference_exact]
  | rightReference =>
    simp only [compileNode, onNode, selected]
    cases request.right <;> try rfl
    rename_i name
    cases name <;> simp only [unsupported, SourceRecursiveIntersectionKernel.unsupported, interpret, compileReference_exact]
  | ordinary =>
    simp only [compileNode, onNode, selected]
    cases request.left <;> cases request.right <;>
      simp only [unsupported, SourceRecursiveIntersectionKernel.unsupported, interpret, compileRows_exact]

end MicroCFTA.SourceRecursiveIntersectionCode
