import MicroCFTA.Fragments
import MicroCFTA.EqualityTrie

/-!
# Suspended-constraint enumeration state machine

The transitions follow `Enumeration.hs`. Graph identity, intersection, and
recursive unfolding are explicit interfaces. Execution bounds report errors;
they do not silently reject branches. Residual guards remain in the output.
-/
set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationState
open Language Fragments

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The existing checked path-trie model supplies suspended equality variables. -/
abbrev Suspended := EqualityTrie.Suspended Nat

/-- Use the source-equivalent checked trie descent. -/
abbrev descendScs := @EqualityTrie.descendScs Nat

/-- Every represented path must reach the assigned equality variable. -/
def Suspended.Holds (assignment : Nat → Term Symbol) (term : Term Symbol) (sc : Suspended) : Prop :=
  ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, term.atPath path = some (assignment sc.var)

/-- Source UVar states. A missing node is a pure equality variable. -/
inductive UVarValue (Symbol : Type) where
  | unenumerated : Option Nat → List Suspended → UVarValue Symbol
  | enumerated : Fragment Symbol → UVarValue Symbol
  | eliminated

/-- One graph edge and its two kinds of constraints. -/
structure Edge (Symbol Guard : Type) where
  symbol : Symbol
  children : List Nat
  equalities : List EqualityTrie.Trie
  residual : Option Guard

/-- The recursive case supplies the unfolded outer body. -/
inductive Node (Symbol Guard : Type) where
  | empty
  | alternatives : List (Edge Symbol Guard) → Node Symbol Guard
  | recursive : Nat → Node Symbol Guard
  | unresolved : Nat → Node Symbol Guard

/-- Graph primitives supplied by the interned-graph implementation. -/
structure Graph (Symbol Guard : Type) where
  node : Nat → Node Symbol Guard
  intersect : Nat → Nat → Nat

/-- Recursion keys omit equality-variable identities. -/
structure RecursionKey where
  node : Nat
  tries : List (List (List Nat))
  deriving DecidableEq

/-- Canonical path sets represent the source's set of suspended tries. -/
def recursionKey (node : Nat) (scs : List Suspended) : RecursionKey :=
  ⟨node, (scs.map fun sc => EqualityTrie.fromPathTrie sc.trie).eraseDups.mergeSort
    (fun left right => compare left right != .gt)⟩

/-- Mutable state copied separately for each nondeterministic branch. -/
structure State (Symbol Guard : Type) where
  counter : Nat
  representatives : UnionFind.Forest
  values : List (UVarValue Symbol)
  obligations : List (Guard × Fragment Symbol)
  recursionAncestry : Nat → List RecursionKey
  expansionAncestry : List RecursionKey

/-- The root starts in UVar zero. -/
def initial (root : Nat) : State Symbol Guard :=
  ⟨1, UnionFind.withInitialValues [0], [.unenumerated (some root) []], [], fun _ => [], []⟩

/-- Source invariant failures and explicit finite execution bounds. -/
inductive Error where
  | fuelExhausted | representativeFuel | invalidSlot | invalidIntersection
  | unresolvedReference | unfinishedFragment
  deriving DecidableEq, Repr

/-- State and errors are local to each nondeterministic alternative. -/
abbrev EnumerateM (Symbol Guard : Type) := StateT (State Symbol Guard) (ExceptT Error List)

/-- Reject one branch, as the list monad does. -/
def reject : EnumerateM Symbol Guard α := fun _ => []

/-- Choose each alternative with the same input state. -/
def choose (values : List α) : EnumerateM Symbol Guard α := fun state =>
  values.map fun value => .ok (value, state)

/-- Report an execution limit or source invariant failure. -/
def failure (error : Error) : EnumerateM Symbol Guard α := fun _ => [.error error]

/-- Retain a branch exactly when its Boolean guard is true. -/
def require (condition : Bool) : EnumerateM Symbol Guard Unit :=
  if condition then pure () else reject

/-- Write the supplied UVar, not its representative. -/
def setValue (uv : Nat) (value : UVarValue Symbol) : EnumerateM Symbol Guard Unit :=
  modify fun state => {state with values := state.values.set uv value}

/-- Read one raw slot. -/
def rawValue (uv : Nat) : EnumerateM Symbol Guard (UVarValue Symbol) := do
  match (← get).values[uv]? with
  | none => failure .invalidSlot
  | some value => pure value

/-- Find and path-compress a representative. -/
def representative (fuel uv : Nat) : EnumerateM Symbol Guard Nat := do
  let state ← get
  match UnionFind.findRoot fuel state.representatives uv with
  | none => failure .representativeFuel
  | some found =>
      set {state with representatives := found.forest}
      pure found.representative

/-- Read the current representative's slot. -/
def getValue (fuel uv : Nat) : EnumerateM Symbol Guard (UVarValue Symbol) := do
  rawValue (← representative fuel uv)

/-- Give a variable the ancestry of the current expansion. -/
def inheritAncestry (uv : Nat) : EnumerateM Symbol Guard Unit :=
  modify fun state => {state with recursionAncestry := (fun other =>
    if other = uv then (state.expansionAncestry ++ state.recursionAncestry uv).eraseDups
    else state.recursionAncestry other)}

/-- Allocate a slot and inherit the current recursion ancestry. -/
def allocate (node : Option Nat) : EnumerateM Symbol Guard Nat := do
  let state ← get
  let uv := state.counter
  set {state with counter := uv + 1, values := state.values ++ [UVarValue.unenumerated node []]}
  inheritAncestry uv
  pure uv

/-- A new equality class starts with a pure equality variable. -/
def suspend (trie : EqualityTrie.Trie) : EnumerateM Symbol Guard Suspended := do
  pure ⟨trie, ← allocate none⟩

/-- Only two unenumerated slots can be intersected. -/
def intersectValues (graph : Graph Symbol Guard) :
    UVarValue Symbol → UVarValue Symbol → Option (UVarValue Symbol)
  | .unenumerated left ls, .unenumerated right rs =>
      some (.unenumerated (match left, right with
        | none, node => node
        | node, none => node
        | some a, some b => some (graph.intersect a b)) (ls ++ rs))
  | _, _ => none

/-- Structural emptiness rejects an intersection branch. -/
def hasEmptyContents (graph : Graph Symbol Guard) : UVarValue Symbol → Bool
  | .unenumerated (some node) _ => match graph.node node with | .empty => true | _ => false
  | _ => false

/-- Move an old representative's contents into the current representative. -/
def assimilate (graph : Graph Symbol Guard) (target source : Nat) : EnumerateM Symbol Guard Unit := do
  if target = source then pure () else
    let sourceValue ← rawValue source
    match sourceValue with
    | .eliminated => pure ()
    | _ =>
        let targetValue ← rawValue target
        match intersectValues graph sourceValue targetValue with
        | none => failure .invalidIntersection
        | some merged =>
            require (!hasEmptyContents graph merged)
            setValue target merged
            setValue source .eliminated
            modify fun state => {state with recursionAncestry := (fun other =>
              if other = target then
                (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
              else state.recursionAncestry other)}

/-- Add a reached node and its inherited suspended constraints. -/
def mergeNode (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    EnumerateM Symbol Guard Unit := do
  let root ← representative fuel uv
  let previous ← rawValue root
  match intersectValues graph (.unenumerated (some node) scs) previous with
  | none => failure .invalidIntersection
  | some merged =>
      setValue root merged
      inheritAncestry root
      require (!hasEmptyContents graph merged)

/-- Union equality variables before value-slot assimilation. -/
def unionVariables (fuel left right : Nat) : EnumerateM Symbol Guard Unit := do
  let state ← get
  match UnionFind.union fuel fuel state.representatives left right with
  | none => failure .representativeFuel
  | some forest => set {state with representatives := forest}

/-- Every suspended nonempty path starts at an available child. -/
def arityAllows (arity : Nat) (scs : List Suspended) : Bool :=
  scs.all fun sc => (EqualityTrie.fromPathTrie sc.trie).all fun path =>
    match path with | [] => true | child :: _ => decide (child < arity)

mutual
  /-- Enumerate a node or merge the equality variables reached at its root. -/
  def enumerateNode (graph : Graph Symbol Guard) : Nat → List Suspended → Nat →
      EnumerateM Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, node => do
        match graph.node node with
        | .empty => reject
        | view =>
          let here := scs.filter fun sc => EqualityTrie.isTerminal sc.trie
          let below := scs.filter fun sc => !EqualityTrie.isTerminal sc.trie
          match here with
          | [] =>
            match view with
            | .empty => reject
            | .recursive _ => pure (.hole (← allocate (some node)))
            | .alternatives edges => enumerateEdge graph fuel scs (← choose edges)
            | .unresolved _ => failure .unresolvedReference
          | first :: rest =>
            let roots ← here.mapM fun sc => representative (fuel + 1) sc.var
            rest.forM fun sc => unionVariables (fuel + 1) first.var sc.var
            let root ← representative (fuel + 1) first.var
            roots.forM (assimilate graph root)
            mergeNode graph (fuel + 1) root node below
            pure (.hole root)

  /-- Descend edge constraints and retain its residual guard for the caller. -/
  def enumerateEdge (graph : Graph Symbol Guard) : Nat → List Suspended → Edge Symbol Guard →
      EnumerateM Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, edge => do
        require (arityAllows edge.children.length scs)
        let added ← edge.equalities.mapM suspend
        let children ← edge.children.zipIdx |>.mapM fun (node, index) =>
          enumerateNode graph fuel (descendScs index (scs ++ added)) node
        let fragment := Fragment.node edge.symbol children
        match edge.residual with
        | none => pure ()
        | some guard => modify fun state => {state with obligations := (guard, fragment) :: state.obligations}
        pure fragment
end

/-- Slots that can initiate work, before suspended dependencies are removed. -/
def candidate (graph : Graph Symbol Guard) : UVarValue Symbol → Bool
  | .unenumerated (some node) scs =>
      match graph.node node with | .recursive _ => !scs.isEmpty | _ => true
  | _ => false

/-- Scan live slots and resolve the suspended variables that block expansion. -/
def findExpandable (graph : Graph Symbol Guard) (fuel : Nat) :
    EnumerateM Symbol Guard (Option (List Nat)) := do
  let values := (← get).values
  let (candidates, blocked) ← values.zipIdx.foldlM
    (fun (candidates, blocked) (value, index) => do
      match value with
      | .unenumerated _ scs =>
          let blocked ← scs.foldlM (fun blocked sc => do
            pure ((← representative fuel sc.var) :: blocked)) blocked
          pure (if candidate graph value then candidates ++ [index] else candidates, blocked)
      | _ => pure (candidates, blocked)) ([], [])
  if candidates.isEmpty then pure none
  else pure (some (candidates.filter fun uv => !(uv ∈ blocked)))

/-- No work, blocked work, or the next dependency-safe variable. -/
inductive Next where
  | done | stuck | expand (uv : Nat)
  deriving DecidableEq, Repr

/-- An invalid ordering hint falls back to the first available variable. -/
def pickNext (preference : List Nat → Option Nat) : Option (List Nat) → Next
  | none => .done
  | some [] => .stuck
  | some (first :: rest) =>
      match preference (first :: rest) with
      | some preferred => if preferred ∈ first :: rest then .expand preferred else .expand first
      | none => .expand first

/-- Expand one selected UVar and store its fragment. -/
def enumerateOut (graph : Graph Symbol Guard) (fuel uv : Nat) :
    EnumerateM Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) uv with
  | .unenumerated (some node) scs =>
      let root ← representative (fuel + 1) uv
      let ancestry := (← get).recursionAncestry root
      modify fun state => {state with expansionAncestry := (
        match graph.node node with
        | .recursive _ => (recursionKey node scs :: ancestry).eraseDups
        | _ => ancestry)}
      let fragment ← enumerateNode graph fuel scs
        (match graph.node node with | .recursive body => body | _ => node)
      modify fun state => {state with expansionAncestry := []}
      setValue root (.enumerated fragment)
      pure fragment
  | _ => reject

/-- The callback sees either the selected graph node or its completed fragment. -/
abbrev Oracle (Symbol Guard OracleState : Type) := OracleState → Nat →
  Sum (Fragment Symbol) Nat → EnumerateM Symbol Guard (Bool × OracleState)

/-- The complete caller loop, including pruning and repeated-recursion truncation. -/
def enumerateFully (graph : Graph Symbol Guard) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) : Nat → OracleState → EnumerateM Symbol Guard Unit
  | 0, _ => failure .fuelExhausted
  | fuel + 1, oracleState => do
      let next := pickNext (order oracleState) (← findExpandable graph (fuel + 1))
      match next with
      | .done => pure ()
      | .stuck => reject
      | .expand uv =>
          match ← getValue (fuel + 1) uv with
          | .unenumerated (some node) scs =>
              let repeated ← match graph.node node with
                | .recursive _ => do
                    let root ← representative (fuel + 1) uv
                    let current : State Symbol Guard ← get
                    if recursionKey node scs ∈ current.recursionAncestry root then
                      setValue root (.unenumerated (some node) [])
                      pure true
                    else pure false
                | _ => pure false
              if repeated then enumerateFully graph order oracle fuel oracleState
              else
                let (beforeReject, beforeState) ← oracle oracleState uv (.inr node)
                require (!beforeReject)
                let fragment ← enumerateOut graph (fuel + 1) uv
                let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                require (!afterReject)
                enumerateFully graph order oracle fuel afterState
          | _ => reject

/-- The ordinary public enumerator does not apply an oracle predicate. -/
def noPruning : Oracle Symbol Guard Unit := fun state _ _ => pure (false, state)

/-- Keep real symbols, unresolved holes, and recursion truncation distinct. -/
inductive PartialSymbol (Symbol : Type) where
  | concrete : Symbol → PartialSymbol Symbol
  | hole : Nat → PartialSymbol Symbol
  | truncated
  deriving DecidableEq, Repr

/-- Diagnostic rendering distinguishes pending recursive constraints from final truncation. -/
def expandPartial (graph : Graph Symbol Guard) : Nat → Fragment Symbol →
    EnumerateM Symbol Guard (Term (PartialSymbol Symbol))
  | 0, _ => failure .fuelExhausted
  | fuel + 1, .node symbol children => do
      pure (.node (.concrete symbol) (← children.mapM (expandPartial graph fuel)))
  | fuel + 1, .hole uv => do
      match ← getValue (fuel + 1) uv with
      | .enumerated fragment => expandPartial graph fuel fragment
      | .unenumerated (some node) [] =>
          match graph.node node with
          | .recursive _ => pure (.node .truncated [])
          | _ => pure (.node (.hole uv) [])
      | _ => pure (.node (.hole uv) [])

/-- Concrete rendering uses the caller's marker for any unexpanded recursive node. -/
def expandFragment (graph : Graph Symbol Guard) (marker : Symbol) : Nat → Fragment Symbol →
    EnumerateM Symbol Guard (Term Symbol)
  | 0, _ => failure .fuelExhausted
  | fuel + 1, .node symbol children => do
      pure (.node symbol (← children.mapM (expandFragment graph marker fuel)))
  | fuel + 1, .hole uv => do
      match ← getValue (fuel + 1) uv with
      | .enumerated fragment => expandFragment graph marker fuel fragment
      | .unenumerated (some node) _ =>
          match graph.node node with
          | .recursive _ => pure (.node marker [])
          | _ => failure .unfinishedFragment
      | _ => failure .unfinishedFragment

/-- Read a completed variable. A nonrecursive unfinished root rejects the branch. -/
def expandUVar (graph : Graph Symbol Guard) (marker : Symbol) (fuel uv : Nat) :
    EnumerateM Symbol Guard (Term Symbol) := do
  match ← getValue (fuel + 1) uv with
  | .enumerated fragment => expandFragment graph marker fuel fragment
  | .unenumerated (some node) _ =>
      match graph.node node with
      | .recursive _ => pure (.node marker [])
      | _ => reject
  | _ => reject

/-- One run keeps every residual constraint paired with its rendered guarded subtree. -/
def runs (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    List (Except Error ((Term Symbol × List (Guard × Term Symbol)) × State Symbol Guard)) :=
  let action : EnumerateM Symbol Guard (Term Symbol × List (Guard × Term Symbol)) := do
    enumerateFully graph (fun _ _ => none) noPruning fuel ()
    let term ← expandUVar graph marker fuel 0
    let pending ← (← get).obligations.mapM fun (guard, fragment) => do
      pure (guard, ← expandFragment graph marker fuel fragment)
    pure (term, pending)
  action (initial root)

/-- The arity check is exactly the first-index requirement of every suspended path. -/
theorem arityAllows_correct (arity : Nat) (scs : List Suspended) :
    arityAllows arity scs = true ↔
      ∀ sc ∈ scs, ∀ index suffix,
        index :: suffix ∈ EqualityTrie.fromPathTrie sc.trie → index < arity := by
  simp only [arityAllows, List.all_eq_true]
  constructor
  · intro bound sc member index suffix path
    simpa using bound sc member (index :: suffix) path
  · intro bound sc member path present
    cases path with
    | nil => rfl
    | cons index suffix => simpa using bound sc member index suffix present

/-- Source maximum-index checks and the executable arity predicate agree on valid tries. -/
theorem arityAllows_maximum (arity : Nat) (scs : List Suspended)
    (valid : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie) :
    arityAllows arity scs = true ↔
      ∀ sc ∈ scs, (EqualityTrie.getMaxNonemptyIndex sc.trie).all (· < arity) = true := by
  rw [arityAllows_correct]
  constructor
  · intro bounds sc member
    exact (EqualityTrie.arity_exact sc.trie (valid sc member) arity).mpr (bounds sc member)
  · intro bounds sc member
    exact (EqualityTrie.arity_exact sc.trie (valid sc member) arity).mp (bounds sc member)

/-- An ordering hint can select only a variable offered by the scheduler. -/
theorem pickNext_safe (preference : List Nat → Option Nat) (offered : List Nat) (uv : Nat)
    (selected : pickNext preference (some offered) = .expand uv) : uv ∈ offered := by
  cases offered with
  | nil => cases selected
  | cons first rest =>
      unfold pickNext at selected
      cases choice : preference (first :: rest) with
      | none => simp [choice] at selected; subst uv; simp
      | some wanted =>
          by_cases present : wanted ∈ first :: rest
          · simp [choice, present] at selected
            subst uv
            exact present
          · simp [choice, present] at selected
            subst uv
            simp

/-- A stopped recursive variable never enters the candidate set. -/
theorem unconstrained_recursive_not_candidate (graph : Graph Symbol Guard) (node body : Nat)
    (recursive : graph.node node = .recursive body) :
    candidate graph (.unenumerated (some node) []) = false := by
  simp [candidate, recursive]

/-- Pure equality variables and eliminated slots cannot initiate expansion. -/
theorem constraint_only_not_candidate (graph : Graph Symbol Guard) (scs : List Suspended) :
    candidate graph (.unenumerated none scs) = false ∧ candidate graph .eliminated = false := by
  constructor <;> rfl

/-- An execution bound is distinct from a rejected nondeterministic branch. -/
theorem bound_is_not_empty (graph : Graph Symbol Guard) (scs : List Suspended)
    (node : Nat) (state : State Symbol Guard) :
    enumerateNode graph 0 scs node state = [.error .fuelExhausted] := rfl

/-- A terminal suspended trie requires equality with the current complete term. -/
theorem terminal_requirement (assignment : Nat → Term Symbol) (term : Term Symbol) (uv : Nat) :
    Suspended.Holds assignment term ⟨.terminal, uv⟩ ↔ term = assignment uv := by
  simp [Suspended.Holds, EqualityTrie.fromPathTrie, Term.atPath]

/-- Descent preserves every inherited suspended equality at an existing child. -/
theorem suspended_descent_sound (assignment : Nat → Term Symbol)
    (symbol : Symbol) (children : List (Term Symbol)) (scs : List Suspended)
    (valid : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie)
    (holds : ∀ sc ∈ scs, Suspended.Holds assignment (.node symbol children) sc)
    (index : Nat) (child : Term Symbol) (found : children[index]? = some child) :
    ∀ sc ∈ descendScs index scs, Suspended.Holds assignment child sc := by
  intro sc member suffix present
  obtain ⟨original, originalMember, same, path⟩ :=
    (EqualityTrie.descendScs_exact index scs valid sc.var suffix).mp ⟨sc, member, rfl, present⟩
  have equality := holds original originalMember (index :: suffix) path
  simpa [Term.atPath, found, same] using equality

/-- Valid inherited equalities cannot be rejected by the edge's arity check. -/
theorem suspended_arity_necessary (assignment : Nat → Term Symbol)
    (symbol : Symbol) (children : List (Term Symbol)) (scs : List Suspended)
    (holds : ∀ sc ∈ scs, Suspended.Holds assignment (.node symbol children) sc) :
    arityAllows children.length scs = true := by
  apply arityAllows_correct _ _ |>.mpr
  intro sc member index suffix path
  have equality := holds sc member (index :: suffix) path
  obtain ⟨child, found, _⟩ := Option.bind_eq_some_iff.mp equality
  exact (List.getElem?_eq_some_iff.mp found).1

/-- Arity, root equalities, and all descended obligations reconstruct every original obligation. -/
theorem suspended_descent_complete (assignment : Nat → Term Symbol)
    (symbol : Symbol) (children : List (Term Symbol)) (scs : List Suspended)
    (valid : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie)
    (arity : arityAllows children.length scs = true)
    (roots : ∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = true →
      Term.node symbol children = assignment sc.var)
    (descendants : ∀ index child, children[index]? = some child →
      ∀ sc ∈ descendScs index scs, Suspended.Holds assignment child sc) :
    ∀ sc ∈ scs, Suspended.Holds assignment (.node symbol children) sc := by
  intro sc member path present
  cases path with
  | nil =>
      have terminal := (EqualityTrie.nil_mem sc.trie).mp present
      simpa [Term.atPath] using congrArg some
        (roots sc member (by simp [terminal, EqualityTrie.isTerminal]))
  | cons index suffix =>
      have bound := (arityAllows_correct _ _).mp arity sc member index suffix present
      have found : children[index]? = some children[index] := List.getElem?_eq_getElem bound
      obtain ⟨descended, descendedMember, same, suffixMember⟩ :=
        (EqualityTrie.descendScs_exact index scs valid sc.var suffix).mpr
          ⟨sc, member, rfl, present⟩
      have suffixEquality := descendants index children[index] found descended descendedMember suffix suffixMember
      simpa [Term.atPath, found, same] using suffixEquality

/-- Suspended constraints are preserved exactly by root discharge and child descent. -/
theorem suspended_decomposition (assignment : Nat → Term Symbol)
    (symbol : Symbol) (children : List (Term Symbol)) (scs : List Suspended)
    (valid : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie) :
    (∀ sc ∈ scs, Suspended.Holds assignment (.node symbol children) sc) ↔
      arityAllows children.length scs = true ∧
      (∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = true →
        Term.node symbol children = assignment sc.var) ∧
      (∀ index child, children[index]? = some child →
        ∀ sc ∈ descendScs index scs, Suspended.Holds assignment child sc) := by
  constructor
  · intro holds
    refine ⟨suspended_arity_necessary assignment symbol children scs holds, ?_,
      suspended_descent_sound assignment symbol children scs valid holds⟩
    intro sc member terminal
    have trie : sc.trie = .terminal := by
      cases h : sc.trie <;> simp [EqualityTrie.isTerminal, h] at terminal ⊢
    have equality := holds sc member [] (by simp [trie, EqualityTrie.fromPathTrie])
    exact Option.some.inj equality
  · rintro ⟨arity, roots, descendants⟩
    exact suspended_descent_complete assignment symbol children scs valid arity roots descendants

/-- Every nonempty finite list has a member with greatest assigned height. -/
theorem finite_height_maximum (variables : List Nat) (height : Nat → Nat)
    (nonempty : variables ≠ []) :
    ∃ largest ∈ variables, ∀ uv ∈ variables, height uv ≤ height largest := by
  induction variables with
  | nil => contradiction
  | cons first rest ih =>
      by_cases empty : rest = []
      · subst rest
        exact ⟨first, by simp, by simp⟩
      · obtain ⟨largest, member, maximal⟩ := ih empty
        by_cases bigger : height first ≤ height largest
        · refine ⟨largest, by simp [member], ?_⟩
          intro uv present
          rcases List.mem_cons.mp present with same | present
          · simpa [same] using bigger
          · exact maximal uv present
        · refine ⟨first, by simp, ?_⟩
          intro uv present
          rcases List.mem_cons.mp present with same | present
          · simp [same]
          · exact Nat.le_trans (maximal uv present) (by omega)

/-- A finite nonempty set cannot consist only of strict subtree dependencies.
The scheduler's stuck case needs its reachable-slot invariants to establish these dependencies. -/
theorem strict_dependency_stuck_impossible (variables : List Nat) (nonempty : variables ≠ [])
    (assignment : Nat → Term Symbol)
    (blocked : ∀ target ∈ variables, ∃ source ∈ variables,
      ∃ path, path ≠ [] ∧ (assignment source).atPath path = some (assignment target)) : False := by
  obtain ⟨largest, member, maximal⟩ :=
    finite_height_maximum variables (fun uv => (assignment uv).height) nonempty
  obtain ⟨source, sourceMember, path, proper, reaches⟩ := blocked largest member
  have bound := atPath_height_bound _ _ path reaches
  have largestHeight := maximal source sourceMember
  have positive : 0 < path.length := by
    have nonzero : path.length ≠ 0 := fun zero => proper (List.length_eq_zero_iff.mp zero)
    omega
  omega

/-- The concrete state update performed by allocation. -/
def allocated (node : Option Nat) (state : State Symbol Guard) : State Symbol Guard :=
  {state with
    counter := state.counter + 1
    values := state.values ++ [UVarValue.unenumerated node []]
    recursionAncestry := (fun other =>
      if other = state.counter then (state.expansionAncestry ++ state.recursionAncestry state.counter).eraseDups
      else state.recursionAncestry other)}

/-- Allocation has exactly one result and retains all old value slots. -/
theorem allocate_exact (node : Option Nat) (state : State Symbol Guard) :
    allocate node state = [.ok (state.counter, allocated node state)] := rfl

/-- The fresh-name supply remains equal to the slot count after allocation. -/
theorem allocated_supply (node : Option Nat) (state : State Symbol Guard)
    (aligned : state.counter = state.values.length) :
    (allocated node state).counter = (allocated node state).values.length := by
  simp [allocated, aligned]

/-- The newly allocated UVar names precisely the appended unenumerated slot. -/
theorem allocated_slot (node : Option Nat) (state : State Symbol Guard)
    (aligned : state.counter = state.values.length) :
    (allocated node state).values[state.counter]? = some (.unenumerated node []) := by
  simp [allocated, aligned]

/-- View the output values and retain any operational error. -/
def results (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    List (Except Error (Term Symbol × List (Guard × Term Symbol))) :=
  (runs graph marker fuel root).map (Except.map Prod.fst)

/-- An ordinary leaf with a residual Boolean guard. The enumerator does not decide it. -/
def residualLeaf : Graph Nat Bool :=
  ⟨fun _ => .alternatives [⟨7, [], [], some false⟩], fun left _ => left⟩

/-- The full driver returns a false residual guard unchanged with its complete subterm. -/
theorem residual_is_retained :
    results residualLeaf 99 8 0 = [.ok (.node 7 [], [(false, .node 7 [])])] := by
  rfl

/-- The graph for a recursive constructor with no base alternative. -/
def endlessGraph : Graph Nat Bool :=
  ⟨fun node => if node = 0 then .recursive 1 else .alternatives [⟨0, [0], [], none⟩],
    fun left _ => left⟩

/-- The full driver returns its recursion marker without unfolding an unconstrained binder. -/
theorem unconstrained_recursion_truncates :
    results endlessGraph 99 4 0 = [.ok (.node 99 [], [])] := by
  rfl

/-- The ordinary finite-term semantics of the recursive constructor. -/
def endlessLanguage : Automaton Unit Nat := fun _ => [⟨0, [()], fun _ => true⟩]

/-- The recursive constructor has no finite terms at any height. -/
theorem endless_enumeration_empty (fuel : Nat) : enumerate endlessLanguage fuel () = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [enumerate, endlessLanguage, products, ih]

/-- A recursion marker from `runs` does not prove that its represented language is nonempty. -/
theorem recursion_marker_not_acceptance :
    results endlessGraph 99 4 0 = [.ok (.node 99 [], [])] ∧
      ∀ term, ¬ Accepts endlessLanguage () term := by
  refine ⟨unconstrained_recursion_truncates, ?_⟩
  intro term accepted
  obtain ⟨fuel, member⟩ := enumerate_complete endlessLanguage accepted
  rw [endless_enumeration_empty] at member
  cases member

/-- One nonterminal suspended path. -/
def pendingPath : Suspended := ⟨.branch [(0, .terminal)], 1⟩

/-- A repeated recursion state has the same node and trie key in its ancestry. -/
def repeatedState : State Nat Bool :=
  {initial 0 with
    counter := 2
    values := [.unenumerated (some 0) [pendingPath], .unenumerated none []]
    recursionAncestry := (fun uv => if uv = 0 then [recursionKey 0 [pendingPath]] else [])}

/-- Render the root after the source caller loop has finished. -/
def finishRoot (graph : Graph Symbol Guard) (marker : Symbol) (fuel : Nat) :
    EnumerateM Symbol Guard (Term Symbol) := do
  enumerateFully graph (fun _ _ => none) noPruning fuel ()
  expandUVar graph marker fuel 0

/-- The repeated-recursion branch clears pending constraints before it returns a marker. -/
theorem repeated_recursion_clears_constraints :
    List.map (Except.map Prod.fst) (finishRoot endlessGraph 99 6 repeatedState) = [.ok (.node 99 [])] := by
  cbv

/-- Partial rendering keeps a constrained recursive node visibly unresolved. -/
theorem constrained_recursion_is_hole :
    List.map (Except.map Prod.fst) (expandPartial endlessGraph 4 (.hole 0) repeatedState) =
      [.ok (.node (.hole 0) [])] := by
  rfl

/-- Unconstrained recursive roots have no oracle callback, including an oracle that would fail. -/
theorem unconstrained_recursion_no_callback :
    List.map (Except.map Prod.fst) (enumerateFully endlessGraph (fun (_ : Unit) _ => none)
      (fun _ _ _ => failure .invalidSlot) 4 () (initial 0)) = [.ok ()] := by
  rfl

/-- A graph whose two child positions must select the same one of two leaves. -/
def equalChildrenGraph : Graph Nat Bool :=
  ⟨fun node => if node = 0 then
      .alternatives [⟨2, [1, 1], [.branch [(0, .terminal), (1, .terminal)]], none⟩]
    else .alternatives [⟨10, [], [], none⟩, ⟨11, [], [], none⟩],
    fun left _ => left⟩

/-- The complete UVar driver retains both equal pairs and rejects both mixed pairs. -/
theorem equality_driver_exact :
    results equalChildrenGraph 99 12 0 =
      [.ok (.node 2 [.node 10 [], .node 10 []], []),
       .ok (.node 2 [.node 11 [], .node 11 []], [])] := by
  cbv

/-- A nested equality excludes child alternatives that lack the required position. -/
def nestedChildrenGraph : Graph Nat Bool :=
  ⟨fun node => if node = 0 then
      .alternatives [⟨2, [1, 1],
        [.branch [(0, .branch [(0, .terminal)]), (1, .branch [(0, .terminal)])]], none⟩]
    else if node = 1 then .alternatives [⟨10, [], [], none⟩, ⟨20, [2], [], none⟩]
    else .alternatives [⟨30, [], [], none⟩, ⟨31, [], [], none⟩],
    fun left _ => left⟩

/-- The source caller driver preserves both nested solutions and rejects missing paths. -/
theorem nested_equality_driver_exact :
    results nestedChildrenGraph 99 16 0 =
      [.ok (.node 2 [.node 20 [.node 30 []], .node 20 [.node 30 []]], []),
       .ok (.node 2 [.node 20 [.node 31 []], .node 20 [.node 31 []]], [])] := by
  cbv

end MicroCFTA.EnumerationState
