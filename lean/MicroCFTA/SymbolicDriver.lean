import MicroCFTA.Symbolic

/-!
# The bounded symbolic counting driver

This is an executable port of `Internal.Symbolic`'s mutually recursive
counter. Node identities and graph primitives form an explicit interface.
Bounds report errors. The state retains both graph counts and normalized
context counts. No list of complete terms is constructed by this driver.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Target Obligation)

/-- One edge carries the signed equality indicators supplied by `Constraint.indicators`. -/
structure Edge (Symbol : Type) where
  symbol : Symbol
  children : List Nat
  indicators : List (Int × List (List (List Nat)))
  deriving DecidableEq

/-- The shared interned graph and its identity-producing operations. -/
structure Graph (Symbol : Type) where
  edges : Nat → List (Edge Symbol)
  intersect : Nat → Nat → Nat
  condition : List Nat → Symbol × Nat → Nat → Nat
  project : List Nat → Nat → Nat

/-- Independent domains, substitutions, fresh names, and pending equalities. -/
structure Problem (Symbol : Type) where
  domains : List (Nat × Nat)
  bindings : List (Nat × Fragment Symbol)
  nextVariable : Nat
  obligations : List (Obligation Symbol)

/-- Normalized domain identities and obligations form the source context-cache key. -/
structure Key (Symbol : Type) where
  domains : List (Nat × Nat)
  obligations : List (Obligation Symbol)

/-- Counts shared by one compiled language. -/
structure Counts (Symbol : Type) where
  graphs : List (Nat × Int) := []
  contexts : List (Key Symbol × Int) := []

/-- Explicit execution bounds and source invariant violations. -/
inductive Error where
  | fuelExhausted | missingVariable | invalidRank | missingConstructor
  deriving DecidableEq, Repr

abbrev CountM (Symbol : Type) := StateT (Counts Symbol) (Except Error)

/-- Read a finite variable map. -/
def lookup (entries : List (Nat × Value)) (key : Nat) : Option Value :=
  (entries.find? fun entry => entry.1 == key).map Prod.snd

/-- Delete all entries for a variable. -/
def delete (entries : List (Nat × Value)) (key : Nat) : List (Nat × Value) :=
  entries.filter fun entry => entry.1 != key

/-- Insert or replace a variable, preserving numeric key order. -/
def insert (entries : List (Nat × Value)) (key : Nat) (value : Value) : List (Nat × Value) :=
  ((key, value) :: delete entries key).mergeSort fun left right => left.1 ≤ right.1

mutual
  /-- Structural context equality. -/
  def fragmentEq [DecidableEq Symbol] : Fragment Symbol → Fragment Symbol → Bool
    | .var left, .var right => decide (left = right)
    | .constructor left children, .constructor right others =>
        decide (left = right) && fragmentsEq children others
    | _, _ => false

  /-- Equality of ordered context lists. -/
  def fragmentsEq [DecidableEq Symbol] : List (Fragment Symbol) → List (Fragment Symbol) → Bool
    | [], [] => true
    | left :: rest, right :: others => fragmentEq left right && fragmentsEq rest others
    | _, _ => false
end

/-- Equality of a context and its remaining path. -/
def targetEq [DecidableEq Symbol] (left right : Target Symbol) : Bool :=
  fragmentEq left.fragment right.fragment && decide (left.path = right.path)

/-- Equality of pending obligations. -/
def obligationEq [DecidableEq Symbol] : Obligation Symbol → Obligation Symbol → Bool
  | .exists left, .exists right => targetEq left right
  | .equal a b, .equal c d => targetEq a c && targetEq b d
  | _, _ => false

/-- Equality of two ordered lists under an explicit element comparison. -/
def equalLists (same : Value → Value → Bool) : List Value → List Value → Bool
  | [], [] => true
  | left :: rest, right :: others => same left right && equalLists same rest others
  | _, _ => false

mutual
  /-- Source-derived context order: variables precede constructors. -/
  def compareFragment [Ord Symbol] : Fragment Symbol → Fragment Symbol → Ordering
    | .var left, .var right => compare left right
    | .var _, .constructor _ _ => .lt
    | .constructor _ _, .var _ => .gt
    | .constructor left children, .constructor right others =>
        match compare left right with | .eq => compareFragments children others | order => order

  /-- Lexicographic context-child comparison. -/
  def compareFragments [Ord Symbol] : List (Fragment Symbol) → List (Fragment Symbol) → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | left :: rest, right :: others =>
        match compareFragment left right with | .eq => compareFragments rest others | order => order
end

/-- Source-derived target order. -/
def compareTarget [Ord Symbol] (left right : Target Symbol) : Ordering :=
  match compareFragment left.fragment right.fragment with
  | .eq => compare left.path right.path
  | order => order

/-- Source-derived obligation order: existence precedes equality. -/
def compareObligation [Ord Symbol] : Obligation Symbol → Obligation Symbol → Ordering
  | .exists left, .exists right => compareTarget left right
  | .exists _, .equal _ _ => .lt
  | .equal _ _, .exists _ => .gt
  | .equal a b, .equal c d =>
      match compareTarget a c with | .eq => compareTarget b d | order => order

/-- Keep the first copy of every equal entry. -/
def uniqueBy (same : Value → Value → Bool) : List Value → List Value
  | [] => []
  | first :: rest => first :: uniqueBy same (rest.filter fun other => !same first other)
termination_by values => values.length
decreasing_by
  simp only [List.length_unattach, List.length_cons]
  apply Nat.lt_succ_of_le
  exact Nat.le_trans (List.length_filter_le ..) (by simp)

/-- Concrete equality of context-cache keys. -/
def keyEq [DecidableEq Symbol] (left right : Key Symbol) : Bool :=
  decide (left.domains = right.domains) &&
    equalLists obligationEq left.obligations right.obligations

mutual
  /-- Follow all bindings in a constructor context. -/
  def inline (bindings : List (Nat × Fragment Symbol)) : Nat → Fragment Symbol → Except Error (Fragment Symbol)
    | 0, _ => .error .fuelExhausted
    | fuel + 1, .var name =>
        match lookup bindings name with | none => .ok (.var name) | some fragment => inline bindings fuel fragment
    | fuel + 1, .constructor symbol children => do
        pure (.constructor symbol (← inlineMany bindings fuel children))

  /-- Inline ordered child contexts. -/
  def inlineMany (bindings : List (Nat × Fragment Symbol)) :
      Nat → List (Fragment Symbol) → Except Error (List (Fragment Symbol))
    | _, [] => .ok []
    | 0, _ :: _ => .error .fuelExhausted
    | fuel + 1, child :: rest => do
        pure ((← inline bindings fuel child) :: (← inlineMany bindings fuel rest))
end

/-- Follow substitutions and constructor prefixes without expanding a domain. -/
def follow (bindings : List (Nat × Fragment Symbol)) :
    Nat → Fragment Symbol → List Nat → Except Error (Option (Target Symbol))
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, .var name, path =>
      match lookup bindings name with
      | none => .ok (some ⟨.var name, path⟩)
      | some fragment => follow bindings fuel fragment path
  | fuel + 1, fragment@(.constructor _ _), [] => do
      pure (some ⟨← inline bindings fuel fragment, []⟩)
  | fuel + 1, .constructor _ children, index :: rest =>
      match children[index]? with
      | none => .ok none
      | some child => follow bindings fuel child rest

mutual
  /-- Rename every live variable through the compact domain-numbering map. -/
  def rename (names : List (Nat × Nat)) : Nat → Fragment Symbol → Except Error (Fragment Symbol)
    | 0, _ => .error .fuelExhausted
    | _ + 1, .var name =>
        match lookup names name with | none => .error .missingVariable | some new => .ok (.var new)
    | fuel + 1, .constructor symbol children => do
        pure (.constructor symbol (← renameMany names fuel children))

  /-- Rename ordered child contexts. -/
  def renameMany (names : List (Nat × Nat)) : Nat → List (Fragment Symbol) → Except Error (List (Fragment Symbol))
    | _, [] => .ok []
    | 0, _ :: _ => .error .fuelExhausted
    | fuel + 1, child :: rest => do
        pure ((← rename names fuel child) :: (← renameMany names fuel rest))
end

/-- An empty remaining path needs no existence obligation. -/
def required (target : Target Symbol) : List (Obligation Symbol) :=
  if target.path.isEmpty then [] else [.exists target]

/-- Inline, follow, and rename one target. -/
def normalizeTarget (fuel : Nat) (problem : Problem Symbol) (names : List (Nat × Nat))
    (target : Target Symbol) : Except Error (Option (Target Symbol)) := do
  match ← follow problem.bindings fuel target.fragment target.path with
  | none => pure none
  | some followed => pure (some ⟨← rename names fuel followed.fragment, followed.path⟩)

/-- Normalize one obligation and preserve self-equality path existence. -/
def normalizeObligation [DecidableEq Symbol] [Ord Symbol] (fuel : Nat)
    (problem : Problem Symbol) (names : List (Nat × Nat)) :
    Obligation Symbol → Except Error (Option (List (Obligation Symbol)))
  | .exists target => do
      pure ((← normalizeTarget fuel problem names target).map required)
  | .equal left right => do
      let left ← normalizeTarget fuel problem names left
      let right ← normalizeTarget fuel problem names right
      match left, right with
      | some first, some second =>
          if targetEq first second then pure (some (required first))
          else if compareTarget first second == .gt then pure (some [.equal second first])
          else pure (some [.equal first second])
      | _, _ => pure none

/-- Normalize bindings, obligations, and domain names before consulting the context cache. -/
def normalize [DecidableEq Symbol] [Ord Symbol] (fuel : Nat) (problem : Problem Symbol) :
    Except Error (Option (Problem Symbol)) := do
  let names := problem.domains.zipIdx.map fun (entry, new) => (entry.1, new)
  let pending ← problem.obligations.mapM (normalizeObligation fuel problem names)
  if pending.any Option.isNone then pure none else
    let obligations := (uniqueBy obligationEq (pending.flatMap fun entry => entry.getD [])).mergeSort
      fun left right => compareObligation left right != .gt
    pure (some ⟨problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)), [],
      problem.domains.length, obligations⟩)

mutual
  /-- Check whether a context contains a selected variable. Normalized problems have no bindings. -/
  def occurs (name : Nat) : Fragment Symbol → Bool
    | .var other => name == other
    | .constructor _ children => occursMany name children

  /-- Occurrence in any ordered child context. -/
  def occursMany (name : Nat) : List (Fragment Symbol) → Bool
    | [] => false
    | child :: rest => occurs name child || occursMany name rest
end

/-- Intersect equal constructors and multiply their signed indicator polynomials. -/
def intersectEdge [DecidableEq Symbol] (graph : Graph Symbol) (left right : Edge Symbol) : Option (Edge Symbol) :=
  if left.symbol = right.symbol ∧ left.children.length = right.children.length then
    some ⟨left.symbol, List.zipWith graph.intersect left.children right.children,
      left.indicators.flatMap fun (coefficient, classes) =>
        right.indicators.map fun (other, constraints) => (coefficient * other, classes ++ constraints)⟩
  else none

/-- Read a required domain or expose the source's partial-map invariant failure. -/
def domain (problem : Problem Symbol) (name : Nat) : Except Error Nat :=
  match lookup problem.domains name with | none => .error .missingVariable | some node => .ok node

/-- Distinct-intersection counting reuses the proved signed-map implementation. -/
def countUnion [DecidableEq Symbol] (graph : Graph Symbol)
    (count : Edge Symbol → CountM Symbol Int) (edges : List (Edge Symbol)) : CountM Symbol Int := do
  let pieces := Symbolic.unionCoefficients (intersectEdge graph) edges
  let values ← pieces.mapM fun (edge, coefficient) => do pure (coefficient * (← count edge))
  pure values.sum

mutual
  /-- Count one shared node once per identity. -/
  def countNode [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) : Nat → Nat → CountM Symbol Int
    | 0, _ => throw .fuelExhausted
    | fuel + 1, node => do
        let edges := graph.edges node
        if edges.isEmpty then pure 0 else
          match lookup (← get).graphs node with
          | some count => pure count
          | none =>
              let count ← countUnion graph (countEdge graph fuel) edges
              modify fun counts => {counts with graphs := insert counts.graphs node count}
              pure count

  /-- Convert an edge into independent domains and equality obligations. -/
  def countEdge [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) : Nat → Edge Symbol → CountM Symbol Int
    | 0, _ => throw .fuelExhausted
    | fuel + 1, edge => do
        let context := Fragment.constructor edge.symbol
          ((List.range edge.children.length).map Fragment.var)
        let values ← edge.indicators.mapM fun (coefficient, classes) => do
          let count ← solve graph fuel
            ⟨edge.children.zipIdx.map (fun (node, name) => (name, node)), [], edge.children.length,
              Symbolic.edgeObligations context classes⟩
          pure (coefficient * count)
        pure values.sum

  /-- Normalize and cache each equality context before choosing the next step. -/
  def solve [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) : Nat → Problem Symbol → CountM Symbol Int
    | 0, _ => throw .fuelExhausted
    | fuel + 1, problem => do
        if problem.domains.any (fun entry => (graph.edges entry.2).isEmpty) then pure 0 else
          match ← liftM (normalize (fuel + 1) problem) with
          | none => pure 0
          | some normalized =>
              let key : Key Symbol := ⟨normalized.domains, normalized.obligations⟩
              match (← get).contexts.find? (fun entry => keyEq entry.1 key) with
              | some (_, count) => pure count
              | none =>
                  let count ← solveStep graph fuel normalized
                  modify fun counts => {counts with contexts := (key, count) :: counts.contexts}
                  pure count

  /-- Resolve one pending path, or multiply independent domain counts. -/
  def solveStep [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) : Nat → Problem Symbol → CountM Symbol Int
    | 0, _ => throw .fuelExhausted
    | fuel + 1, problem =>
        match problem.obligations with
        | [] => do
            let counts ← problem.domains.mapM fun entry => countNode graph fuel entry.2
            pure counts.prod
        | .exists target :: rest =>
            match Symbolic.resolveContext target.fragment target.path with
            | .absent => pure 0
            | .expand name => expandVariable graph fuel problem name
            | .resolved _ => solve graph fuel {problem with obligations := rest}
        | .equal left right :: rest =>
            match Symbolic.resolveContext left.fragment left.path,
                Symbolic.resolveContext right.fragment right.path with
            | .absent, _ | _, .absent => pure 0
            | .expand name, _ | _, .expand name => expandVariable graph fuel problem name
            | .resolved first, .resolved second => unify graph fuel {problem with obligations := rest} first second

  /-- Merge variable domains, expand variable-constructor equality, or compare constructors. -/
  def unify [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) :
      Nat → Problem Symbol → Fragment Symbol → Fragment Symbol → CountM Symbol Int
    | 0, _, _, _ => throw .fuelExhausted
    | fuel + 1, problem, .var left, .var right => do
        if left = right then solve graph fuel problem else
          let common := graph.intersect (← liftM (domain problem left)) (← liftM (domain problem right))
          solve graph fuel {problem with
            domains := insert (delete problem.domains left) right common
            bindings := insert problem.bindings left (.var right)}
    | fuel + 1, problem, .var name, fragment@(.constructor _ _) =>
        if occurs name fragment then pure 0 else
          expandVariable graph fuel {problem with
            obligations := Obligation.equal ⟨.var name, []⟩ ⟨fragment, []⟩ :: problem.obligations} name
    | fuel + 1, problem, fragment@(.constructor _ _), .var name =>
        unify graph fuel problem (.var name) fragment
    | fuel + 1, problem, .constructor left children, .constructor right others =>
        if left ≠ right ∨ children.length ≠ others.length then pure 0 else
          solve graph fuel {problem with
            obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations}

  /-- Expose a variable's root and retain overlapping alternatives by inclusion-exclusion. -/
  def expandVariable [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) :
      Nat → Problem Symbol → Nat → CountM Symbol Int
    | 0, _, _ => throw .fuelExhausted
    | fuel + 1, problem, name => do
        let node ← liftM (domain problem name)
        countUnion graph (fun edge => do
          let names := List.range' problem.nextVariable edge.children.length
          let context := Fragment.constructor edge.symbol (names.map Fragment.var)
          let values ← edge.indicators.mapM fun (coefficient, classes) => do
            let count ← solve graph fuel
              {problem with
                domains := ((names.zip edge.children) ++ delete problem.domains name).mergeSort
                  (fun left right => left.1 ≤ right.1)
                bindings := insert problem.bindings name context
                nextVariable := problem.nextVariable + edge.children.length
                obligations := Symbolic.edgeObligations context classes ++ problem.obligations}
            pure (coefficient * count)
          pure values.sum) (graph.edges node)
end

/-- Run the actual bounded counter with initially empty memo tables. -/
def cardinality [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (fuel root : Nat) :
    Except Error Int := (countNode graph fuel root {}).map Prod.fst

/-- Possible constructors use arity, user key, then symbol as their total order. -/
def constructorsAt [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (path : List Nat) (root : Nat) : List (Symbol × Nat) :=
  ((graph.edges (graph.project path root)).map fun edge => (edge.symbol, edge.children.length)).eraseDups.mergeSort
    fun left right =>
      (match compare left.2 right.2 with
      | .eq => match compare (order left.1) (order right.1) with
        | .eq => compare left.1 right.1
        | result => result
      | result => result) != .gt

/-- Evaluate from a count snapshot and discard newly computed cache entries. -/
def isolated (action : CountM Symbol Value) : CountM Symbol Value := do
  let counts ← get
  pure (← liftM (action counts)).1

mutual
  /-- Decode a prefix by counted constructor blocks, retaining the conditioned graph and suffix rank. -/
  def selectAt [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → CountM Symbol (Term Symbol × Nat × Int)
    | 0, _, _, _ => throw .fuelExhausted
    | fuel + 1, root, path, rank => do
        let projected := graph.project path root
        if (← countNode graph fuel projected) = 1 then
          pure (← isolated (selectUnique graph order fuel projected []), root, rank)
        else chooseConstructor graph order fuel root path rank (constructorsAt graph order path root)

  /-- Skip complete constructor blocks by their exact counts. -/
  def chooseConstructor [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → List (Symbol × Nat) → CountM Symbol (Term Symbol × Nat × Int)
    | 0, _, _, _, _ => throw .fuelExhausted
    | _ + 1, _, _, _, [] => throw .missingConstructor
    | fuel + 1, root, path, remaining, constructor :: rest => do
        let restricted := graph.condition path constructor root
        let count ← countNode graph fuel restricted
        if remaining ≥ count then chooseConstructor graph order fuel root path (remaining - count) rest
        else
          let (children, final, suffix) ← selectChildren graph order fuel restricted path remaining
            (List.range constructor.2)
          pure (.node constructor.1 children, final, suffix)

  /-- Select child positions left to right in the progressively restricted graph. -/
  def selectChildren [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → List Nat → CountM Symbol (List (Term Symbol) × Nat × Int)
    | _, root, _, rank, [] => pure ([], root, rank)
    | 0, _, _, _, _ :: _ => throw .fuelExhausted
    | fuel + 1, root, path, rank, index :: rest => do
        let (term, restricted, suffix) ← selectAt graph order fuel root (path ++ [index]) rank
        let (children, final, finalRank) ← selectChildren graph order fuel restricted path suffix rest
        pure (term :: children, final, finalRank)

  /-- Decode a singleton projected language without restricting unrelated siblings. -/
  def selectUnique [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → CountM Symbol (Term Symbol)
    | 0, _, _ => throw .fuelExhausted
    | fuel + 1, root, path => uniqueConstructor graph order fuel root path (constructorsAt graph order path root)

  /-- The singleton decoder selects the first nonempty constructor block. -/
  def uniqueConstructor [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → List (Symbol × Nat) → CountM Symbol (Term Symbol)
    | 0, _, _, _ => throw .fuelExhausted
    | _ + 1, _, _, [] => throw .missingConstructor
    | fuel + 1, root, path, constructor :: rest => do
        let count ← countNode graph fuel (graph.condition path constructor root)
        if count = 0 then uniqueConstructor graph order fuel root path rest else
          let children ← (List.range constructor.2).mapM fun index =>
            isolated (selectUnique graph order fuel root (path ++ [index]))
          pure (.node constructor.1 children)
end

/-- Public bounds checking precedes the internal source selection operation. -/
def unrank [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (rank : Int) : Except Error (Term Symbol) := do
  let (total, counts) ← countNode graph fuel root {}
  if rank < 0 ∨ total ≤ rank then throw .invalidRank
  pure (← selectAt graph order fuel root [] rank counts).1.1

/-- A plain leaf's indicator is one. -/
def plainLeaf (symbol : Nat) : Edge Nat := ⟨symbol, [], [(1, [])]⟩

/-- Masks zero to three encode finite subsets of the two leaf symbols. -/
def maskLeaves (mask : Nat) : List Nat :=
  ([0, 1] : List Nat).filter fun symbol => if symbol = 0 then mask % 2 = 1 else mask / 2 % 2 = 1

/-- A singleton domain for one valid leaf symbol. -/
def singletonMask (symbol : Nat) : Nat := if symbol = 0 then 1 else if symbol = 1 then 2 else 0

/-- Intersect the two represented finite leaf domains. -/
def intersectMask (left right : Nat) : Nat := Nat.land left right

/-- Pair identities retain independent child masks and a child equality. -/
def pairId (left right : Nat) : Nat := 4 + 4 * left + right

/-- Decode the two child masks from a pair identity. -/
def pairMasks (node : Nat) : Nat × Nat := ((node - 4) / 4, (node - 4) % 4)

/-- A finite graph family closed under equality-pair conditioning and projection. -/
def pairGraph : Graph Nat :=
  {edges := fun node =>
    if node < 4 then (maskLeaves node).map plainLeaf else
      let masks := pairMasks node
      [⟨2, [masks.1, masks.2], [(1, [[[0], [1]]])]⟩]
   intersect := fun left right =>
    if left < 4 ∧ right < 4 then intersectMask left right else
      let a := pairMasks left
      let b := pairMasks right
      pairId (intersectMask a.1 b.1) (intersectMask a.2 b.2)
   condition := fun path (symbol, arity) node =>
    if node < 4 then
      if path = [] ∧ arity = 0 then intersectMask node (singletonMask symbol) else 0
    else
      let masks := pairMasks node
      match path with
      | [] => if symbol = 2 ∧ arity = 2 then node else 0
      | [0] => if arity = 0 then pairId (intersectMask masks.1 (singletonMask symbol)) masks.2 else 0
      | [1] => if arity = 0 then pairId masks.1 (intersectMask masks.2 (singletonMask symbol)) else 0
      | _ => 0
   project := fun path node =>
    if path = [] then node else
    if node < 4 then 0 else
      let masks := pairMasks node
      match path with | [0] => masks.1 | [1] => masks.2 | _ => 0}

/-- Full normalized-context counting gives two terms for two equal two-element domains. -/
theorem equal_pair_count : cardinality pairGraph 80 (pairId 3 3) = .ok 2 := by
  cbv

/-- A conditioned equality with disjoint domains has no term. -/
theorem disjoint_equal_pair_count : cardinality pairGraph 80 (pairId 1 2) = .ok 0 := by
  cbv

/-- The actual constructor-conditioned decoder gives the first distinct pair. -/
theorem equal_pair_rank_zero :
    unrank pairGraph id 120 (pairId 3 3) 0 = .ok (.node 2 [.node 0 [], .node 0 []]) := by
  cbv

/-- The actual decoder uses its singleton shortcut and residual suffix rank for the second pair. -/
theorem equal_pair_rank_one :
    unrank pairGraph id 120 (pairId 3 3) 1 = .ok (.node 2 [.node 1 [], .node 1 []]) := by
  cbv

/-- The public wrapper rejects both negative and upper-bound ranks. -/
theorem equal_pair_bounds :
    unrank pairGraph id 120 (pairId 3 3) (-1) = .error .invalidRank ∧
    unrank pairGraph id 120 (pairId 3 3) 2 = .error .invalidRank := by
  constructor <;> cbv

mutual
  /-- Add preceding constructor blocks and condition each matched prefix. -/
  def rankAt [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Term Symbol → Int → CountM Symbol (Option (Nat × Int))
    | 0, _, _, _, _ => throw .fuelExhausted
    | fuel + 1, root, path, term@(.node symbol children), before => do
        let projected := graph.project path root
        if (← countNode graph fuel projected) = 1 then
          let unique ← isolated (selectUnique graph order fuel projected [])
          pure (if termEq unique term then some (root, before) else none)
        else
          let available := constructorsAt graph order path root
          if (symbol, children.length) ∈ available then
            rankConstructor graph order fuel root path (symbol, children.length) children before available
          else pure none

  /-- Find the desired constructor and add the counts of every earlier constructor. -/
  def rankConstructor [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Symbol × Nat → List (Term Symbol) → Int → List (Symbol × Nat) →
      CountM Symbol (Option (Nat × Int))
    | 0, _, _, _, _, _, _ => throw .fuelExhausted
    | _ + 1, _, _, _, _, _, [] => pure none
    | fuel + 1, root, path, wanted, children, before, constructor :: rest => do
        let restricted := graph.condition path constructor root
        let count ← countNode graph fuel restricted
        if constructor = wanted then
          if count = 0 then pure none else
            rankChildren graph order fuel restricted path before children.zipIdx
        else rankConstructor graph order fuel root path wanted children (before + count) rest

  /-- Rank each child in the graph restricted by its preceding siblings. -/
  def rankChildren [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → List (Term Symbol × Nat) → CountM Symbol (Option (Nat × Int))
    | _, root, _, before, [] => pure (some (root, before))
    | 0, _, _, _, _ :: _ => throw .fuelExhausted
    | fuel + 1, root, path, before, (child, index) :: rest => do
        match ← rankAt graph order fuel root (path ++ [index]) child before with
        | none => pure none
        | some (restricted, next) => rankChildren graph order fuel restricted path next rest
end

/-- The source inverse shares the initial graph counts with its selections. -/
def rankOf [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (term : Term Symbol) :
    Except Error (Option Int) := do
  let (_, counts) ← countNode graph fuel root {}
  pure ((← rankAt graph order fuel root [] term 0 counts).1.map Prod.snd)

/-- Both selected terms return their distinct source ranks. -/
theorem equal_pair_inverse_ranks :
    rankOf pairGraph id 120 (pairId 3 3) (.node 2 [.node 0 [], .node 0 []]) = .ok (some 0) ∧
    rankOf pairGraph id 120 (pairId 3 3) (.node 2 [.node 1 [], .node 1 []]) = .ok (some 1) := by
  constructor <;> cbv

/-- The source inverse rejects a mixed pair rather than assigning an accepted rank. -/
theorem unequal_pair_rejected :
    rankOf pairGraph id 120 (pairId 3 3) (.node 2 [.node 0 [], .node 1 []]) = .ok none := by
  cbv

/-- Equal user keys retain distinct symbols through the final symbol comparison. -/
theorem colliding_order_keys_keep_both_terms :
    unrank pairGraph (fun _ => (0 : Nat)) 120 (pairId 3 3) 0 = .ok (.node 2 [.node 0 [], .node 0 []]) ∧
    unrank pairGraph (fun _ => (0 : Nat)) 120 (pairId 3 3) 1 = .ok (.node 2 [.node 1 [], .node 1 []]) := by
  constructor <;> cbv

/-- Negated equality is the unconstrained indicator minus the equality indicator. -/
def unequalPairGraph : Graph Nat :=
  {pairGraph with edges := fun node =>
    if node < 4 then pairGraph.edges node else
      let masks := pairMasks node
      [⟨2, [masks.1, masks.2], [(1, []), (-1, [[[0], [1]]])]⟩]}

/-- Signed guard counting retains exactly the two unequal pairs. -/
theorem negative_indicator_count : cardinality unequalPairGraph 100 (pairId 3 3) = .ok 2 := by
  cbv

/-- The counted constructor decoder reaches both members of the negated equality language. -/
theorem negative_indicator_ranks :
    unrank unequalPairGraph id 140 (pairId 3 3) 0 = .ok (.node 2 [.node 0 [], .node 1 []]) ∧
    unrank unequalPairGraph id 140 (pairId 3 3) 1 = .ok (.node 2 [.node 1 [], .node 0 []]) := by
  constructor <;> cbv

/-- Two different root alternatives overlap in exactly one term. -/
def overlapGraph : Graph Nat :=
  {pairGraph with edges := fun node =>
    if node = 20 then
      [⟨2, [3, 1], [(1, [])]⟩, ⟨2, [1, 3], [(1, [])]⟩]
    else pairGraph.edges node}

/-- The full symbolic union counter counts three distinct terms, although there are four runs. -/
theorem overlapping_alternatives_count : cardinality overlapGraph 100 20 = .ok 3 := by
  cbv

/-- Nested equality forces expansion through optional wrappers and rejects missing positions. -/
def nestedGraph : Graph Nat :=
  {edges := fun node =>
    if node = 0 then []
    else if node = 1 then [plainLeaf 0, plainLeaf 1]
    else if node = 2 then [plainLeaf 9, ⟨8, [1], [(1, [])]⟩]
    else [⟨7, [2, 2], [(1, [[[0, 0], [1, 0]]])]⟩]
   intersect := fun left right => if left = right then left else 0
   condition := fun _ _ _ => 0
   project := fun _ _ => 0}

/-- The actual normalize/unify/expand driver preserves both nested equal terms. -/
theorem nested_expansion_count : cardinality nestedGraph 180 3 = .ok 2 := by
  cbv

/-- Exhausted execution bounds are explicit errors, not evidence of an empty language. -/
theorem insufficient_fuel_is_error : cardinality pairGraph 0 (pairId 3 3) = .error .fuelExhausted := rfl

/-- The tested efficient decoder's outputs coincide exactly with an independent two-term language. -/
theorem equality_example_count_and_decoder :
    cardinality pairGraph 80 (pairId 3 3) = .ok 2 ∧
    (∀ rank : Fin 2, unrank pairGraph id 120 (pairId 3 3) rank.val =
      .ok (.node 2 [.node rank.val [], .node rank.val []])) ∧
    (∀ rank : Fin 2, rankOf pairGraph id 120 (pairId 3 3)
      (.node 2 [.node rank.val [], .node rank.val []]) = .ok (some rank.val)) := by
  refine ⟨equal_pair_count, ?_, ?_⟩
  · intro rank
    rcases rank with ⟨rank, bound⟩
    have alternatives : rank = 0 ∨ rank = 1 := by omega
    rcases alternatives with rfl | rfl
    · exact equal_pair_rank_zero
    · exact equal_pair_rank_one
  · intro rank
    rcases rank with ⟨rank, bound⟩
    have alternatives : rank = 0 ∨ rank = 1 := by omega
    rcases alternatives with rfl | rfl
    · exact equal_pair_inverse_ranks.1
    · exact equal_pair_inverse_ranks.2

/-- Structural context equality recognizes exactly identical fragments. -/
theorem fragmentEq_correct [DecidableEq Symbol] (left right : Fragment Symbol) :
    fragmentEq left right = true ↔ left = right := by
  induction left using Fragment.rec
    (motive_2 := fun lefts => ∀ rights : List (Fragment Symbol),
      fragmentsEq lefts rights = true ↔ lefts = rights) generalizing right with
  | var name => cases right <;> simp [fragmentEq]
  | constructor symbol children ih => cases right <;> simp [fragmentEq, ih]
  | nil rights => cases rights <;> simp [fragmentsEq]
  | cons first rest ihfirst ihrest rights => cases rights <;> simp [fragmentsEq, ihfirst, ihrest]

/-- Target equality compares both its whole context and its remaining path. -/
theorem targetEq_correct [DecidableEq Symbol] (left right : Target Symbol) :
    targetEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [targetEq, fragmentEq_correct]

/-- Cache-obligation equality does not identify different suspended requirements. -/
theorem obligationEq_correct [DecidableEq Symbol] (left right : Obligation Symbol) :
    obligationEq left right = true ↔ left = right := by
  cases left <;> cases right <;> simp [obligationEq, targetEq_correct]

/-- Element equality lifts to exact ordered-list equality. -/
theorem equalLists_correct (same : Value → Value → Bool)
    (correct : ∀ left right, same left right = true ↔ left = right) (left right : List Value) :
    equalLists same left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalLists]
  | cons first rest ih => cases right <;> simp [equalLists, correct, ih]

/-- Distinct normalized contexts cannot collide in the executable context cache. -/
theorem keyEq_correct [DecidableEq Symbol] (left right : Key Symbol) :
    keyEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [keyEq, equalLists_correct obligationEq obligationEq_correct]

end MicroCFTA.SymbolicDriver
