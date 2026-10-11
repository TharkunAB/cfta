import MicroCFTA.ObservationGraph

/-!
# Semantic pruning decisions and recursive scheduling

This module ports the control flow in `Refinement.Prune`. `ObservationGraph`
implements the finite specialization operation. Here a candidate stores the
result of its query and the ambiguity check. The source stops at the first
unknown result. Ambiguous actuals restore the complete original edge.

The recursive scheduler uses explicit fuel. Fuel exhaustion means that the
model has not established termination. It does not mean an empty language.
Interned node construction, equality narrowing, and solver calls remain
separate operations in the driver interface.
-/

namespace MicroCFTA.PruneSchedule
open Guards

/-- One specialized edge and the source query results for its observations. -/
structure Candidate (Edge : Type) where
  edge : Edge
  verdict : Verdict
  ambiguous : Bool
  deriving Repr

/-- An undecided query or an unfinished recursive computation. -/
inductive Error where
  | unknown | fuel
  deriving DecidableEq, Repr

/-- The source accumulator loop, including restoration of the original edge. -/
def check (original : Edge) : List Edge → List (Candidate Edge) → Except Error (List Edge)
  | retained, [] => .ok retained
  | retained, candidate :: rest =>
      match candidate.verdict with
      | .yes => check original (retained ++ [candidate.edge]) rest
      | .no => check original retained rest
      | .unknown => if candidate.ambiguous then .ok [original] else .error .unknown

/-- Keep exactly the proved candidates when all queries decide. -/
def decided : List (Candidate Edge) → List Edge
  | [] => []
  | candidate :: rest =>
      if candidate.verdict = .yes then candidate.edge :: decided rest else decided rest

/-- A fully decided pass preserves source order and multiplicity. -/
theorem check_decided (original : Edge) (candidates : List (Candidate Edge))
    (complete : ∀ c ∈ candidates, c.verdict ≠ .unknown) (retained : List Edge) :
    check original retained candidates = .ok (retained ++ decided candidates) := by
  induction candidates generalizing retained with
  | nil => simp [check, decided]
  | cons c cs ih =>
      have rest : ∀ d ∈ cs, d.verdict ≠ .unknown := by
        intro d hd
        exact complete d (by simp [hd])
      cases hc : c.verdict with
      | yes => simp [check, decided, hc, ih rest, List.append_assoc]
      | no => simp [check, decided, hc, ih rest]
      | unknown => exact False.elim (complete c (by simp) hc)

/-- The first ambiguous unknown restores the original, including its guard. -/
theorem ambiguous_restores (original : Edge) (prior suffix : List (Candidate Edge))
    (complete : ∀ c ∈ prior, c.verdict ≠ .unknown) (edge : Edge)
    (retained : List Edge) :
    check original retained (prior ++ ⟨edge, .unknown, true⟩ :: suffix) = .ok [original] := by
  induction prior generalizing retained with
  | nil => rfl
  | cons c cs ih =>
      have rest : ∀ d ∈ cs, d.verdict ≠ .unknown := by
        intro d hd
        exact complete d (by simp [hd])
      cases hc : c.verdict with
      | yes => simpa [check, hc] using ih rest (retained ++ [c.edge])
      | no => simpa [check, hc] using ih rest retained
      | unknown => exact False.elim (complete c (by simp) hc)

/-- An unambiguous unknown is an error even after successful candidates. -/
theorem unknown_errors (original : Edge) (prior suffix : List (Candidate Edge))
    (complete : ∀ c ∈ prior, c.verdict ≠ .unknown) (edge : Edge)
    (retained : List Edge) :
    check original retained (prior ++ ⟨edge, .unknown, false⟩ :: suffix) = .error .unknown := by
  induction prior generalizing retained with
  | nil => rfl
  | cons c cs ih =>
      have rest : ∀ d ∈ cs, d.verdict ≠ .unknown := by
        intro d hd
        exact complete d (by simp [hd])
      cases hc : c.verdict with
      | yes => simpa [check, hc] using ih rest (retained ++ [c.edge])
      | no => simpa [check, hc] using ih rest retained
      | unknown => exact False.elim (complete c (by simp) hc)

/-- Entry dispatch after equality narrowing and semantic/residual splitting. -/
def semantic (original discharged : Edge) (semanticTop hasFree readsRecursion : Bool)
    (candidates : List (Candidate Edge)) : Except Error (List Edge) :=
  if semanticTop then .ok [discharged]
  else if hasFree && readsRecursion then .ok [original]
  else check original [] candidates

/-- Reading through an unfinished recursive binder retains the whole edge. -/
theorem recursive_guard_retained (original discharged : Edge)
    (candidates : List (Candidate Edge)) :
    semantic original discharged false true true candidates = .ok [original] := rfl

/-- A top semantic guard drops only the already-separated semantic component. -/
theorem top_discharged (original discharged : Edge) (free through : Bool)
    (candidates : List (Candidate Edge)) :
    semantic original discharged true free through candidates = .ok [discharged] := rfl

/-- A finite source view of one interned node. -/
inductive View (Node Edge : Type) where
  | empty | reference
  | branches (edges : List Edge)
  | binder (body : Node)

/-- Source identity cache and recursive binders in scope. -/
structure Build (Node : Type) where
  cache : List (Node × Node) := []
  binders : List Node := []

/-- Source operations at the representation and guard-evaluation boundary. -/
structure Operations (Node Edge : Type) where
  view : Node → View Node Edge
  children : Edge → List Node
  replaceChildren : Edge → List Node → Edge
  narrow : Edge → Edge
  empty : Node → Bool
  evaluate : Build Node → Edge → Except Error (List Edge × Build Node)
  node : List Edge → Node
  rebuildBinder : Node → Node → Node

/-- Find the newest cached result by interned identity. -/
def lookup [DecidableEq Node] (q : Node) : List (Node × Node) → Option Node
  | [] => none
  | (key, value) :: rest => if q = key then some value else lookup q rest

mutual
  /-- Source bottom-up driver. Cache writes occur after the recursive result. -/
  def pruneNode [DecidableEq Node] (ops : Operations Node Edge) :
      Nat → Build Node → Node → Except Error (Node × Build Node)
    | 0, _, _ => .error .fuel
    | fuel + 1, build, q =>
      match ops.view q with
      | .empty | .reference => .ok (q, build)
      | .branches edges =>
          match lookup q build.cache with
          | some known => .ok (known, build)
          | none => do
              let (edges, next) ← pruneEdges ops fuel build edges
              let result := ops.node edges
              .ok (result, { next with cache := (q, result) :: next.cache })
      | .binder body =>
          match lookup q build.cache with
          | some known => .ok (known, build)
          | none => do
              let (pruned, next) ← pruneNode ops fuel { build with binders := q :: build.binders } body
              let rebuilt := ops.rebuildBinder q pruned
              let (result, last) ← if rebuilt = q then .ok (q, next)
                                  else pruneNode ops fuel next rebuilt
              .ok (result, { last with cache := (q, result) :: last.cache })

  /-- Prune every child in order before equality narrowing. -/
  def pruneChildren [DecidableEq Node] (ops : Operations Node Edge) :
      Nat → Build Node → List Node → Except Error (List Node × Build Node)
    | 0, _, _ => .error .fuel
    | _ + 1, build, [] => .ok ([], build)
    | fuel + 1, build, q :: qs => do
        let (child, next) ← pruneNode ops fuel build q
        let (children, last) ← pruneChildren ops fuel next qs
        .ok (child :: children, last)

  /-- Eliminate an empty narrowed child before running semantic queries. -/
  def pruneEdges [DecidableEq Node] (ops : Operations Node Edge) :
      Nat → Build Node → List Edge → Except Error (List Edge × Build Node)
    | 0, _, _ => .error .fuel
    | _ + 1, build, [] => .ok ([], build)
    | fuel + 1, build, edge :: rest => do
        let (children, next) ← pruneChildren ops fuel build (ops.children edge)
        let narrowed := ops.narrow (ops.replaceChildren edge children)
        let (retained, observed) ← if (ops.children narrowed).any ops.empty then .ok ([], next)
                       else ops.evaluate next narrowed
        let (suffix, last) ← pruneEdges ops fuel observed rest
        .ok (retained ++ suffix, last)
end

/-- The source never resolves or replaces a bare recursive reference here. -/
theorem reference_unchanged [DecidableEq Node] (ops : Operations Node Edge)
    (fuel : Nat) (build : Build Node) (q : Node) (reference : ops.view q = .reference) :
    pruneNode ops (fuel + 1) build q = .ok (q, build) := by
  simp [pruneNode, reference]

/-- A cached ordinary node does not rerun its children or solver queries. -/
theorem cache_hit [DecidableEq Node] (ops : Operations Node Edge)
    (fuel : Nat) (build : Build Node) (q known : Node) (edges : List Edge)
    (plain : ops.view q = .branches edges) (cached : lookup q build.cache = some known) :
    pruneNode ops (fuel + 1) build q = .ok (known, build) := by
  simp [pruneNode, plain, cached]

/-- A source success is different from an unfinished model execution. -/
theorem exhausted_not_empty [DecidableEq Node] (ops : Operations Node Edge)
    (build : Build Node) (q result : Node) (next : Build Node) :
    pruneNode ops 0 build q ≠ .ok (result, next) := by
  simp [pruneNode]

end MicroCFTA.PruneSchedule
