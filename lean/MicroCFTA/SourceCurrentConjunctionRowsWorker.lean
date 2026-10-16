import MicroCFTA.SourceCurrentConjunctionRowsAllocation
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Literal current conjunction rows with physical equality allocation

Reads and projections retain their actual constructor heap. Tuple equality
folds retain their returned operation cache on success or failure.
Contradiction skips requirement projection. Two bounds control projection
and row reads. List scans recurse on the literal finite lists.
The exposure sequence completes all supplied operands. It does not
establish host lazy demand or the host's skipped operand reads.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsWorker
open InternedConstructorTemplates
local notation "Guard" => SourceSymbolicIndex.Constraint

abbrev Physical (Symbol Formula : Type) := SourceCurrentConjunctionRowsAllocation.State Symbol Formula
abbrev Job (Symbol Formula : Type) := SourceCurrentConjunctionCompletionReads.Job Symbol (Guard Formula)

/-- Equality failures and incomplete reads retain distinct source diagnostics. -/
inductive Fault where
  | equality (message : String)
  | missingEquality
  | pending (key : InternedBinderProtocol.NodeKey)
  | unresolved (name : InternedBinderProtocol.Reference)
  | exhausted (limit : SourceEqualityRequiredWorker.Limit)

/-- Every observation retains the exact constructor heap and equality-operation state. -/
inductive Outcome (Symbol Formula Output : Type) where
  | done (output : Output) (state : Physical Symbol Formula)
  | failed (fault : Fault) (state : Physical Symbol Formula)

def Outcome.state : Outcome Symbol Formula Output → Physical Symbol Formula
  | .done _ state | .failed _ state => state

/-- Only a completed prefix enters its continuation at the actual returned state. -/
def Outcome.bind (first : Outcome Symbol Formula Input)
    (next : Input → Physical Symbol Formula → Outcome Symbol Formula Output) : Outcome Symbol Formula Output :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- Read operand edge lists in their literal order without changing equality operations. -/
def exposures [DecidableEq (EdgeKey Symbol (Guard Formula))] (readFuel : Nat) :
    List (Value Symbol (Guard Formula)) → Physical Symbol Formula →
      Outcome Symbol Formula (List (List (EdgeValue Symbol (Guard Formula))))
  | [], before => .done [] before
  | value :: values, before =>
      match MergedFreshOrdinaryExposure.nodeEdges readFuel value before.heap with
      | .done edges heap =>
          (exposures readFuel values ⟨heap, before.equality⟩).bind fun remaining after => .done (edges :: remaining) after
      | .pending key heap => .failed (.pending key) ⟨heap, before.equality⟩
      | .unresolved name heap => .failed (.unresolved name) ⟨heap, before.equality⟩
      | .exhausted heap => .failed (.exhausted .head) ⟨heap, before.equality⟩

/-- Execute natural-path jobs through the literal signed forest worker in job order. -/
def projections [DecidableEq (EdgeKey Symbol (Guard Formula))] (projectionFuel readFuel : Nat) :
    List (Job Symbol Formula) → Physical Symbol Formula → Outcome Symbol Formula (List (Value Symbol (Guard Formula)))
  | [], before => .done [] before
  | (forest, path) :: jobs, before =>
      match SourceEqualityProjectionWorker.forest projectionFuel readFuel (path.map Int.ofNat) forest before.heap with
      | .done value heap =>
          (projections projectionFuel readFuel jobs ⟨heap, before.equality⟩).bind fun values after => .done (value :: values) after
      | .pending key heap => .failed (.pending key) ⟨heap, before.equality⟩
      | .unresolved name heap => .failed (.unresolved name) ⟨heap, before.equality⟩
      | .exhausted limit heap => .failed (.exhausted limit) ⟨heap, before.equality⟩

/-- Project each class in forest-major path order, then canonicalize its actual values. -/
def classes [DecidableEq (EdgeKey Symbol (Guard Formula))] (projectionFuel readFuel : Nat)
    (forests : List (List (Value Symbol (Guard Formula)))) :
    EqualityNormalize.Constraints → Physical Symbol Formula → Outcome Symbol Formula (List (List (Value Symbol (Guard Formula))))
  | [], before => .done [] before
  | paths :: constraints, before =>
      (projections projectionFuel readFuel (SourceCurrentConjunctionCompletionReads.jobs forests paths) before).bind
        fun projected middle =>
          (classes projectionFuel readFuel forests constraints middle).bind fun remaining after =>
            .done (SourceCurrentConjunctionRequirements.canonical projected :: remaining) after

/-- Literal child columns precede the actual class requirements. No arity check is added. -/
def requirements [DecidableEq (EdgeKey Symbol (Guard Formula))] (projectionFuel readFuel : Nat)
    (edges : List (EdgeValue Symbol (Guard Formula))) (constraints : EqualityNormalize.Constraints)
    (before : Physical Symbol Formula) : Outcome Symbol Formula (List (List (Value Symbol (Guard Formula)))) :=
  (classes projectionFuel readFuel (edges.map EdgeValue.children) constraints before).bind fun rows after =>
    .done ((SourceCurrentConjunctionRequirements.columns edges).map SourceCurrentConjunctionRequirements.canonical ++ rows) after

/-- The reached equality fold returns its exact cache before any live requirement projection. -/
noncomputable def tuple [DecidableEq (EdgeKey Symbol (Guard Formula))] (projectionFuel readFuel : Nat)
    (edges : List (EdgeValue Symbol (Guard Formula))) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Option (List (List (Value Symbol (Guard Formula))))) :=
  let folded := SourceCurrentConjunctionEquality.fold edges before.equality
  let current : Physical Symbol Formula := ⟨before.heap, folded.2⟩
  match folded.1 with
  | .error message => .failed (.equality message) current
  | .ok none => .failed .missingEquality current
  | .ok (some result) =>
      match SourceEqualityInheritedPayload.classes result.payload with
      | none => .done none current
      | some constraints =>
          (requirements projectionFuel readFuel edges constraints current).bind fun rows after => .done (some rows) after

/-- Process each literal tuple and omit only the tuples whose fold is contradictory. -/
noncomputable def tuples [DecidableEq (EdgeKey Symbol (Guard Formula))] (projectionFuel readFuel : Nat) :
    List (List (EdgeValue Symbol (Guard Formula))) → Physical Symbol Formula →
      Outcome Symbol Formula (List (List (List (Value Symbol (Guard Formula)))))
  | [], before => .done [] before
  | edges :: remaining, before =>
      (tuple projectionFuel readFuel edges before).bind fun row middle =>
        (tuples projectionFuel readFuel remaining middle).bind fun rows after =>
          .done (match row with | none => rows | some row => row :: rows) after

/-- Expose operands, form matching tuples in source order, then execute their allocated rows. -/
noncomputable def rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (Guard Formula))]
    (projectionFuel readFuel : Nat) (nodes : List (Value Symbol (Guard Formula))) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (List (List (List (Value Symbol (Guard Formula))))) :=
  (exposures readFuel nodes before).bind fun edges after =>
    tuples projectionFuel readFuel (SourceCurrentConjunctionTuples.tuples edges) after

end MicroCFTA.SourceCurrentConjunctionRowsWorker
