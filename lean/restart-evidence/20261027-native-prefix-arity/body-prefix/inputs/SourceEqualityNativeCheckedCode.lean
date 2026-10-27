import MicroCFTA.SourceEqualityConjoinAllocation
import MicroCFTA.SourceEqualityMkEdgeArity
import MicroCFTA.SourceRecursiveIntersectionCompile
import MicroCFTA.SourceRecursiveIntersectionKernelReadback

/-!
# Existing source code after the checked native edge decision

The accepted branch retains the ordered original child requests. The rejected
branch constructs the source sentinel without child requests. Equality-field
allocation precedes this code and remains part of the enclosing execution.
Only accepted branches have the older compiler correspondence proved here.
-/
namespace MicroCFTA.SourceEqualityNativeCheckedCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionKernel
open SourceEqualityConjoinAllocation SourceObservations SourceGuards
variable {Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint Formula

/-- Delay original child requests until the actual combined constraint passes its constructor check. -/
def children (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (combined : Allocated) :
    Code Symbol Guard (EdgeValue Symbol Guard) :=
  (SourceRecursiveIntersectionCode.walk (fun pair => requestNode domain pair.1 pair.2)
    (left.children.zip right.children)).bind fun values =>
      .work (makeEdge left.entry.key.symbol (readback combined) values) .pure

/-- The rejected or mismatched branch emits the exact source empty-edge constructor request. -/
def sentinel (left : EdgeValue Symbol Guard) : Code Symbol Guard (EdgeValue Symbol Guard) :=
  .work (makeEdge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) .pure

/-- Equal arity and literal combined readback identify the accepted code with the older compiler. -/
theorem children_eq_compileEdge (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (combined : Allocated) (conjoin : Guard → Guard → Guard)
    (arity : left.children.length = right.children.length)
    (same : readback combined = conjoin left.entry.key.constraint right.entry.key.constraint) :
    children domain left right combined =
      compileEdge SourceEqualityConstraintConstructors.top conjoin ⟨domain, left, right⟩ := by
  simp only [children, compileEdge, arity, ↓reduceIte, same]

/-- Actual allocated conjunction supplies the literal readback needed by accepted compiler correspondence. -/
theorem children_eq_of_conjoin [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (first second combined : Allocated)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : SourceEqualityConstraintAllocation.Ready before.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready before.constraints second.stored)
    (firstFields : readback first = left.entry.key.constraint) (secondFields : readback second = right.entry.key.constraint)
    (done : (SourceEqualityConjoinAllocation.conjoin le first second before).1 = .ok combined)
    (arity : left.children.length = right.children.length) :
    children domain left right combined = compileEdge SourceEqualityConstraintConstructors.top
      (SourceEqualityConstraintConstructors.conjoin le) ⟨domain, left, right⟩ := by
  obtain ⟨actual, completed, _, _, fields, _, _, _⟩ := conjoin_correct le first second before valid firstReady secondReady
  have identical : actual = combined := Except.ok.inj (completed.symm.trans done)
  subst actual
  apply children_eq_compileEdge domain left right combined _ arity
  simpa only [firstFields, secondFields] using fields

/-- The accepted code retains the actual source child callbacks and the final constructor cache. -/
theorem children_exact [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (combined : Allocated) (state : Machine Symbol Guard) :
    interpret nodes edges (children domain left right combined) state =
      (SourceRecursiveIntersectionKernel.walk (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
        (left.children.zip right.children) state).bind fun values after =>
          SourceRecursiveIntersectionKernel.work (makeEdge left.entry.key.symbol (readback combined) values) after := by
  simp only [children, interpret_bind, interpret_walk, interpret_requestNode_fun, interpret, result_bind_pure]

/-- Complete accepted child execution gives ordered receipts, exact fields, and the original incoming arity. -/
theorem children_readback [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (combined : Allocated) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (arity : left.children.length = right.children.length) (result : EdgeValue Symbol Guard) (final : Machine Symbol Guard)
    (done : interpret nodes edges (children domain left right combined) state = .done result final) :
    ∃ values after,
      WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩) (left.children.zip right.children) state values after ∧
      SourceRecursiveIntersectionKernel.work (makeEdge left.entry.key.symbol (readback combined) values) after = .done result final ∧
      result.entry.key.symbol = left.entry.key.symbol ∧ result.entry.key.constraint = readback combined ∧
      result.children = values ∧ result.children.length = left.children.length := by
  rw [children_eq_compileEdge domain left right combined (fun _ _ => readback combined) arity rfl,
    compileEdge_exact] at done
  obtain ⟨values, after, trace, built, symbol, guard, fields⟩ := edge_readback
    SourceEqualityConstraintConstructors.top (fun _ _ => readback combined)
    (fun domain left right => nodes ⟨domain, left, right⟩) calls domain left right state valid known leftResident rightResident arity result final done
  refine ⟨values, after, trace, built, symbol, guard, fields, ?_⟩
  rw [fields, trace.length, List.length_zip, arity, Nat.min_self]

/-- The source sentinel uses no recursive callback and retains its exact resulting heap. -/
theorem sentinel_exact [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (left : EdgeValue Symbol Guard) (state : Machine Symbol Guard) :
    interpret nodes edges (sentinel left) state =
      SourceRecursiveIntersectionKernel.work (makeEdge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) state := by
  simp only [sentinel, interpret, result_bind_pure]

/-- A complete satisfying conjunction cannot fail the constructor test at its represented incoming arity. -/
theorem accepted_of_conjunction [DecidableEq Formula] [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (first second : Guard) (combined : Allocated)
    (firstActive : SourceCompactGuards.ActiveOption first.equalities)
    (secondActive : SourceCompactGuards.ActiveOption second.equalities)
    (same : readback combined = SourceEqualityConstraintConstructors.conjoin le first second)
    (symbol : Label Formula) (terms : List (Language.Term (Label Formula))) (arity : Nat) (represented : arity = terms.length)
    (firstAccepted : SourceSymbolicIndex.acceptsConstraint formulas solver first (.node symbol terms) = true)
    (secondAccepted : SourceSymbolicIndex.acceptsConstraint formulas solver second (.node symbol terms) = true) :
    SourceEqualityMkEdgeAllocation.accepted (readback combined) arity = true := by
  rw [represented, same]
  apply SourceEqualityMkEdgeArity.accepted_of_source formulas solver _
    (SourceEqualityGuardReadback.active (SourceEqualityConstraintConstructors.conjoin_cached le first second)) symbol terms
  rw [SourceEqualityConstraintConstructors.conjoined le formulas solver first second firstActive secondActive,
    firstAccepted, secondAccepted]
  rfl

end MicroCFTA.SourceEqualityNativeCheckedCode
