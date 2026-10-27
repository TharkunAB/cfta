import MicroCFTA.SourcePruningEnumerationOwnArity
import MicroCFTA.SourceEqualityIntersectionEdgeAllocation
import MicroCFTA.SourceEqualityNativeCheckedCode

/-!
# Fresh arity from the actual checked native child worker

The prefix must return its ready constraint.
The child worker must actually return the observed row.
The conclusion retains its complete ordered child and constructor receipts.
-/
namespace MicroCFTA.SourcePruningEnumerationCheckedWorkerArity
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
open InternedEdgeResidency IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionKernel
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula

/-- The ready prefix and actual child return derive fresh arity without a gate premise. -/
theorem observed_projected_arity
    [DecidableEq (SourceGuards.Guard FullSyntax.Formula)] [DecidableEq (EdgeKey Symbol Constraint)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second combined : Allocated) (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (firstReady : SourceEqualityConstraintAllocation.Ready operations.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready operations.constraints second.stored)
    (nodes : NodeCall Symbol Constraint) (edges : EdgeCall Symbol Constraint)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Cache.Interned DomainKey) (left right : EdgeValue Symbol Constraint)
    (state : Machine Symbol Constraint) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (prepared : (SourceEqualityIntersectionEdgeAllocation.run le first second
      left.children.length right.children.length operations).1 = .ok (.ready combined))
    (result : EdgeValue Symbol Constraint) (final : Machine Symbol Constraint)
    (done : interpret nodes edges
      (SourceEqualityNativeCheckedCode.children domain left right combined) state = .done result final)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project result.entry.key.constraint = some (tries, residual)) :
    ∃ values after,
      WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
        (left.children.zip right.children) state values after ∧
      SourceRecursiveIntersectionKernel.work
        (makeEdge left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after =
          .done result final ∧
      result.entry.key.symbol = left.entry.key.symbol ∧
      result.entry.key.constraint = SourceEqualityConjoinAllocation.readback combined ∧
      result.children = values ∧ result.children.length = left.children.length ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length (suspendedVars start tries) = true := by
  have sameArity : left.children.length = right.children.length := by
    by_cases same : left.children.length = right.children.length
    · exact same
    · have impossible := congrArg Prod.fst
        (SourceEqualityIntersectionEdgeAllocation.run_mismatch le first second
          left.children.length right.children.length operations same)
      rw [prepared] at impossible
      cases impossible
  obtain ⟨branch, literal, sourceSame, _prefixValid, _growth, ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second
      left.children.length right.children.length operations operationsValid firstReady secondReady
  have branchSame : branch = .ready combined := Except.ok.inj (literal.symm.trans prepared)
  subst branch
  obtain ⟨_combinedReady, cached, _physical⟩ := ready combined rfl
  have accepted : SourceEqualityMkEdgeAllocation.accepted
      (SourceEqualityConjoinAllocation.readback combined) left.children.length = true := by
    change SourceEqualityIntersectionEdgeAllocation.Branch.ready
      (SourceEqualityConjoinAllocation.readback combined) = _ at sourceSame
    unfold SourceEqualityIntersectionEdgeAllocation.source at sourceSame
    split at sourceSame
    next _mismatch => cases sourceSame
    next _matched =>
      dsimp only at sourceSame
      split at sourceSame
      next kept =>
        have readbackSame := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj sourceSame
        rw [readbackSame]
        exact kept
      next _rejected => cases sourceSame
  have fits : SourceEqualityMkEdgeAllocation.fits left.children.length
      (SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback combined)) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory
        (SourceEqualityConjoinAllocation.readback combined) = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using accepted
  obtain ⟨classes, source, rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact
    left.children.length (SourceCompactGuards.sourceEqualities
      (SourceEqualityConjoinAllocation.readback combined))).mp fits
  obtain ⟨canonicalProjection, validTries, pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete
      (SourceEqualityConjoinAllocation.readback combined) cached)
  obtain ⟨values, after, trace, built, symbolSame, guardSame, childrenSame, lengthSame⟩ :=
    SourceEqualityNativeCheckedCode.children_readback nodes edges calls domain left right combined
      state valid known leftResident rightResident sameArity result final done
  rw [guardSame] at projected
  have projectionSame := Option.some.inj (canonicalProjection.symm.trans projected)
  have triesSame : EnumerationEquality.readClasses classes = tries := congrArg Prod.fst projectionSame
  refine ⟨values, after, trace, built, symbolSame, guardSame, childrenSame, lengthSame, ?_, ?_⟩
  · rw [← triesSame]
    exact validTries
  · intro start
    rw [← triesSame, lengthSame]
    apply (fresh_arity_iff left.children.length start (EnumerationEquality.readClasses classes)).mpr
    intro trie member index suffix path
    obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp member
    subst trie
    exact rootBounds paths pathsMember (index :: suffix)
      ((pathReadback paths pathsMember (index :: suffix)).mp path)

end MicroCFTA.SourcePruningEnumerationCheckedWorkerArity
