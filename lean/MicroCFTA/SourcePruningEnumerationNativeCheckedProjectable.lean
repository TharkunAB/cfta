import MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
import MicroCFTA.SourcePruningEnumerationCheckedArity

/-!
# Projection from actual checked edge results

The allocated intersection checks the combined guard before child work.
Its ready result supplies a successful own-constraint projection.
Both checked constructor outcomes also supply that projection.
These results do not give checked history to arbitrary resident rows.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeCheckedProjectable
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "readback" => SourceEqualityConjoinAllocation.readback
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- The actual ready gate supplies its accepted guard and canonical own projection. -/
theorem ready_projectable
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second combined : Allocated) (leftArity rightArity : Nat)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (firstReady : SourceEqualityConstraintAllocation.Ready operations.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready operations.constraints second.stored)
    (observed : (SourceEqualityIntersectionEdgeAllocation.run le first second
      leftArity rightArity operations).1 = .ok (.ready combined)) :
    SourceEqualityMkEdgeAllocation.accepted (readback combined) leftArity = true ∧
      ∃ classes : EqualityNormalize.Constraints,
        SourceCompactGuards.sourceEqualities (readback combined) = some classes ∧
        SourcePruningEnumerationConstraint.project (readback combined) =
          some (EnumerationEquality.readClasses classes,
            if (SourceCompactGuards.positive (readback combined).guard).isSome
              then none else some (readback combined)) ∧
        (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
        SourcePruningEnumerationArityOrigins.Fits (readback combined) leftArity := by
  obtain ⟨branch, literal, sourceSame, _prefixValid, _growth, ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second leftArity rightArity
      operations valid firstReady secondReady
  have branchSame : branch = .ready combined := Except.ok.inj (literal.symm.trans observed)
  subst branch
  obtain ⟨_combinedReady, cached, _physical⟩ := ready combined rfl
  have accepted : SourceEqualityMkEdgeAllocation.accepted (readback combined) leftArity = true := by
    change SourceEqualityIntersectionEdgeAllocation.Branch.ready (readback combined) = _ at sourceSame
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
  have fits : SourceEqualityMkEdgeAllocation.fits leftArity
      (SourceCompactGuards.sourceEqualities (readback combined)) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory (readback combined) = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using accepted
  obtain ⟨classes, source, _rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact leftArity
    (SourceCompactGuards.sourceEqualities (readback combined))).mp fits
  obtain ⟨projection, validTries, _pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete (readback combined) cached)
  exact ⟨accepted, classes, source, projection, validTries,
    SourcePruningEnumerationNativeCheckedOriginArity.ready_fits le first second combined
      leftArity rightArity operations valid firstReady secondReady observed⟩

/-- Either observed checked constructor return supplies its own projection and bounds. -/
theorem observed_build_projectable [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (original : Guard) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (Value Symbol Guard))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : SourceEqualityMkEdgeAllocation.accepted original children.length = true →
      InternedNestedProvenance.Values heap children)
    (edge : EdgeValue Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (after : InternedConstructorTemplates.State Symbol Guard)
    (observed : SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok edge, operations, after)) :
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive edge.entry.key.constraint.guard).isSome
            then none else some edge.entry.key.constraint) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows edge.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  obtain ⟨_checked, receipt, _operationsValid, _operationsGrowth, _kept, _resident,
    _symbol, _guard, _children, classes, source, projection, validTries,
    _pathReadback, ownArity⟩ :=
    SourcePruningEnumerationCheckedArity.checked_projected_arity symbol original stored children
      before heap cached physical storedReady valid heapReady available
  have edgeSame := Except.ok.inj (congrArg Prod.fst (receipt.symm.trans observed))
  rw [edgeSame] at source projection ownArity
  exact ⟨classes, source, projection, validTries, ownArity⟩

end MicroCFTA.SourcePruningEnumerationNativeCheckedProjectable
