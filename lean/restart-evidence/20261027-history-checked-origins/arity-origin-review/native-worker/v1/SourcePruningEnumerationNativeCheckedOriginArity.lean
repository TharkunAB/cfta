import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.SourceEqualityNativeDemandAcceptedReceipt
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance

/-!
# Projected arity of actual checked native edge returns

The ready prefix derives its own guard check.
The accepted worker retains its actual ordered child walk and returned state.
The sentinel retains its complete original constructor receipt.
These results do not infer origins for every edge in a current Packet.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open EnumerationState EnumerationCorrectness
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- The actual ready result derives projected arity at its checked incoming child count. -/
theorem ready_fits
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second combined : Allocated) (leftArity rightArity : Nat)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (firstReady : SourceEqualityConstraintAllocation.Ready operations.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready operations.constraints second.stored)
    (observed : (SourceEqualityIntersectionEdgeAllocation.run le first second
      leftArity rightArity operations).1 = .ok (.ready combined)) :
    SourcePruningEnumerationArityOrigins.Fits (SourceEqualityConjoinAllocation.readback combined) leftArity := by
  obtain ⟨branch, literal, sourceSame, _prefixValid, _growth, ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second leftArity rightArity
      operations valid firstReady secondReady
  have branchSame : branch = .ready combined := Except.ok.inj (literal.symm.trans observed)
  subst branch
  obtain ⟨_combinedReady, cached, _physical⟩ := ready combined rfl
  have accepted : SourceEqualityMkEdgeAllocation.accepted
      (SourceEqualityConjoinAllocation.readback combined) leftArity = true := by
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
  have fits : SourceEqualityMkEdgeAllocation.fits leftArity
      (SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback combined)) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory
        (SourceEqualityConjoinAllocation.readback combined) = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using accepted
  obtain ⟨classes, source, rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact leftArity
    (SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback combined))).mp fits
  obtain ⟨canonicalProjection, _validTries, pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete
      (SourceEqualityConjoinAllocation.readback combined) cached)
  intro tries residual projected start
  have triesSame : EnumerationEquality.readClasses classes = tries :=
    congrArg Prod.fst (Option.some.inj (canonicalProjection.symm.trans projected))
  rw [← triesSame]
  apply (fresh_arity_iff leftArity start (EnumerationEquality.readClasses classes)).mpr
  intro trie member index suffix path
  obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp member
  subst trie
  exact rootBounds paths pathsMember (index :: suffix)
    ((pathReadback paths pathsMember (index :: suffix)).mp path)

/-- The actual sentinel retains every original receipt field and derives its empty own projection. -/
theorem sentinel_provenance [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol)
    (heap : InternedConstructorTemplates.State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready heap) :
    let built := InternedConstructorTemplates.run (makeEdge symbol top [.empty]) heap
    SourceEqualityRequiredCache.Keeps heap built.2 ∧ EdgeResident built.2 built.1 ∧
      built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = top ∧ built.1.children = [.empty] ∧
      (∀ holds ambient term, ¬ InternedGuardedLanguage.edgeMeaning holds ambient built.1 term) ∧
      SourcePruningEnumerationArityOrigins.Fits built.1.entry.key.constraint built.1.children.length := by
  obtain ⟨keeps, resident, symbolSame, guardSame, childrenSame, rejects⟩ :=
    SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance symbol heap ready
  refine ⟨keeps, resident, symbolSame, guardSame, childrenSame, rejects, ?_⟩
  intro tries residual projected start
  rw [guardSame] at projected
  have topProjection : SourcePruningEnumerationConstraint.project (top : Guard) = some ([], none) := rfl
  rw [topProjection] at projected
  have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
  subst tries
  rfl

/-- Actual child receipts retain the full original accepted result and derive its fresh own arity. -/
theorem accepted_body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state after : State width)
    (first second combined : Allocated) (values : List (Value Symbol Guard)) (fuel : Nat)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (walk : SourceEqualityNativeDemandChildWalk.Walk (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children)
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2} values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
    let final : State width := {after with native := advance after.native {after.native.machine with heap := built.2}}
    execute (fuel + 3) (.edgeBody request .pure) state = .done built.1 final ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) final.native.machine request built.1 ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap final.native.machine.heap ∧
      EdgeResident final.native.machine.heap built.1 ∧ built.1.children = values ∧ built.1.children.length = request.left.children.length ∧
      SourcePruningEnumerationArityOrigins.Fits built.1.entry.key.constraint built.1.children.length := by
  have original := SourceEqualityNativeDemandAcceptedReceipt.body_produced formulas solver request state after
    first second combined values fuel valid heapReady inputs leftCached rightCached arity symbols left right accepted walk
  have childEffects := walk.effects heapReady
  have fields := MergedPhysicalGroupEdges.makeEdge_fields after.native.machine.heap
    childEffects.1.ready.semantic.1.normal.facts request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values childEffects.2.2.1
  obtain ⟨firstReady, _firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    valid.constraints leftCached first left
  obtain ⟨secondReady, _secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    valid.constraints rightCached second right
  have checked := ready_fits GuardStructuralOrder.le first second combined
    request.left.children.length request.right.children.length state.operations valid firstReady secondReady accepted
  refine ⟨original.1, original.2.1, original.2.2.1, original.2.2.2.1,
    original.2.2.2.2.1, original.2.2.2.2.2, ?_⟩
  rw [fields.2.1, original.2.2.2.2.2]
  exact checked

end MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
