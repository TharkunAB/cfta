import MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw
import MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries

/-!
# Actual source cutoffs from the fixed pure query law

Both original source entry chains retain their exact terminal requests.
The pure law supplies the warm cutoff clause at the actual returned cells.
The original query retains its full endpoint and captured continuation.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePureQueryLaw (PureResult)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The original source terminal queries consume the same global pure returned law. -/
theorem current_stored_universe_auxiliary_pure_cutoff_queries
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (_patternAvailable : Available heap pattern)
    (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        body universeValue bodyEntry.identity entry.identity
      let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (request : NodeRequest Symbol Guard) (cutoff : Nat × Nat),
        ((request = ⟨bodyTerminal.1, body, referenceValue⟩ ∧ cutoff = pair bodyEntry.identity entry.identity) ∨
          (request = ⟨diagonalTerminal.1, referenceValue, referenceValue⟩ ∧
            cutoff = pair entry.identity entry.identity)) →
        decision request.domain.key request.left request.right = .repeated cutoff ∧
        compileNode request = .pure (repeatedValue cutoff) ∧
        ∀ (Output : Type) (next : Value Symbol Guard → Code Symbol Guard Output)
          (before after : Checked width) (fuel : Nat) (value : Output),
          SourceCurrentAllocatedNativePhysicalCache.Valid before.native →
          NodeReady before.native.machine request →
          (∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
            SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) →
          Returned PureResult before.native.nodes →
          execute fuel (.code (.node request next)) before = .done value after →
          ∃ (total inner outer : Nat) (middle : Checked width),
            total < fuel ∧ inner + outer = total ∧
            Steps inner (.code (requestNode request.domain request.left request.right)) before
              (.code (.pure (repeatedValue cutoff))) middle ∧
            Steps outer (.code (next (repeatedValue cutoff))) middle (.code (.pure value)) after := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, sourceQueries⟩ :=
    SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only at sourceQueries ⊢
  intro request cutoff sourceCase
  obtain ⟨selected, compiled, nativeQuery⟩ := sourceQueries request cutoff sourceCase
  refine ⟨selected, compiled, ?_⟩
  intro Output next before after fuel value physical ready safe returned done
  exact nativeQuery Output next before after fuel value physical ready safe
    (SourceCurrentAllocatedNativePureQueryLaw.returned_expected
      request before (repeatedValue cutoff) compiled returned) done

end MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries

#check @MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries.current_stored_universe_auxiliary_pure_cutoff_queries
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries.current_stored_universe_auxiliary_pure_cutoff_queries
