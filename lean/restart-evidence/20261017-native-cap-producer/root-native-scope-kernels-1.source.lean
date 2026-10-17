import MicroCFTA.SourceCurrentConstrainedCapNativePairWeight
import MicroCFTA.SourceRecursiveIntersectionCompile

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeScopeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
variable {Symbol Guard : Type}

/-- Closed initial inputs produce covered actual entry and every later annotated source read. -/
theorem entered_reads (annotation : Guard → Prop) (depth : Nat)
    (source current : State Symbol Guard) (facts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat) :
    let actual := SourceRecursiveIntersectionEnvironment.enter cache IntersectionEmptyDomain.emptyDomain.key left right first second
    SourceCurrentConstrainedCapNativeCoverage.Bindings annotation source actual.1.key ∧
      Covered actual.1.key (body left) ∧ Covered actual.1.key (body right) ∧
      ∀ name ∈ SourceRecursiveIntersectionDomain.names actual.1.key,
        ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
          Available current value ∧ value.referenceOf = .mu name ∧
          SourceEqualityAnnotationLanguage.Annotated annotation value ∧ Covered actual.1.key value := by
  let actual := SourceRecursiveIntersectionEnvironment.enter cache IntersectionEmptyDomain.emptyDomain.key left right first second
  have entered := SourceCurrentConstrainedCapNativeCoverage.enter annotation depth source IntersectionEmptyDomain.emptyDomain.key
    (SourceCurrentConstrainedCapNativeCoverage.empty annotation source) left right leftAvailable rightAvailable leftCap rightCap
    (Covered.closed _ left leftClosed) (Covered.closed _ right rightClosed) cache valid first second
  refine ⟨entered.1, entered.2.1, entered.2.2, ?_⟩
  intro name member
  exact SourceCurrentConstrainedCapNativeCoverage.Bindings.read annotation source current facts growth history
    actual.1.key entered.1 name member

/-- The literal repeated branch produces its own cap and exact source-ranked occurrence certificate. -/
theorem repeated_producer [DecidableEq Symbol]
    (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard)
    (bindings : SourceCurrentHereditaryNativeScope.Bindings annotation source request.domain.key)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftCovered : Covered request.domain.key request.left) (rightCovered : Covered request.domain.key request.right)
    (first second : Nat) (leftId : identity request.left = some first) (rightId : identity request.right = some second)
    (selected : decision request.domain.key request.left request.right = .repeated (pair first second)) :
    compileNode request = .pure (repeatedValue (pair first second)) ∧
      Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) (repeatedValue (pair first second)) ∧
      ∀ depth, Cap annotation depth (repeatedValue (pair first second)) := by
  have weight := SourceCurrentConstrainedCapNativePairWeight.pair_weight annotation source facts request.domain.key bindings
    request.left request.right leftAvailable rightAvailable leftCovered rightCovered first second leftId rightId
  refine ⟨by simp only [compileNode, selected], ?_, fun depth => .plain depth (.reference _)⟩
  apply SourceCurrentConstrainedCapPairOccurrences.reference
  exact Nat.le_of_eq weight

#print axioms entered_reads
#check @entered_reads
#print axioms repeated_producer
#check @repeated_producer
end MicroCFTA.NativeScopeKernels
