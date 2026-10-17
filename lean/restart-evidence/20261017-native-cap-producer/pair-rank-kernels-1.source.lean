import MicroCFTA.SourceCurrentConstrainedCapNativePairRank

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.PairRankChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
variable {Symbol Guard : Type}

/-- Actual ordinary children derive their source coverage and cannot repeat the sorted ancestor identity pair. -/
theorem ordinary_children_excluded (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (firstEntry secondEntry : Interned NodeKey) (firstRows secondRows : List (EdgeValue Symbol Guard))
    (firstLevel secondLevel : Nat) (firstFree secondFree : List Reference)
    (firstAvailable : Available source (.node firstEntry firstRows firstLevel firstFree))
    (secondAvailable : Available source (.node secondEntry secondRows secondLevel secondFree))
    (firstCovered : Covered domain (.node firstEntry firstRows firstLevel firstFree))
    (secondCovered : Covered domain (.node secondEntry secondRows secondLevel secondFree))
    (nonplain : ¬ Annotated annotation (.node firstEntry firstRows firstLevel firstFree) ∨
      ¬ Annotated annotation (.node secondEntry secondRows secondLevel secondFree))
    (first second : EdgeValue Symbol Guard) (firstMember : first ∈ firstRows) (secondMember : second ∈ secondRows)
    (children : Value Symbol Guard × Value Symbol Guard) (member : children ∈ first.children.zip second.children)
    (leftNumber rightNumber : Nat)
    (leftId : identity children.1 = some leftNumber) (rightId : identity children.2 = some rightNumber) :
    pairRank annotation children.1 children.2 < pairRank annotation (.node firstEntry firstRows firstLevel firstFree)
        (.node secondEntry secondRows secondLevel secondFree) ∧
      pair leftNumber rightNumber ≠ pair firstEntry.identity secondEntry.identity := by
  have inside := List.of_mem_zip member
  have childAvailable : Available source children.1 := firstAvailable.children _ (List.mem_flatMap.mpr ⟨first, firstMember, inside.1⟩)
  have otherAvailable : Available source children.2 := secondAvailable.children _ (List.mem_flatMap.mpr ⟨second, secondMember, inside.2⟩)
  have childCovered := Covered.node_child source facts domain firstEntry firstRows firstLevel firstFree firstAvailable firstCovered first firstMember children.1 inside.1
  have otherCovered := Covered.node_child source facts domain secondEntry secondRows secondLevel secondFree secondAvailable secondCovered second secondMember children.2 inside.2
  have smaller := SourceCurrentConstrainedCapNonplainRank.zip_pair_lt annotation
    (.node firstEntry firstRows firstLevel firstFree) (.node secondEntry secondRows secondLevel secondFree)
    nonplain first second firstMember secondMember children member
  exact ⟨smaller, SourceCurrentConstrainedCapNativePairRank.strict_pair_ne annotation source facts domain bindings
    children.1 children.2 (.node firstEntry firstRows firstLevel firstFree) (.node secondEntry secondRows secondLevel secondFree)
    childAvailable otherAvailable firstAvailable secondAvailable childCovered otherCovered firstCovered secondCovered
    leftNumber rightNumber firstEntry.identity secondEntry.identity leftId rightId rfl rfl smaller⟩

end MicroCFTA.PairRankChecks

#print axioms MicroCFTA.PairRankChecks.ordinary_children_excluded
#check @MicroCFTA.PairRankChecks.ordinary_children_excluded
