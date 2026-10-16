import MicroCFTA.SourceRecursiveIntersectionSourceInventory

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.SourceInventoryIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionDomainInventory
variable {Symbol Guard : Type}

/-- Literal domain entry derives its exact child-body scope and static-source word check. -/
theorem actual_enter_body (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (nodes : source.nodes.next < 2 ^ bits)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache)
    (domain : Interned DomainKey) (member : domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains source)
    (left right : Value Symbol Guard) (scope : NodeScope source ⟨domain, left, right⟩)
    (first second : Nat) (leftId : SourceRecursiveIntersectionControl.identity left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity right = some second)
    (room : (SourceRecursiveIntersectionEnvironment.enter cache domain.key left right first second).1.identity < 2 ^ (bits + 1)) :
    let entered := (SourceRecursiveIntersectionEnvironment.enter cache domain.key left right first second).1
    entered.key ∈ SourceRecursiveIntersectionSourceInventory.domains source ∧
      Canonical entered.key ∧ SourceRecursiveIntersectionDomain.Typed entered.key ∧
      NodeScope source ⟨entered, SourceRecursiveIntersectionKernel.body left, SourceRecursiveIntersectionKernel.body right⟩ ∧
      ∀ key, SourceRecursiveIntersectionMemo.requestKey (bits + 2) entered
        (SourceRecursiveIntersectionKernel.body left) (SourceRecursiveIntersectionKernel.body right) = some key →
        SourceRecursiveIntersectionMemo.KeySafe (bits + 2) entered
          (SourceRecursiveIntersectionKernel.body left) (SourceRecursiveIntersectionKernel.body right) := by
  let entered := (SourceRecursiveIntersectionEnvironment.enter cache domain.key left right first second).1
  have exactKey : entered.key = SourceRecursiveIntersectionDomain.extend domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second) :=
    (IntersectionEmptyDomain.make_correct cache valid _).2.1
  have inside := SourceRecursiveIntersectionSourceInventory.entered_mem source facts cache valid domain member left right
    scope.leftAvailable scope.rightAvailable first second leftId rightId
  have supported := supported_of_mem inside
  have childScope := scope.mu source domain entered left right first second exactKey
  exact ⟨inside, supported.canonical, supported.typed, childScope,
    SourceRecursiveIntersectionSourceInventory.node_key_safe bits source facts nodes _ childScope room⟩

/-- Interned references use their actual initial issued reservation. -/
theorem actual_reference_name (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (name : Nat) (available : Available source (.reference (.interned name))) :
    name ∈ SourceRecursiveIntersectionSourceInventory.names source :=
  SourceRecursiveIntersectionSourceInventory.identity_mem source facts (.reference (.interned name)) available name rfl

/-- The all-issued range is a conservative bound that is already too large at eight identities. -/
theorem coarse_eight_inventory (source : InternedConstructorTemplates.State Symbol Guard)
    (issued : source.nodes.next = 8) :
    (SourceRecursiveIntersectionSourceInventory.domains source).length = 2 ^ 72 ∧
      2 ^ 63 < (SourceRecursiveIntersectionSourceInventory.domains source).length := by
  rw [SourceRecursiveIntersectionSourceInventory.domains_length, issued]
  constructor
  · rfl
  · decide

#print axioms actual_enter_body
#check @actual_enter_body
#print axioms actual_reference_name
#check @actual_reference_name
#print axioms coarse_eight_inventory
#check @coarse_eight_inventory
end MicroCFTA.SourceInventoryIndependentChecks
