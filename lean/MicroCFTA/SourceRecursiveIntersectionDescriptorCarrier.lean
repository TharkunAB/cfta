import MicroCFTA.SourceRecursiveIntersectionDomain
import MicroCFTA.SourceRecursiveIntersectionMuInventoryName
import Init.Data.List.Lemmas

namespace MicroCFTA.SourceRecursiveIntersectionDomain

/-- Builds descriptor choices from the initial inventory. -/
def originalDescriptorCarrier {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard) :
    List MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey :=
  let inputs := MicroCFTA.SourceRecursiveIntersectionInputView.inventory state
  let pairs := inputs.flatMap fun left =>
    inputs.map fun right => MicroCFTA.IntersectSchedule.pair left right
  let empty : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey := ⟨[], []⟩
  let anchor := MicroCFTA.IntersectSchedule.pair
    MicroCFTA.IntersectSchedule.Input.empty MicroCFTA.IntersectSchedule.Input.empty
  let pairChoices := List.foldr
    (fun pair keys => keys ++ keys.map (fun key => extend key [] pair))
    [empty] pairs
  List.foldr
    (fun name keys => keys ++ keys.map (fun key =>
      MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
        (extend key [name] anchor).free key.seen))
    pairChoices (List.range state.nodes.next)

end MicroCFTA.SourceRecursiveIntersectionDomain
