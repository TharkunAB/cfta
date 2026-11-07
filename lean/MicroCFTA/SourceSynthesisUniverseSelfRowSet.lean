import MicroCFTA.SourceSynthesisUniverseRowTransform

/-!
# Actual source self rows inside the replayed body product

Every original row occurs in its self pair in the real hash join.
Literal replay identifies that pair's result in the actual product list.
The checked self-row execution derives its substitution readback and live
children. Its actual edge constructor then replays in the final machine.
The ordered target list retains every source occurrence and duplicate.
This internal theorem consumes the replay derived by BodyWalkReplay.
-/
namespace MicroCFTA.SourceSynthesisUniverseSelfRowSet
open Cache Language InternedConstructorTemplates InternedBinderProtocol
open InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseRowTransform (Readback)

variable {Symbol Guard : Type}

private theorem aligned_input {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    ∀ input ∈ inputs, ∃ output ∈ outputs, relation input output := by
  induction aligned with
  | nil => intro input member; cases member
  | @cons input output inputs outputs own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨output, List.mem_cons_self, own⟩
      · obtain ⟨target, present, related⟩ := ih selected later
        exact ⟨target, List.mem_cons_of_mem _ present, related⟩

/-- Derived product replay supplies every live target and its actual source-ordered constructor replay. -/
theorem from_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (domain : Interned DomainKey) (uId : Nat) (markerEntry : Interned NodeKey)
    (markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (bodyRows products : List (EdgeValue Symbol Guard)) (final : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid final)
    (markerAvailable : Available final.heap (.node markerEntry markerRows markerDepth []))
    (seen : pair uId uId ∈ domain.key.seen)
    (tops : ∀ source ∈ bodyRows, source.entry.key.constraint = top)
    (shapes : ∀ source ∈ bodyRows, source.children =
        [.node markerEntry markerRows markerDepth [], .reference (.interned uId), .reference (.interned uId)] ∨
      ∃ arity, source.children = List.replicate arity (.reference (.interned uId)))
    (productResident : ∀ row ∈ products, EdgeResident final.heap row)
    (replayed : All₂ (fun (matched : EdgeValue Symbol Guard × EdgeValue Symbol Guard) row =>
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) matched.1 matched.2 final = .done row final)
      (pairs bodyRows bodyRows) products) :
    ∃ targets,
      All₂ (Readback top uId) bodyRows targets ∧
      All₂ (fun (source : EdgeValue Symbol Guard) target => SourceRecursiveIntersectionKernel.work
        (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) final =
          .done target final) bodyRows targets ∧
      (∀ target ∈ targets, target ∈ products) ∧
      (∀ target ∈ targets, EdgeResident final.heap target) ∧
      (∀ target ∈ targets, EqualityLeafProjectionPhysical.dead target = false) ∧
      walk (fun source => SourceRecursiveIntersectionKernel.work
        (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)))
        bodyRows final = .done targets final := by
  have each : ∀ source ∈ bodyRows, ∃ target ∈ products,
      Readback top uId source target ∧ EqualityLeafProjectionPhysical.dead target = false ∧
      SourceRecursiveIntersectionKernel.work
        (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) final =
          .done target final := by
    intro source member
    have selfMember : (source, source) ∈ pairs bodyRows bodyRows :=
      (pairs_member bodyRows bodyRows (source, source)).mpr ⟨member, member, rfl⟩
    obtain ⟨target, targetIn, returned⟩ := aligned_input replayed (source, source) selfMember
    obtain ⟨result, after, completed, _, _, _, readback, live⟩ :=
      SourceSynthesisUniverseRowTransform.edge_self_complete emptyGuard top conjoin conjoinTop domain uId
        markerEntry markerRows markerDepth source final valid markerAvailable (tops source member) seen (shapes source member)
    have same := (Result.done.inj (completed.symm.trans returned)).1
    have pure := (SourceSynthesisUniverseRowTransform.edge_self_work emptyGuard top conjoin conjoinTop domain uId
      markerEntry markerRows markerDepth source final (tops source member) seen (shapes source member)).symm.trans returned
    exact ⟨target, targetIn, same ▸ readback, same ▸ live, pure⟩
  have gather (sources : List (EdgeValue Symbol Guard)) :
      (∀ source ∈ sources, source ∈ bodyRows) →
      ∃ targets,
        All₂ (Readback top uId) sources targets ∧
        All₂ (fun (source : EdgeValue Symbol Guard) target => SourceRecursiveIntersectionKernel.work
          (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) final =
            .done target final) sources targets ∧
        (∀ target ∈ targets, target ∈ products) ∧
        (∀ target ∈ targets, EqualityLeafProjectionPhysical.dead target = false) ∧
        walk (fun source => SourceRecursiveIntersectionKernel.work
          (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)))
          sources final = .done targets final := by
    induction sources with
    | nil =>
        intro _
        exact ⟨[], .nil, .nil, (by intro target member; cases member),
          (by intro target member; cases member), rfl⟩
    | cons source sources ih =>
        intro included
        obtain ⟨target, targetIn, readback, live, pure⟩ := each source (included source List.mem_cons_self)
        obtain ⟨targets, aligned, pureRows, retained, liveRows, walked⟩ :=
          ih (fun other member => included other (List.mem_cons_of_mem _ member))
        refine ⟨target :: targets, .cons readback aligned, .cons pure pureRows, ?_, ?_, ?_⟩
        · intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact targetIn
          · exact retained other later
        · intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact live
          · exact liveRows other later
        · simp only [walk, pure, Result.bind, walked]
  obtain ⟨targets, aligned, pureRows, retained, liveRows, walked⟩ := gather bodyRows (fun _ member => member)
  exact ⟨targets, aligned, pureRows, retained, fun target member => productResident target (retained target member),
    liveRows, walked⟩

end MicroCFTA.SourceSynthesisUniverseSelfRowSet
