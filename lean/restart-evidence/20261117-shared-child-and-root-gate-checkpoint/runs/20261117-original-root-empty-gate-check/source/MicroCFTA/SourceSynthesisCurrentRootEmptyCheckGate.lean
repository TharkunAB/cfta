import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceCurrentHereditaryUnconstrained
import MicroCFTA.SourceEndpointReachability

namespace MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/-!
Note [The raw root gate reads stored universe bodies]
The endpoint check stops at each Mu. It does not read either stored probe.
Every Mu retained by the accepted raw construction has the original universe
body. Its rows have Top guards. Its children are the nullary marker or the
original recursive reference. These facts make the literal visited fold true.
Availability carries this fact to each Mu that the endpoint check can reach.
This proof concerns the raw construction. It does not cover later reduction
or refolding. A false gate does not establish finite inhabitance.
-/

private theorem original_stored_mu_unconstrained
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : InternedBinderProtocol.NodeKey)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    SourceMemoGate.unconstrained (.mu entry body depth ordinary) = true := by
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, markerShape, _arrowChildren,
      _arrowKey, _catalog, _markerClosed, _markerAvailable, kinds, _retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built
      key entry body depth ordinary stored
  obtain ⟨markerEntry, markerRow, markerEq, markerLeaf, markerKey⟩ := markerShape
  have topPlain : SourceMemoGate.plain SourceSynthesisGeneralizeSyntax.top = true := rfl
  have markerPlain : Annotated (fun guard => SourceMemoGate.plain guard = true) marker := by
    rw [markerEq]
    refine .node markerEntry [markerRow] 0 [] ?_ ?_
    · intro edge member
      have same := List.mem_singleton.mp member
      cases same
      rw [markerKey]
      exact topPlain
    · intro child member
      obtain ⟨row, rowMember, childMember⟩ := List.mem_flatMap.mp member
      have same := List.mem_singleton.mp rowMember
      cases same
      rw [markerLeaf] at childMember
      cases childMember
  have bodyPlain : Annotated (fun guard => SourceMemoGate.plain guard = true) body := by
    rw [bodyEq]
    refine .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] ?_ ?_
    · intro row member
      rw [(kinds row member).1]
      exact topPlain
    · intro child member
      obtain ⟨row, selected, included⟩ := List.mem_flatMap.mp member
      rcases (kinds row selected).2 child included with same | same
      · rw [same]
        exact markerPlain
      · rw [same]
        exact .reference _
  exact SourceCurrentHereditaryUnconstrained.unconstrained
    (.mu entry body depth ordinary) (.mu entry body depth ordinary bodyPlain)

/-- The accepted original raw root disables the outer constrained-Mu gate. -/
theorem original_root_reaches_constrained_mu_false
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap) :
    SourceEndpointReachability.reaches SourceMemoGate.unconstrained rootValue = false := by
  have impossible : ∀ value, SourceEndpointReachability.Witness SourceMemoGate.unconstrained value →
      Available sourceHeap value → False := by
    intro value witness
    induction witness with
    | @binder entry body depth ordinary constrained =>
        intro available
        have plain := original_stored_mu_unconstrained lib query signed whole accepted
          rootValue sourceHeap built entry.key entry body depth ordinary
          (available.resident entry rfl)
        rw [plain] at constrained
        cases constrained
    | union _nested member _next ih =>
        intro available
        exact ih (available.children _ member)
    | node _nested rowMember childMember _next ih =>
        intro available
        exact ih (available.children _ (List.mem_flatMap.mpr ⟨_, rowMember, childMember⟩))
  have available : Available sourceHeap rootValue :=
    (InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)).result
      rootValue sourceHeap built
  cases answer : SourceEndpointReachability.reaches SourceMemoGate.unconstrained rootValue with
  | false => rfl
  | true =>
      exact False.elim (impossible rootValue
        ((SourceEndpointReachability.reaches_iff SourceMemoGate.unconstrained rootValue).mp answer)
        available)

end MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate

#check MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate.original_root_reaches_constrained_mu_false
#print axioms MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate.original_root_reaches_constrained_mu_false
