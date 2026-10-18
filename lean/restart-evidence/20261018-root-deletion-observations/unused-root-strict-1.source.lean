import MicroCFTA.SourceCurrentStoredRootDeletionErasure
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeRequestWinner
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution

/-!
# Root deletion for actual smart-unused source binders

The actual history gives exact unused readback through the current probe.
The root observation then reduces to the actual strict body call. It needs
no assumed parametric payload contract. A completed source call remains
explicit. The theorem does not establish general source comparison.
-/
namespace MicroCFTA.SourceCurrentNativeUnusedRootDeletion
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredRootDeletion (deleted)

/-- Actual smart-unused return observations reduce to the current strict body with combined root cuts. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before environment) (earlier : History empty before)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build (.binder true expression) environment before = .done value after) :
    ∃ depth afterDepth ordinary cut raw afterRaw,
      callback expression environment .depth before = .done depth afterDepth ∧
      callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      InternedFreshOrdinaryConstruction.build expression
        (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw after ∧ Extends afterRaw.nodes.issued after.nodes.issued ∧
      (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
        ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
          Equivalent (deleted cuts value assignment)
            (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw assignment)) := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,
      depthDone,ordinaryDone,requestDone,depthContext,_cutContext,afterContext,
      rawDone,filterDone,rawContext,growth,issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true expression environment before value after context actual
  obtain ⟨selected,present,finished⟩ := SourceCurrentNativeRequestWinner.winner true depth ordinary
    (callback expression environment) cut value after requestDone
  obtain ⟨entry,body,rfl⟩ := InternedProfileHeap.stored_probes depth ordinary selected after
    afterContext.base.normal.facts depthAvailable ordinaryAvailable present
  obtain ⟨path⟩ := SourceCurrentNativeMuPublication.build_history (.binder true expression) environment before context
  have afterHistory : History empty after := .trans earlier (by simpa only [actual,Outcome.state] using path)
  have localContext := depthContext.local (.uninterned (ordinaryLevel depth))
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))
  have rawAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ afterDepth
    localContext.base.normal.facts localContext.base.inputs).result raw afterRaw rawDone
  refine ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,
    depthDone,ordinaryDone,rawDone,filterDone,growth,issued,?_⟩
  intro unused cuts assignment
  have exactReturn := SourceCurrentNativeNormalizedComparisonExecution.history_unused after afterHistory
    (muKey depth ordinary) entry body depth ordinary present unused
  have reduced := SourceCurrentStoredRootDeletionErasure.erased_filter cuts
    (.uninterned (ordinaryLevel depth)) raw assignment afterRaw rawContext.base.normal rawAvailable
  rw [filterDone] at reduced
  rw [finished,exactReturn]
  exact reduced

end MicroCFTA.SourceCurrentNativeUnusedRootDeletion
