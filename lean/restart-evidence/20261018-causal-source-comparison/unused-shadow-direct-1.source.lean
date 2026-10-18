import MicroCFTA.SourceCurrentNativeReaderUnusedRootDeletion
import MicroCFTA.SourceCurrentStoredMuProfileContract

/-!
# A common local profile for actual smart-unused returns

The selected historical winner gives exact unused return erasure. The
current ordinary callback excludes its local name from that return.
Changing the assigned local profile therefore leaves every root deletion
unchanged. The strict raw body can use an Empty local profile.
-/
namespace MicroCFTA.SourceCurrentNativeUnusedRootShadow
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredMuProfileContract (shadow)

/-- Actual unused returns ignore the ordinary local profile and use Empty in the strict body observer. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build (.binder true expression) environment before = .done value after)
    (reader : State Symbol Guard) (later : Grows after reader) (history : History empty reader) :
    ∃ depth afterDepth ordinary cut raw afterRaw,
      callback expression environment .depth before = .done depth afterDepth ∧
      callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      InternedFreshOrdinaryConstruction.build expression
        (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw after ∧ Extends afterRaw.nodes.issued after.nodes.issued ∧
      (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
        .uninterned (ordinaryLevel depth) ∉ value.free ∧
        (∀ (cuts : Reference → Bool) (assignment : Reference → Profile) (replacement : Profile),
          deleted cuts value assignment =
            deleted cuts value (shadow (.uninterned (ordinaryLevel depth)) replacement assignment)) ∧
        ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
          Equivalent (deleted cuts value assignment)
            (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw
              (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment))) := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,
      depthDone,ordinaryDone,requestDone,depthContext,_cutContext,afterContext,
      rawDone,filterDone,_rawContext,growth,issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true expression environment before value after context actual
  obtain ⟨otherDepth,otherAfterDepth,otherOrdinary,otherCut,otherRaw,otherAfterRaw,
      otherDepthDone,otherOrdinaryDone,otherRawDone,_otherFilter,_otherGrowth,_otherIssued,reduced⟩ :=
    SourceCurrentNativeReaderUnusedRootDeletion.build expression environment before context value after actual reader later history
  have sameDepth := Outcome.done.inj (depthDone.symm.trans otherDepthDone)
  cases sameDepth.1
  cases sameDepth.2
  have sameOrdinary := Outcome.done.inj (ordinaryDone.symm.trans otherOrdinaryDone)
  cases sameOrdinary.1
  cases sameOrdinary.2
  have sameRaw := Outcome.done.inj (rawDone.symm.trans otherRawDone)
  cases sameRaw.1
  cases sameRaw.2
  obtain ⟨selected,present,finished⟩ := SourceCurrentNativeRequestWinner.winner true depth ordinary
    (callback expression environment) cut value after requestDone
  obtain ⟨entry,body,rfl⟩ := InternedProfileHeap.stored_probes depth ordinary selected after
    afterContext.base.normal.facts depthAvailable ordinaryAvailable present
  refine ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,
    depthDone,ordinaryDone,rawDone,filterDone,growth,issued,?_⟩
  intro unused
  have exactReturn := finished.trans (SourceCurrentNativeNormalizedComparisonExecution.history_unused reader history
    (muKey depth ordinary) entry body depth ordinary (later.nodeRecords _ _ present) unused)
  have noDeep : .uninterned (ordinaryLevel depth) ∉ InternedDeepFreeDepth.deepNames ordinary := by
    simpa only [InternedFreshOrdinaryDepthHeap.usesLocal,decide_eq_false_iff_not] using unused
  have erased := SourceCurrentNativeCallbackErasure.callback_result expression environment
    (.uninterned (ordinaryLevel depth)) afterDepth depthContext.base
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth)) ordinary cut ordinaryDone noDeep
  have available : Available cut value := by rw [exactReturn]; exact erased.2.1
  have missing : .uninterned (ordinaryLevel depth) ∉ value.free := by rw [exactReturn]; exact erased.2.2
  have shadowed : ∀ (cuts : Reference → Bool) (assignment : Reference → Profile) (replacement : Profile),
      deleted cuts value assignment =
        deleted cuts value (shadow (.uninterned (ordinaryLevel depth)) replacement assignment) := by
    intro cuts assignment replacement
    apply SourceCurrentStoredRootDeletion.congr value cut erased.1.normal.facts.coherent available
      cuts cuts assignment _ (fun _ _ => rfl)
    intro name member
    have different : name ≠ .uninterned (ordinaryLevel depth) := fun same => missing (same ▸ member)
    simp only [shadow,if_neg different]
  refine ⟨missing,shadowed,?_⟩
  intro cuts assignment
  have compared := reduced unused cuts (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)
  rw [← shadowed cuts assignment (some [])] at compared
  exact compared

end MicroCFTA.SourceCurrentNativeUnusedRootShadow
