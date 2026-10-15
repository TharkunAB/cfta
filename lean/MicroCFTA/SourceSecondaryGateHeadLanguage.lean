import MicroCFTA.SourceSecondaryGateHead
import MicroCFTA.MergedFreshOrdinaryExposureInputs
import MicroCFTA.MergedFreshOrdinaryGuardedSoundness

/-!
# Accepted terms through actual secondary-gate head reads

The completed source worklist covers every constructor origin in a later
cache that retains its effects. A finite warm head chain supplies such an
origin for each independently accepted term. Closed stopping points use an
actual closed read. No future language or completed-read premise is supplied.
-/
namespace MicroCFTA.SourceSecondaryGateHeadLanguage
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values Edges)
open MergedFreshOrdinaryExposure MergedFreshOrdinaryGraph
open MergedSourceExposure (Result)
open MergedFreshOrdinaryExposureCertificate
open MergedFreshOrdinaryExposureCoverage (origin_terminal origin_single)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open SourceSecondaryGateHead
open InternedGuardedLanguage (meaning)

private theorem collect_resident_fixed [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) (edges : List (EdgeValue Symbol Guard))
    (done : collect fuel state [] pending = .done edges state) : Edges state edges := by
  obtain ⟨found, cert⟩ := collect_certificate fuel state semantic covered [] pending inputs edges done
  intro edge member
  obtain ⟨source, reached, original⟩ := MergedFreshOrdinaryExposureOrigins.collect_origins fuel state
    semantic covered [] pending inputs edges state done state (grows_refl _) edge member
  have available := MergedFreshOrdinaryExposureInputs.Certificate.reachable_available state pending found edges cert source reached
  exact InternedEdgeResidency.resident_edges state semantic.1.normal.facts.linked source available.resident edge original

/-- Completed fixed-cache reads cover every constructor origin, including open roots and identity skips. -/
theorem nodeEdges_covers_fixed [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (value : Value Symbol Guard) (available : Available state value) (edges : List (EdgeValue Symbol Guard))
    (done : nodeEdges fuel value state = .done edges state)
    (edge : EdgeValue Symbol Guard) (origin : Origin state [value] edge) : edge ∈ edges := by
  have facts := semantic.1.normal.facts
  have fallback (root : Value Symbol Guard) (input : Available state root)
      (completed : (collect fuel state [] [root]).canonical = .done edges state)
      (origin : Origin state [root] edge) : edge ∈ edges := by
    have inputs : Values state [root] := by
      intro child member
      simpa only [List.mem_singleton.mp member] using input
    cases read : collect fuel state [] [root] with
    | unresolved | pending | exhausted => simp only [read, Result.canonical, reduceCtorEq] at completed
    | done values final =>
        have equal : canonicalEdges values = edges ∧ final = state := by
          simpa only [read, Result.canonical, Result.done.injEq] using completed
        have cache := equal.2
        subst final
        rw [← equal.1]
        exact InternedEdgeResidency.canonicalEdges_retains state facts.coherent values edge
          (collect_resident_fixed fuel state semantic covered [root] inputs values read)
          (collect_covers fuel state semantic covered [root] inputs values read edge origin)
  cases value with
  | empty | reference =>
      have impossible := origin_terminal state _ rfl edge origin
      cases impossible
  | node entry own depth free =>
      cases done
      exact origin_terminal state _ rfl edge origin
  | union entry members depth free => exact fallback _ available done origin
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, context, _, _, _, _, _⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have back : Grows middle state := by
        have later : Grows middle (collect fuel middle [] [.mu entry body depth ordinary]).canonical.state := by
          simpa only [MergedPreparedReaderEffects.canonical_state] using
            (MergedFreshOrdinaryColdReplay.collect_correct fuel middle context.normal.facts.coherent.valid
              [] [.mu entry body depth ordinary]).2
        cases result with
        | node actual own level free =>
            have equal : own = edges ∧ middle = state := by
              simpa only [nodeEdges, unfolded, Result.done.injEq] using done
            rw [equal.2]
            exact grows_refl state
        | empty | reference | union | mu =>
            have completed : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges state := by
              simpa only [nodeEdges, unfolded] using done
            simpa only [completed, Result.state] using later
      have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary)
        state state result middle facts.coherent.valid unfolded back
      have same := (Outcome.done.inj (unfolded.symm.trans replay)).2
      subst middle
      cases result with
      | node actual own level free =>
          have equal : own = edges := by
            simpa only [nodeEdges, unfolded, Result.done.injEq, and_true] using done
          rw [← equal]
          exact origin_terminal state (.node actual own level free) rfl edge
            (origin_single state _ (.node actual own level free)
              (by simp only [successors, unfolded]) rfl edge origin)
      | empty | reference | union | mu =>
          exact fallback _ available (by simpa only [nodeEdges, unfolded] using done) origin

/-- Actual warm unfolding equations remain valid above their completed cache. -/
theorem warm_grows [DecidableEq (EdgeKey Symbol Guard)]
    {before : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead before value)
    (valid : Valid before) (after : State Symbol Guard) (growth : Grows before after) : WarmHead after value := by
  induction support with
  | empty => exact .empty
  | ordinary => exact .ordinary
  | closed closed => exact .closed closed
  | unfold actual rest ih =>
      exact .unfold (InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ after _ _ valid actual growth) ih

/-- Each accepted warm-head term has an independently accepted constructor origin in a derived future cache. -/
theorem accepted_origin [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : meaning holds ambient value term) :
    ∃ view, SemanticReady view ∧ Keeps state view ∧ ∃ edge,
      Origin view [value] edge ∧ MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term := by
  revert accepted available semantic
  induction support with
  | empty => intro _ _ impossible; simp only [meaning] at impossible
  | @ordinary entry edges depth free =>
      intro semantic available accepted
      obtain ⟨edge, member, accepted⟩ := (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term |>.mp accepted
      exact ⟨state, semantic, pure_keeps state semantic.ready, edge, ⟨_, .seed List.mem_cons_self, member⟩, accepted⟩
  | @closed value closed =>
      intro semantic available accepted
      obtain ⟨edges, after, read, kept, ready, _, _⟩ :=
        SourceEqualityProjectionRead.complete value state semantic available closed
      obtain ⟨edge, member, accepted⟩ := (read.exact semantic available closed holds ambient term).mpr accepted
      cases read with
      | done fuel actual =>
          exact ⟨after, ready, kept, edge,
            MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel value state semantic.ready.semantic
              semantic.ready.covered available edges after actual after (grows_refl _) edge member, accepted⟩
  | @unfold entry body depth ordinary next actual rest ih =>
      intro semantic available accepted
      obtain ⟨result, middle, done, _, _, nextAvailable, language⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      obtain ⟨view, ready, kept, edge, origin, acceptedEdge⟩ :=
        ih semantic nextAvailable ((language holds ambient term).mpr accepted)
      have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ view _ _
        semantic.ready.semantic.1.normal.facts.coherent.valid actual kept.growth
      refine ⟨view, ready, kept, edge, ?_, acceptedEdge⟩
      apply origin.from_seeds view [next] [.mu entry body depth ordinary] ?_ edge
      intro child member
      have same : child = next := List.mem_singleton.mp member
      subst child
      exact .step (.seed List.mem_cons_self) (by simp only [successors, replay, List.mem_singleton])

/-- Every actual completed read of a warm head has the exact derived cache and resident-row effects. -/
theorem nodeEdges_verified [DecidableEq (EdgeKey Symbol Guard)]
    {state after : State Symbol Guard} {value : Value Symbol Guard} {edges : List (EdgeValue Symbol Guard)} {fuel : Nat}
    (support : WarmHead state value) (semantic : SemanticReady state) (available : Available state value)
    (actual : nodeEdges fuel value state = .done edges after) :
    Keeps state after ∧ SemanticReady after ∧ Edges after edges := by
  obtain ⟨bound, rows, final, read, kept, ready, resident⟩ := warm_nodeEdges_complete support semantic available
  obtain ⟨sameRows, sameState⟩ := (SourceEqualityProjectionRead.Read.done bound read).unique
    (SourceEqualityProjectionRead.Read.done fuel actual)
  cases sameRows
  cases sameState
  exact ⟨kept, ready, resident⟩

/-- Actual completed warm-head reads retain a constructor edge for every independently accepted term. -/
theorem nodeEdges_included [DecidableEq (EdgeKey Symbol Guard)]
    {state after : State Symbol Guard} {value : Value Symbol Guard} {edges : List (EdgeValue Symbol Guard)} {fuel : Nat}
    (support : WarmHead state value) (semantic : SemanticReady state) (available : Available state value)
    (actual : nodeEdges fuel value state = .done edges after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : meaning holds ambient value term) :
    ∃ edge ∈ edges, MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term := by
  have checked := nodeEdges_verified support semantic available actual
  obtain ⟨view, ready, kept, edge, origin, acceptedEdge⟩ :=
    accepted_origin (warm_grows support semantic.ready.semantic.1.normal.facts.coherent.valid after checked.1.growth)
      checked.2.1 (checked.1.available value available) holds ambient term accepted
  have replay := MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel value state view
    semantic.ready.semantic.1.normal.facts.coherent.valid edges after actual kept.growth
  exact ⟨edge, nodeEdges_covers_fixed fuel view ready.ready.semantic ready.ready.covered value
    (kept.available value (checked.1.available value available)) edges replay edge origin, acceptedEdge⟩

/-- A false secondary gate preserves every accepted term through its actual later-cache head reconstruction. -/
theorem head_included [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path} {value result : Value Symbol Guard}
    {before final caller after : State Symbol Guard}
    (gate : InternedFreshOrdinaryStatefulGateTrace.NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value) (growth : Grows final caller)
    (actual : Head value caller result after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : meaning holds ambient value term) : meaning holds ambient result term := by
  have support := warm_head gate semantic available caller growth
  cases actual with
  | read fuel edges middle read built =>
      have checked := nodeEdges_verified support callerSemantic callerAvailable read
      have included := nodeEdges_included support callerSemantic callerAvailable read holds ambient term accepted
      have normalized := MergedColdInterpretation.makeNode_exact middle checked.2.1.ready.semantic.1.normal.facts
        (meaning holds ambient) edges checked.2.2 holds (InternedGuardedLanguage.laws holds ambient) term
      have resultLanguage : meaning holds ambient result term ↔
          ∃ edge ∈ edges, MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term := by
        simpa only [built] using normalized
      exact resultLanguage.mpr included

/-- Every edge returned from a warm-head worklist denotes only terms of its original input. -/
theorem collect_sound [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) (seen : List Nat) (fuel : Nat)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : collect fuel state seen [value] = .done edges after) :
    ∀ edge ∈ edges, ∀ holds ambient term,
      MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term → meaning holds ambient value term := by
  revert actual after edges fuel seen available semantic
  induction support with
  | empty =>
      intro semantic available seen fuel rows after actual
      cases fuel with
      | zero => cases actual
      | succ fuel =>
          have same : [] = rows ∧ state = after := by simpa only [collect, Result.done.injEq] using actual
          rcases same with ⟨rfl, rfl⟩
          intro edge member
          cases member
  | @ordinary entry own depth free =>
      intro semantic available seen fuel rows after actual
      cases fuel with
      | zero => cases actual
      | succ fuel =>
          have same : own = rows ∧ state = after := by
            simpa only [collect, Result.prepend, List.append_nil, Result.done.injEq] using actual
          rcases same with ⟨rfl, rfl⟩
          intro edge member holds ambient term accepted
          exact ((InternedGuardedLanguage.laws holds ambient).node entry own depth free term).mpr ⟨edge, member, accepted⟩
  | @closed value closed =>
      intro semantic available seen fuel edges after actual edge member holds ambient term accepted
      obtain ⟨source, included, accepted⟩ := MergedFreshOrdinaryGuardedSoundness.collect_sound holds ambient fuel state
        semantic.ready.semantic semantic.ready.covered semantic.guarded seen [value]
        (by intro child member; simpa only [List.mem_singleton.mp member] using available)
        (by intro child member; simpa only [List.mem_singleton.mp member] using closed)
        edges after actual edge member term ((InternedGuardedLanguage.edgeMeaning_all holds ambient edge term).mpr accepted)
      simpa only [List.mem_singleton.mp included] using accepted
  | @unfold entry body depth ordinary next unfolded rest ih =>
      intro semantic available seen fuel edges after actual
      cases fuel with
      | zero => cases actual
      | succ fuel =>
          by_cases visited : entry.identity ∈ seen
          · have same : [] = edges ∧ state = after := by
              simpa only [collect, ite_eq_left visited, Result.done.injEq] using actual
            rcases same with ⟨rfl, rfl⟩
            intro edge member
            cases member
          · have nextDone : collect fuel state (entry.identity :: seen) [next] = .done edges after := by
              simpa only [collect, ite_eq_right visited, unfolded] using actual
            obtain ⟨result, middle, done, _, _, nextAvailable, language⟩ :=
              SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
            obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans unfolded)
            cases sameValue
            cases sameState
            intro edge member holds ambient term accepted
            exact (language holds ambient term).mp
              (ih semantic nextAvailable (entry.identity :: seen) fuel edges after nextDone edge member holds ambient term accepted)

/-- Each actual warm-head read returns only independently accepted terms of its input. -/
theorem nodeEdges_sound [DecidableEq (EdgeKey Symbol Guard)]
    {state after : State Symbol Guard} {value : Value Symbol Guard} {edges : List (EdgeValue Symbol Guard)} {fuel : Nat}
    (support : WarmHead state value) (semantic : SemanticReady state) (available : Available state value)
    (actual : nodeEdges fuel value state = .done edges after) :
    ∀ edge ∈ edges, ∀ holds ambient term,
      MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term → meaning holds ambient value term := by
  have fallback (root : Value Symbol Guard) (support : WarmHead state root) (available : Available state root)
      (completed : (collect fuel state [] [root]).canonical = .done edges after) :
      ∀ edge ∈ edges, ∀ holds ambient term,
        MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term → meaning holds ambient root term := by
    cases read : collect fuel state [] [root] with
    | unresolved | pending | exhausted => simp only [read, Result.canonical, reduceCtorEq] at completed
    | done rows final =>
        have same : canonicalEdges rows = edges ∧ final = after := by
          simpa only [read, Result.canonical, Result.done.injEq] using completed
        cases same.2
        intro edge member holds ambient term accepted
        exact collect_sound support semantic available [] fuel rows after read edge
          (canonicalEdges_member rows edge (same.1 ▸ member)) holds ambient term accepted
  cases support with
  | empty => cases actual; simp
  | @ordinary entry own depth free =>
      cases actual
      intro edge member holds ambient term accepted
      exact ((InternedGuardedLanguage.laws holds ambient).node entry edges depth free term).mpr ⟨edge, member, accepted⟩
  | @closed value closed =>
      intro edge member holds ambient term accepted
      exact MergedFreshOrdinaryGuardedSoundness.nodeEdges_sound holds ambient fuel value state
        semantic.ready.semantic semantic.ready.covered semantic.guarded available closed edges after actual edge member term
        ((InternedGuardedLanguage.edgeMeaning_all holds ambient edge term).mpr accepted)
  | @unfold entry body depth ordinary next unfolded rest =>
      obtain ⟨result, middle, done, _, _, _, language⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans unfolded)
      cases sameValue
      cases sameState
      cases next with
      | node own rows level free =>
          have same : rows = edges ∧ state = after := by
            simpa only [nodeEdges, unfolded, Result.done.injEq] using actual
          rcases same with ⟨rfl, rfl⟩
          intro edge member holds ambient term accepted
          exact (language holds ambient term).mp
            (((InternedGuardedLanguage.laws holds ambient).node own rows level free term).mpr ⟨edge, member, accepted⟩)
      | empty | reference | union | mu =>
          exact fallback _ (.unfold unfolded rest) available (by simpa only [nodeEdges, unfolded] using actual)

/-- An actual later-cache head after a false secondary gate has exactly its original independent language. -/
theorem head_exact [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path} {value result : Value Symbol Guard}
    {before final caller after : State Symbol Guard}
    (gate : InternedFreshOrdinaryStatefulGateTrace.NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value) (growth : Grows final caller)
    (actual : Head value caller result after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    meaning holds ambient result term ↔ meaning holds ambient value term := by
  constructor
  · have support := warm_head gate semantic available caller growth
    cases actual with
    | read fuel edges middle read built =>
        have checked := nodeEdges_verified support callerSemantic callerAvailable read
        have normalized := MergedColdInterpretation.makeNode_exact middle checked.2.1.ready.semantic.1.normal.facts
          (meaning holds ambient) edges checked.2.2 holds (InternedGuardedLanguage.laws holds ambient) term
        have resultLanguage : meaning holds ambient result term ↔
            ∃ edge ∈ edges, MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term := by
          simpa only [built] using normalized
        intro accepted
        obtain ⟨edge, member, accepted⟩ := resultLanguage.mp accepted
        exact nodeEdges_sound support callerSemantic callerAvailable read edge member holds ambient term accepted
  · exact head_included gate semantic available callerSemantic callerAvailable growth actual holds ambient term

end MicroCFTA.SourceSecondaryGateHeadLanguage
