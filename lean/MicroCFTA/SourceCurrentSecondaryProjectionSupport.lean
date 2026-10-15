import MicroCFTA.SourceSecondaryGateHeadLanguage
import MicroCFTA.SourceCurrentSecondaryReplay
import MicroCFTA.SourceCurrentSecondaryProjectionEndpoint

/-!
# Anchored support for selected source projection children

A value is closed or has an actual false gate certificate at one retained
anchor heap. Actual epsilon origins transfer this support through exposed
head rows. Canonical reconstruction keeps complete source edges and child
positions. The anchor retains the current false trace. Closed constrained Mu endpoints
use the current free-list test. Warm head completion reuses only the
trace-independent source worklist proofs.
-/
namespace MicroCFTA.SourceCurrentSecondaryProjectionSupport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values Edges)
open SourceCurrentSecondaryTrace EqualityNormalize
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open MergedFreshOrdinaryGraph MergedFreshOrdinaryExposure

private theorem warm_of_trace [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained path value before answer final) :
    answer = false → SemanticReady before → Available before value →
      ∀ target, Grows final target → SourceSecondaryGateHead.WarmHead target value := by
  induction trace using NodeTrace.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | empty => intro _ _ _ _ _; exact .empty
  | reference => intro impossible; cases impossible
  | union members => intro impossible; cases impossible
  | finite fast => intro _ _ _ _ _; exact .ordinary
  | endpoint slow => intro _ _ _ _ _; exact .ordinary
  | branches slow trace ih => intro _ _ _ _ _; exact .ordinary
  | @constrained entry body depth ordinary path state blocked =>
      intro cleared _ _ _ _
      cases path with
      | nil => exact .closed (by simpa only [Bool.not_eq_false', List.isEmpty_iff] using cleared)
      | cons => cases cleared
  | closed plain closed => intro _ _ _ _ _; exact .closed (List.isEmpty_iff.mp closed)
  | unfold plain opened actual trace ih =>
      intro answer semantic available target growth
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have tail := SourceCurrentSecondaryReplay.node_replay _ _ _ _ _ _ trace middleSemantic resultAvailable
      exact .unfold
        (InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ target _ _
          semantic.ready.semantic.1.normal.facts.coherent.valid actual (grows_trans tail.2.1.growth growth))
        (ih answer middleSemantic resultAvailable target growth)
  | missing absent => trivial
  | present found trace ih => trivial
  | nil => trivial
  | stop head ih => trivial
  | next head tail headIH tailIH => trivial

/-- A false actual gate supplies its finite warm head chain above its completed final cache. -/
theorem warm_head [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (target : State Symbol Guard) (growth : Grows final target) : SourceSecondaryGateHead.WarmHead target value :=
  warm_of_trace trace rfl semantic available target growth

/-- A false completed gate derives the actual nodeEdges read in a later retained constructor cache. -/
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (caller : State Symbol Guard) (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value)
    (growth : Grows final caller) :
    ∃ fuel edges after, nodeEdges fuel value caller = .done edges after ∧ Keeps caller after ∧
      SemanticReady after ∧ Edges after edges :=
  SourceSecondaryGateHead.warm_nodeEdges_complete (warm_head trace semantic available caller growth) callerSemantic callerAvailable

/-- A false completed gate derives finite actual head reconstruction without whole-value closedness. -/
theorem head_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (caller : State Symbol Guard) (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value)
    (growth : Grows final caller) :
    ∃ result after, Head value caller result after ∧ Keeps caller after ∧
      SemanticReady after ∧ Available after result ∧ Ordinary result := by
  obtain ⟨fuel, edges, middle, actual, kept, ready, resident⟩ :=
    nodeEdges_complete trace semantic available caller callerSemantic callerAvailable growth
  have rebuilt := SourceEqualityOpenOrdinaryHead.node edges middle ready resident
  exact ⟨_, _, .read fuel edges middle actual rfl, kept.trans rebuilt.1, rebuilt.2⟩

/-- Every actual completed head agrees with the head derived from the false gate. -/
theorem head_verified [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value result : Value Symbol Guard}
    {before final caller after : State Symbol Guard}
    (gate : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value) (growth : Grows final caller)
    (actual : Head value caller result after) :
    Keeps caller after ∧ SemanticReady after ∧ Available after result ∧ Ordinary result := by
  obtain ⟨value, state, head, kept, ready, resident, ordinary⟩ :=
    head_complete gate semantic available caller callerSemantic callerAvailable growth
  obtain ⟨sameValue, sameState⟩ := head.unique actual
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident, ordinary⟩

/-- Closed values or exact false gate receipts at one fixed source anchor support the path. -/
def Support [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (path : Path) (value : Value Symbol Guard) : Prop :=
  value.free = [] ∨ (Available anchor value ∧ NodeTrace unconstrained path value anchor false anchor)

/-- Anchored support supplies a finite actual warm head chain in each retained caller heap. -/
theorem support_warm_head [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard} {path : Path} {value : Value Symbol Guard}
    (support : Support unconstrained anchor path value) (semantic : SemanticReady anchor)
    (caller : State Symbol Guard) (growth : Grows anchor caller) : SourceSecondaryGateHead.WarmHead caller value := by
  rcases support with closed | ⟨available, trace⟩
  · exact .closed closed
  · exact warm_head trace semantic available caller growth

/-- A selected ordinary child is closed or retains its shorter false certificate at the anchor. -/
theorem ordinary_selected_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard} {index : Nat} {path : Path}
    {entry : Interned InternedBinderProtocol.NodeKey} {edges : List (EdgeValue Symbol Guard)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference}
    (support : Support unconstrained anchor (index :: path) (.node entry edges depth free))
    (anchorSemantic : SemanticReady anchor) (callerSemantic : SemanticReady caller)
    (callerAvailable : Available caller (.node entry edges depth free))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard)
    (selected : edge.children[index]? = some child) : Support unconstrained anchor path child := by
  rcases support with closed | ⟨available, trace⟩
  · exact Or.inl (MergedColdReaderClosed.node_children_closed caller callerSemantic.ready.semantic.1.normal.facts
      entry edges depth free callerAvailable closed edge member child (List.mem_of_getElem? selected))
  · cases trace with
    | finite fast =>
        have closed : (Value.node entry edges depth free).free = [] :=
          List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp fast).2
        exact Or.inl (MergedColdReaderClosed.node_children_closed anchor anchorSemantic.ready.semantic.1.normal.facts
          entry edges depth free available closed edge member child (List.mem_of_getElem? selected))
    | branches slow scan =>
        have childTrace := SourceCurrentSecondaryReplay.false_edges_members unconstrained index path edges anchor anchor scan
          anchorSemantic (fun value included => available.children value included) anchor (grows_refl _) edge member
        have childAvailable : Available anchor child := available.children child
          (List.mem_flatMap.mpr ⟨edge, member, List.mem_of_getElem? selected⟩)
        exact Or.inr ⟨childAvailable, SourceCurrentSecondaryReplay.false_selected childTrace selected⟩

private theorem successor_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard} {path : Path}
    {value child : Value Symbol Guard} (support : Support unconstrained anchor path value)
    (anchorSemantic : SemanticReady anchor) (callerSemantic : SemanticReady caller)
    (callerAvailable : Available caller value) (growth : Grows anchor caller)
    (member : child ∈ successors caller value) : Support unconstrained anchor path child := by
  rcases support with closed | ⟨available, trace⟩
  · exact Or.inl (MergedFreshOrdinaryExposureInputs.successor_closed caller callerSemantic.ready.semantic
      value callerAvailable closed child member)
  · cases value with
    | empty | reference | node => simp only [successors, List.not_mem_nil] at member
    | union => cases trace
    | mu entry body depth ordinary =>
      generalize cleared : false = answer at trace
      cases trace with
      | constrained blocked =>
        have closed : (Value.mu entry body depth ordinary).free = [] := by
          cases path with
          | nil => simpa only [Bool.not_eq_false', List.isEmpty_iff] using cleared.symm
          | cons => cases cleared
        exact Or.inl (MergedFreshOrdinaryExposureInputs.successor_closed caller callerSemantic.ready.semantic
          _ callerAvailable closed child member)
      | closed plain closed =>
        exact Or.inl (MergedFreshOrdinaryExposureInputs.successor_closed caller callerSemantic.ready.semantic
          _ callerAvailable (List.isEmpty_iff.mp closed) child member)
      | unfold plain opened actual tail =>
        obtain ⟨next, middle, done, _, middleSemantic, nextAvailable, _⟩ :=
          SourceEqualityOpenOrdinaryHead.unfold_complete _ _ anchorSemantic available
        obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
        have following : NodeTrace unconstrained path next middle false anchor := by
          simpa only [sameValue, sameState, ← cleared] using tail
        have tailEffects := SourceCurrentSecondaryReplay.node_replay _ _ _ _ _ _ following middleSemantic nextAvailable
        have warm := InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ anchor _ _
          anchorSemantic.ready.semantic.1.normal.facts.coherent.valid done tailEffects.2.1.growth
        have same := (Outcome.done.inj (done.symm.trans warm)).2
        rw [same] at done nextAvailable following
        have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ caller _ _
          anchorSemantic.ready.semantic.1.normal.facts.coherent.valid done growth
        have equal : child = next := List.mem_singleton.mp (by simpa only [successors, replay] using member)
        subst child
        exact Or.inr ⟨nextAvailable, following⟩

/-- Actual completed row reads retain anchored support at every reached epsilon source. -/
theorem reachable_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard} {path : Path}
    {root value : Value Symbol Guard} {fuel : Nat} {edges : List (EdgeValue Symbol Guard)}
    (support : Support unconstrained anchor path root) (anchorSemantic : SemanticReady anchor)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller root) (growth : Grows anchor caller)
    (read : nodeEdges fuel root caller = .done edges caller)
    (reached : Productivity.Reachable (successors caller) [root] value) : Support unconstrained anchor path value := by
  induction reached with
  | seed member => simpa only [List.mem_singleton.mp member] using support
  | @step value next prior member ih =>
      have available := MergedFreshOrdinaryExposureInputs.nodeEdges_reachable_available fuel caller
        callerSemantic.ready.semantic callerSemantic.ready.covered root callerAvailable edges read value prior
      exact successor_support ih anchorSemantic callerSemantic available growth member

private theorem makeNode_edge_member [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (resident : Edges state edges) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges (run (makeNode edges) state).1, edge ∈ edges := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), InternedEdgeResidency.EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · simp only [run, InternedEdgeResidency.nodeEdges, List.not_mem_nil, false_implies, implies_true]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, InternedEdgeResidency.nodeEdges]
    intro edge member
    have kept : edge ∈ canonicalEdges (surviving edges) := by rw [same]; exact member
    exact (List.mem_filter.mp (canonicalEdges_member (surviving edges) edge kept)).1

/-- Every actual selected child of a rebuilt head retains closedness or its shorter anchor certificate. -/
theorem head_selected_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller after : State Symbol Guard}
    {index : Nat} {path : Path} {original exposed : Value Symbol Guard}
    (gate : NodeTrace unconstrained (index :: path) original anchor false anchor)
    (anchorSemantic : SemanticReady anchor) (anchorAvailable : Available anchor original)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller original) (growth : Grows anchor caller)
    (actual : Head original caller exposed after) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child := by
  have support : Support unconstrained anchor (index :: path) original := Or.inr ⟨anchorAvailable, gate⟩
  have warm := support_warm_head support anchorSemantic caller growth
  cases actual with
  | read fuel edges middle read built =>
      have checked := SourceSecondaryGateHeadLanguage.nodeEdges_verified warm callerSemantic callerAvailable read
      have rebuilt := SourceEqualityOpenOrdinaryHead.node edges middle checked.2.1 checked.2.2
      have sameValue := congrArg Prod.fst built
      have sameState := congrArg Prod.snd built
      dsimp only at sameValue sameState
      subst exposed
      subst after
      have originalAvailable := rebuilt.1.available original (checked.1.available original callerAvailable)
      have replay := MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel original caller _
        callerSemantic.ready.semantic.1.normal.facts.coherent.valid edges middle read rebuilt.1.growth
      have retained := grows_trans growth (grows_trans checked.1.growth rebuilt.1.growth)
      intro edge member child selected
      have originalMember := makeNode_edge_member edges middle checked.2.1.ready.semantic.1.normal.facts checked.2.2 edge member
      obtain ⟨source, reached, sourceMember⟩ := MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel original caller
        callerSemantic.ready.semantic callerSemantic.ready.covered callerAvailable edges middle read _ rebuilt.1.growth edge originalMember
      have sourceAvailable := MergedFreshOrdinaryExposureInputs.nodeEdges_reachable_available fuel _
        rebuilt.2.1.ready.semantic rebuilt.2.1.ready.covered original originalAvailable edges replay source reached
      have sourceSupport := reachable_support support anchorSemantic rebuilt.2.1 originalAvailable retained replay reached
      cases source with
      | empty | reference | union | mu => simp only [InternedEdgeResidency.nodeEdges, List.not_mem_nil] at sourceMember
      | node entry rows depth free =>
          exact ordinary_selected_support sourceSupport anchorSemantic rebuilt.2.1 sourceAvailable edge sourceMember child selected

end MicroCFTA.SourceCurrentSecondaryProjectionSupport
