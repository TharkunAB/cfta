import MicroCFTA.SourceSynthesisUniversePrefixReadback
import MicroCFTA.SourceSynthesisUniversePrefixHeight
import MicroCFTA.SourceSynthesisUniverseStoredRows
import MicroCFTA.MergedColdMerge

/-!
# Actual unfolding of the universe retained by a source prefix

The stored executor rebuilds rows in their actual stored order.
Each original marker remains unchanged. Each recursive reference reads
the same complete universe value. Edge requests can allocate new records.
The result is an ordinary node with prefix height at most two.
-/
namespace MicroCFTA.SourceSynthesisUniverseUnfold
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome build buildMany buildEdges work)
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open InternedEdgeResidency InternedShallowHeap MergedPhysicalWarmup
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisUniversePrefixSeed
open SourceSynthesisUniversePrefixHeight

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

private theorem leaf_done (context : List (Value String Guard)) (environment : Environment String Guard)
    (name : Reference) (marker child : Value String Guard) (current : State String Guard)
    (facts : Facts current) (available : Values current context) (closed : marker.free = [])
    (member : child ∈ context) (kind : child = marker ∨ child = .reference name) :
    build (encode context [] child) (context.map (input environment)) current =
      .done (input environment child) current := by
  rcases kind with same | same
  · subst child
    have done := build_closed context [] [] marker environment current facts.coherent available member rfl closed
    simpa only [List.nil_append, input_closed marker environment closed] using done
  · subst child
    have done := build_external context [] [] name environment current facts.coherent available member rfl rfl
    simpa only [List.nil_append, input] using done

private theorem children_done (context : List (Value String Guard)) (environment : Environment String Guard)
    (values : List (Value String Guard)) (current : State String Guard)
    (done : ∀ child ∈ values, build (encode context [] child) (context.map (input environment)) current =
      .done (input environment child) current) :
    buildMany (encodeMany context [] values) (context.map (input environment)) current =
      .done (values.map (input environment)) current := by
  induction values with
  | nil => simp only [encodeMany, buildMany, List.map_nil]
  | cons first rest ih =>
      have own := done first List.mem_cons_self
      have tail := ih (fun child member => done child (List.mem_cons_of_mem _ member))
      simp only [encodeMany, buildMany, own, Outcome.bind, tail, List.map_cons]

private theorem rows_done (context : List (Value String Guard)) (environment : Environment String Guard)
    (name : Reference) (marker whole : Value String Guard) (closed : marker.free = [])
    (replaced : input environment (.reference name) = whole) (sources : List (EdgeValue String Guard)) :
    ∀ current, Facts current → Prepared current → Values current context → Available current marker → Available current whole →
      (∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference name) →
      (∀ source ∈ sources, ∀ child ∈ source.children, child ∈ context) →
      ∃ targets after,
        buildEdges (encodeEdges context [] sources) (context.map (input environment)) current = .done targets after ∧
        MergedColdMerge.Extension current after ∧ Edges after targets ∧
        (∀ target ∈ targets, ∀ child ∈ target.children, child = marker ∨ child = whole) ∧
        targets.length = sources.length := by
  induction sources with
  | nil =>
      intro current facts prepared available markerAvailable wholeAvailable kinds members
      refine ⟨[], current, ?_, .refl current facts prepared, ?_, ?_, rfl⟩
      · simp only [encodeEdges, buildEdges]
      · intro target member; cases member
      · intro target member; cases member
  | cons source rest ih =>
      intro current facts prepared available markerAvailable wholeAvailable kinds members
      cases source with
      | mk entry children =>
          let values := children.map (input environment)
          have valuesAvailable : Values current values := by
            intro value member
            obtain ⟨child, included, rfl⟩ := List.mem_map.mp member
            rcases kinds _ List.mem_cons_self child included with same | same
            · rw [same, input_closed marker environment closed]; exact markerAvailable
            · rw [same, replaced]; exact wholeAvailable
          have childrenDone := children_done context environment children current (fun child member =>
            leaf_done context environment name marker child current facts available closed
              (members _ List.mem_cons_self child member) (kinds _ List.mem_cons_self child member))
          let made := run (makeEdge entry.key.symbol entry.key.constraint values) current
          have checked := edge_verified entry.key.symbol entry.key.constraint values current facts valuesAvailable
          have extension : MergedColdMerge.Extension current made.2 :=
            ⟨checked.facts, prepared.preserve (by intro key own body depth ordinary stored; exact stored),
              checked.growth, checked.history⟩
          have ownResident : EdgeResident made.2 made.1 := checked.result _ _ rfl
          have ownChildren : made.1.children = values :=
            InternedShallowValues.makeEdge_children _ _ values current facts.coherent facts.cached valuesAvailable
          have ownKinds : ∀ child ∈ made.1.children, child = marker ∨ child = whole := by
            intro child member
            rw [ownChildren] at member
            obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
            rcases kinds _ List.mem_cons_self original included with same | same
            · left; rw [same, input_closed marker environment closed]
            · right; rw [same, replaced]
          obtain ⟨targets, after, restDone, later, resident, targetKinds, length⟩ :=
            ih made.2 extension.facts extension.prepared
              (fun value member => extension.available value (available value member))
              (extension.available marker markerAvailable) (extension.available whole wholeAvailable)
              (fun source member => kinds source (List.mem_cons_of_mem _ member))
              (fun source member => members source (List.mem_cons_of_mem _ member))
          refine ⟨made.1 :: targets, after, ?_, extension.trans later, ?_, ?_, by simp only [List.length_cons, length]⟩
          · simp only [encodeEdges, buildEdges, childrenDone, Outcome.bind, work]
            rw [restDone]
          · intro target member
            rcases List.mem_cons.mp member with same | included
            · subst target; exact edge_grows made.2 after later.growth made.1 ownResident
            · exact resident target included
          · intro target member
            rcases List.mem_cons.mp member with same | included
            · subst target; exact ownKinds
            · exact targetKinds target included

/-- Actual stored unfolding retains the same universe atom and at most two ordinary layers. -/
theorem unfold_bounded {top : Guard} {catalog : List (String × Nat)} (seed : Seed top catalog)
    (current : State String Guard) (facts : Facts current) (prepared : Prepared current)
    (ready : Ready (some seed) current) :
    ∃ entry rows depth free after,
      InternedFreshOrdinaryStoredSubstitution.unfold seed.value current = .done (.node entry rows depth free) after ∧
      MergedColdMerge.Extension current after ∧ Available after (.node entry rows depth free) ∧
      (∀ atom ∈ InternedBoundaryAtoms.atoms (.node entry rows depth free), atom = .mu seed.entry.identity) ∧
      height (.node entry rows depth free) ≤ 2 := by
  have wholeAvailable := seed.available_after current facts ready
  obtain ⟨bodyEntry, marker, arrow, rest, bodyEq, markerRead, _arrowChildren, _arrowKey, _aligned,
      _resident, closed, markerAvailable, _tops, rawKinds, _live, _retained, nonempty⟩ :=
    (seed.rows_after current ready).1.readback facts
  let sources := canonicalEdges (arrow :: rest)
  let name := Reference.interned seed.entry.identity
  let environment : Environment String Guard := fun other => if other = name then some seed.value else none
  let body : Value String Guard := .node bodyEntry sources 0 [name]
  let context := leaves body
  have bodyAvailable : Available current body := by
    dsimp only [body, sources, name]
    rw [← bodyEq]
    exact wholeAvailable.children seed.body (by simp [Seed.value, InternedProbeProvenance.children])
  have contextAvailable : Values current context := leaves_available body current bodyAvailable
  have kinds : ∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference name :=
    fun source member => rawKinds source (canonicalEdges_member _ source member)
  have members : ∀ source ∈ sources, ∀ child ∈ source.children, child ∈ context := by
    intro source member child included
    change child ∈ leaves (.node bodyEntry sources 0 [name])
    rw [SourceSynthesisUniverseStoredRows.leaves_reference_eq_children name bodyEntry sources marker closed kinds]
    exact List.mem_flatMap.mpr ⟨source, member, included⟩
  have replaced : input environment (.reference name) = seed.value := by simp only [input, environment, ite_true, Option.getD_some]
  obtain ⟨targets, middle, rowsDone, extension, resident, targetKinds, length⟩ :=
    rows_done context environment name marker seed.value closed replaced sources current facts prepared contextAvailable
      markerAvailable wholeAvailable kinds members
  have targetNonempty : targets ≠ [] := by
    intro absent
    rw [absent, List.length_nil] at length
    have sourcesEmpty : sources = [] := List.length_eq_zero_iff.mp length.symm
    exact nonempty sourcesEmpty
  have markerProperties : InternedBoundaryAtoms.atoms marker = [] ∧ height marker = 1 ∧ marker.referenceOf ≠ .empty := by
    obtain ⟨entry, row, same, children, _key⟩ := markerRead
    cases row with
    | mk edge values =>
        change values = [] at children
        subst values
        rw [same]
        refine ⟨?_, ?_, ?_⟩
        · simp only [InternedBoundaryAtoms.atoms, InternedBoundaryAtoms.edgeAtoms,
            InternedBoundaryAtoms.manyAtoms, List.append_nil]
        · rfl
        · intro impossible; cases impossible
  have survive : surviving targets = targets := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    have liveRow : EqualityLeafProjectionPhysical.dead row = false := by
      apply List.any_eq_false.mpr
      intro child included
      rcases targetKinds row member child included with same | same
      · rw [same]
        intro equal
        exact markerProperties.2.2 (beq_iff_eq.mp equal)
      · rw [same]
        intro equal
        have impossible : seed.value.referenceOf = .empty := beq_iff_eq.mp equal
        cases impossible
    change (!EqualityLeafProjectionPhysical.dead row) = true
    simp only [liveRow, Bool.not_false]
  have selectedResident : Edges middle (canonicalEdges targets) :=
    fun row member => resident row (canonicalEdges_member _ row member)
  have selectedNonempty : canonicalEdges targets ≠ [] := by
    cases targets with
    | nil => exact False.elim (targetNonempty rfl)
    | cons first tail =>
        have retained := canonicalEdges_retains middle extension.facts.coherent (first :: tail) first resident List.mem_cons_self
        intro absent
        rw [absent] at retained
        cases retained
  obtain ⟨entry, readback⟩ := identifyNode_readback (canonicalEdges targets) middle
    extension.facts.coherent extension.facts.linked selectedResident
  have resultShape : (run (makeNode targets) middle).1 =
      .node entry (canonicalEdges targets) (maximumDepth ((canonicalEdges targets).flatMap EdgeValue.children))
        (childFree ((canonicalEdges targets).flatMap EdgeValue.children)) := by
    cases selected : canonicalEdges targets with
    | nil => exact False.elim (selectedNonempty selected)
    | cons first tail =>
        simp only [selected] at readback
        simpa only [makeNode, survive, selected, run, identifyNode] using readback
  have nodeChecked := node_verified targets middle extension.facts resident
  have last : MergedColdMerge.Extension middle (run (makeNode targets) middle).2 :=
    ⟨nodeChecked.facts, extension.prepared.preserve (makeNode_noNewMu targets middle), nodeChecked.growth, nodeChecked.history⟩
  have preparedBody : PreparedWithoutMu body := by
    have actual := prepared seed.entry.key seed.entry seed.body seed.depth seed.ordinary
      (wholeAvailable.resident seed.entry rfl)
    simpa only [bodyEq] using actual
  have unfolded : InternedFreshOrdinaryStoredSubstitution.unfold seed.value current =
      .done (run (makeNode targets) middle).1 (run (makeNode targets) middle).2 := by
    change InternedFreshOrdinaryStoredSubstitution.execute seed.body environment current = _
    rw [bodyEq, InternedFreshOrdinaryStoredSubstitution.execute_eq body environment current preparedBody]
    unfold InternedStoredSubstitution.execute
    change build (encode context [] (.node bodyEntry sources 0 [name])) (context.map (input environment)) current = _
    rw [encode.eq_def]
    simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, build, rowsDone, Outcome.bind, work]
  have atomBound : ∀ atom ∈ InternedBoundaryAtoms.atoms (run (makeNode targets) middle).1,
      atom = .mu seed.entry.identity := by
    intro atom present
    have origin := InternedBoundaryAtoms.makeNode_atom_origin targets middle extension.facts.coherent
      extension.facts.linked resident atom present
    obtain ⟨row, member, child, included, occurrence⟩ := (InternedBoundaryAtoms.edge_member _ atom).mp origin
    rcases targetKinds row member child included with same | same
    · rw [same, markerProperties.1] at occurrence; cases occurrence
    · simpa only [same, Seed.value, InternedBoundaryAtoms.atoms, List.mem_singleton] using occurrence
  have heightBound : height (run (makeNode targets) middle).1 ≤ 2 := by
    apply makeNode_bound targets middle extension.facts resident 2
    intro row member
    cases row with
    | mk own values =>
        have bounded : childrenHeight values ≤ 1 := (childrenHeight_le values 1).mpr (by
          intro child included
          rcases targetKinds _ member child included with same | same
          · simpa only [same, markerProperties.2.1] using (Nat.le_refl 1)
          · simpa only [same, Seed.value, height] using (Nat.zero_le 1))
        change childrenHeight values + 1 ≤ 2
        omega
  exact ⟨entry, _, _, _, _, by simpa only [resultShape] using unfolded, extension.trans last,
    by simpa only [resultShape] using nodeChecked.result _ _ rfl,
    by simpa only [resultShape] using atomBound, by simpa only [resultShape] using heightBound⟩

end MicroCFTA.SourceSynthesisUniverseUnfold
