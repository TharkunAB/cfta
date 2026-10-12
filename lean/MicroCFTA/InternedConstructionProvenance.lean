import MicroCFTA.InternedTemplateProvenance

/-!
# Provenance from complete empty-cache constructor traces

Ordinary and Mu requests consume earlier constructed records. Each Mu
reservation makes its own reference available before the normalized body
runs. Completed records preserve the same invariant for later captures.
-/
namespace MicroCFTA.InternedConstructionProvenance
open Cache InternedConstructorTemplates InternedRecordCoherence InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeRef NodeKey)
open InternedProbeProvenance InternedTemplateProvenance

/-- Reserving a source Mu identity preserves all earlier inputs and makes its own reference available. -/
theorem reserve_available (key : NodeKey) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) :
    let allocated := {state with nodes := (Cache.intern state.nodes key).2}
    Cached allocated ∧ Available allocated (.reference (.interned (Cache.intern state.nodes key).1.identity)) := by
  let allocated := {state with nodes := (Cache.intern state.nodes key).2}
  have growth : Grows state allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := intern_issued_extends state.nodes key coherent.valid.2
  constructor
  · constructor
    · intro other edge present child member
      exact (cached.edges other edge present child member).grows state allocated growth history
    · intro other value present
      exact (cached.nodes other value present).grows state allocated growth history
  · exact reference_available allocated _ (reserved_reference_issued state.nodes key coherent.valid.2)

/-- Actual Mu completion derives all retained fields from its probes, reservation, and body execution. -/
theorem finishMu_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depth ordinary : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (covered : Covered pending state) (cached : Cached state)
    (captured : ∀ value ∈ captures template, Available state value)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary) :
    Coherent (finishMu template depth ordinary state).2 ∧ Cached (finishMu template depth ordinary state).2 ∧
      Available (finishMu template depth ordinary state).2 (finishMu template depth ordinary state).1 := by
  cases found : state.nodeRecords (muKey depth ordinary) with
  | some value =>
      simpa only [finishMu, found] using And.intro coherent (And.intro cached (cached.nodes _ value found))
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      let body := run (compileBody template (.interned entry.1.identity)) allocated
      let candidate := Value.mu entry.1 body.1 depth ordinary
      let completed := {body.2 with nodeRecords := keepFirst body.2.nodeRecords key candidate}
      have allocatedGrowth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have allocatedHistory := intern_issued_extends state.nodes key coherent.valid.2
      have reserved := reserve_correct key state coherent covered
      have reservedAvailable := reserve_available key state coherent cached
      have built := compileBody_available template (.interned entry.1.identity) allocated reserved.1 reservedAvailable.1
        reservedAvailable.2.issued
        (fun value member => (captured value member).grows state allocated allocatedGrowth allocatedHistory)
      have bodyGrowth := (InternedConstructorTemplates.run_correct
        (compileBody template (.interned entry.1.identity)) allocated reserved.1.valid).2
      have bodyHistory := run_issued_extends (compileBody template (.interned entry.1.identity)) allocated reserved.1.valid
      have doneGrowth : Grows body.2 completed :=
        ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩
      have finalSame : (finishMu template depth ordinary state).2 = completed := by
        simp only [finishMu, found]
        rfl
      have finalCoherent : Coherent completed := by
        rw [← finalSame]
        exact (InternedRecordCoherence.finishMu_correct template depth ordinary state coherent covered).1
      have finalBody : Available completed body.1 := built.2.2.grows body.2 completed doneGrowth (extends_refl _)
      have finalDepth : Available completed depth :=
        ((depthAvailable.grows state allocated allocatedGrowth allocatedHistory).grows allocated body.2 bodyGrowth bodyHistory).grows
          body.2 completed doneGrowth (extends_refl _)
      have finalOrdinary : Available completed ordinary :=
        ((ordinaryAvailable.grows state allocated allocatedGrowth allocatedHistory).grows allocated body.2 bodyGrowth bodyHistory).grows
          body.2 completed doneGrowth (extends_refl _)
      have finalCached : Cached completed := by
        constructor
        · intro other edge present child member
          exact (built.2.1.edges other edge present child member).grows body.2 completed doneGrowth (extends_refl _)
        · intro other value present
          rcases record_cases body.2.nodeRecords key other candidate value present with old | ⟨same, sameValue⟩
          · exact (built.2.1.nodes other value old).grows body.2 completed doneGrowth (extends_refl _)
          · subst other value
            refine .intro candidate (stored_resident completed finalCoherent key candidate present)
              (identifyMu_issued completed.nodes entry.1 body.1 depth ordinary finalBody.issued) ?_
            intro child member
            simp only [candidate, InternedProbeProvenance.children, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl
            · exact finalBody
            · exact finalDepth
            · exact finalOrdinary
      have stored := finishMu_stored template depth ordinary state
      rw [finalSame] at stored ⊢
      exact ⟨finalCoherent, finalCached, finalCached.nodes key _ stored⟩

/-- The complete generated Mu request derives both probe premises before its actual reservation. -/
theorem internMu_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered pending state) (cached : Cached state)
    (captured : ∀ value ∈ captures template, Available state value) :
    Coherent (internMu template state).2 ∧ Cached (internMu template state).2 ∧
      Available (internMu template state).2 (internMu template state).1 := by
  have checked := probes_available template state coherent cached captured
  have complete := InternedRecordCoherence.probes_correct template state coherent covered
  have firstValid := (InternedConstructorTemplates.run_correct (compileBody template .depth) state coherent.valid).1
  have history := extends_trans (run_issued_extends (compileBody template .depth) state coherent.valid)
    (run_issued_extends (compileBody template (.uninterned (run (compileBody template .depth) state).1.depth)) _ firstValid)
  exact finishMu_available template _ _ _ checked.1 complete.2 checked.2.1
    (fun value member => (captured value member).grows state (probes template state).2
      (InternedConstructorTemplates.probes_correct template state coherent.valid).2 history)
    checked.2.2.1 checked.2.2.2

/-- Smart Mu cleanup returns an existing retained body, EmptyNode, or its original complete record. -/
theorem cleanup_available (value : Value Symbol Guard) (available : Available state value) :
    Available state (cleanup value) := by
  cases value <;> simp only [cleanup]
  all_goals first
    | exact available
    | (split
       · exact available.children _ List.mem_cons_self
       · split
         · exact empty_available state
         · exact available)

/-- The source smart Mu constructor preserves the complete record and reference provenance invariant. -/
theorem createMu_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered pending state) (cached : Cached state)
    (captured : ∀ value ∈ captures template, Available state value) :
    Coherent (createMu template state).2 ∧ Cached (createMu template state).2 ∧
      Available (createMu template state).2 (createMu template state).1 := by
  have built := internMu_available template state coherent covered cached captured
  exact ⟨built.1, built.2.1, cleanup_available _ built.2.2⟩

/-- Source construction traces use only available original inputs at each constructor call. -/
inductive SourceBuilt [DecidableEq (EdgeKey Symbol Guard)] : InternedConstructorTemplates.State Symbol Guard → Prop where
  | empty : SourceBuilt empty
  | ordinary (before : SourceBuilt state) (template : Template Symbol Guard) (argument : Value Symbol Guard)
      (input : Available state argument) (captured : ∀ value ∈ captures template, Available state value) :
      SourceBuilt (run (compile template argument) state).2
  | binder (before : SourceBuilt state) (template : Template Symbol Guard)
      (captured : ∀ value ∈ captures template, Available state value) : SourceBuilt (createMu template state).2

/-- The strengthened trace is the existing actual constructor trace with finite input provenance. -/
theorem sourceBuilt_constructed [DecidableEq (EdgeKey Symbol Guard)]
    {state : InternedConstructorTemplates.State Symbol Guard} (built : SourceBuilt state) : Constructed state := by
  induction built with
  | empty => exact .empty
  | ordinary before template argument input captured ih => exact .ordinary ih template argument
  | binder before template captured ih => exact .binder ih template

/-- Empty-cache source traces derive complete record coherence, coverage, and reference provenance. -/
theorem sourceBuilt_correct [DecidableEq (EdgeKey Symbol Guard)]
    {state : InternedConstructorTemplates.State Symbol Guard} (built : SourceBuilt state) :
    Coherent state ∧ Covered [] state ∧ Cached state := by
  induction built with
  | empty => exact ⟨empty_correct.1, empty_correct.2, empty_cached⟩
  | ordinary before template argument input captured ih =>
      have result := compile_available template argument _ ih.1 ih.2.2 input captured
      exact ⟨result.1, (compile_correct template argument _ ih.1 ih.2.1).2, result.2.1⟩
  | binder before template captured ih =>
      have result := createMu_available template _ ih.1 ih.2.1 ih.2.2 captured
      exact ⟨result.1, (InternedRecordCoherence.createMu_correct template _ ih.1 ih.2.1).2, result.2.1⟩

/-- Both actual probes derive their complete availability in every source-built constructor state. -/
theorem source_probes_available [DecidableEq (EdgeKey Symbol Guard)]
    {state : InternedConstructorTemplates.State Symbol Guard} (built : SourceBuilt state)
    (template : Template Symbol Guard) (captured : ∀ value ∈ captures template, Available state value) :
    Available (probes template state).2 (probes template state).1.1 ∧
      Available (probes template state).2 (probes template state).1.2 :=
  (probes_available template state (sourceBuilt_correct built).1 (sourceBuilt_correct built).2.2 captured).2.2

/-- Actual fresh-dependent nested probes derive every residency and old-reference premise of key separation. -/
theorem nested_probes_separate [DecidableEq (EdgeKey Symbol Guard)]
    {state : InternedConstructorTemplates.State Symbol Guard} (built : SourceBuilt state)
    (outerTemplate innerTemplate : Template Symbol Guard)
    (capturedOuter : ∀ value ∈ captures outerTemplate, Available state value) :
    let outer := probes outerTemplate state
    let key := muKey outer.1.1 outer.1.2
    let entry := Cache.intern outer.2.nodes key
    let allocated := {outer.2 with nodes := entry.2}
    let inner := probes innerTemplate allocated
    (∀ value ∈ captures innerTemplate, Available allocated value) →
    outer.2.nodeRecords key = none →
    (.interned entry.1.identity ∈ inner.1.1.free ∨ .interned entry.1.identity ∈ inner.1.2.free) →
    key ≠ muKey inner.1.1 inner.1.2 := by
  dsimp only
  intro capturedInner missing retained
  let outer := probes outerTemplate state
  let key := muKey outer.1.1 outer.1.2
  let entry := Cache.intern outer.2.nodes key
  let allocated := {outer.2 with nodes := entry.2}
  let inner := probes innerTemplate allocated
  have initial := sourceBuilt_correct built
  have outerAvailable := probes_available outerTemplate state initial.1 initial.2.2 capturedOuter
  have outerCovered := (InternedRecordCoherence.probes_correct outerTemplate state initial.1 initial.2.1).2
  have reserved := reserve_correct key outer.2 outerAvailable.1 outerCovered
  have reservedAvailable := reserve_available key outer.2 outerAvailable.1 outerAvailable.2.1
  have innerAvailable := probes_available innerTemplate allocated reserved.1 reservedAvailable.1 capturedInner
  have reservationGrowth : Grows outer.2 allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have growth : Grows outer.2 inner.2 := grows_trans reservationGrowth
    (InternedConstructorTemplates.probes_correct innerTemplate allocated reserved.1.valid).2
  exact fresh_probe_key_separates outer.2 inner.2 outerAvailable.1 innerAvailable.1 growth
    outer.1.1 outer.1.2 inner.1.1 inner.1.2 outerAvailable.2.2.1.resident outerAvailable.2.2.2.resident
    innerAvailable.2.2.1.resident innerAvailable.2.2.2.resident
    outerAvailable.2.2.1.issued outerAvailable.2.2.2.issued
    (missing_record_is_fresh outer.2 outerCovered key missing) retained

/-- Original capture-free templates discharge their source-input condition without a cache premise. -/
theorem no_captures (template : Template Symbol Guard) (none : captures template = [])
    (state : InternedConstructorTemplates.State Symbol Guard) :
    ∀ value ∈ captures template, Available state value := by simp [none]

/-- A fresh outer reference can occur beside the nested binder's own probe argument. -/
def outerExample : Template Nat Unit := .node [.mk 0 () [.argument]]

/-- The inner template retains its enclosing binder as an actual captured source reference. -/
def innerExample (name : Reference) : Template Nat Unit :=
  .node [.mk 1 () [.captured (.reference name), .argument]]

/-- Concrete construction separates the exact two-probe key after the actual fresh outer reservation. -/
theorem nested_example :
    let outer := probes outerExample empty
    let key := muKey outer.1.1 outer.1.2
    let entry := Cache.intern outer.2.nodes key
    let allocated := {outer.2 with nodes := entry.2}
    let inner := probes (innerExample (.interned entry.1.identity)) allocated
    key ≠ muKey inner.1.1 inner.1.2 := by
  let outer := probes outerExample empty
  let key := muKey outer.1.1 outer.1.2
  let entry := Cache.intern outer.2.nodes key
  let allocated := {outer.2 with nodes := entry.2}
  apply nested_probes_separate SourceBuilt.empty outerExample (innerExample (.interned entry.1.identity))
    (no_captures outerExample (by simp [outerExample, captures, edgeCaptures, manyCaptures]) empty)
  · intro value member
    have same : value = .reference (.interned entry.1.identity) := by
      simpa [innerExample, captures, edgeCaptures, manyCaptures] using member
    subst value
    exact reference_available allocated _ (reserved_reference_issued outer.2.nodes key
      (InternedConstructorTemplates.probes_correct outerExample empty empty_valid).1.2)
  · cbv
  · left
    dsimp only [entry, key, outer]
    cbv
    exact List.Mem.head _

end MicroCFTA.InternedConstructionProvenance
