import MicroCFTA.EqualityRawLeafInventory
import MicroCFTA.EqualityLeafProjectionActualMeet
import MicroCFTA.EqualityLeafProjectionRepresentation

/-!
# Physical compiler for the finite raw leaf carrier

The generated inventory supplies actual source row requests. Complete cache
readback is exact for every finite predicate, including noncanonical initial
guards. The source intersection discharges the recursive worker contracts.
-/
namespace MicroCFTA.EqualityRawLeafCompiler
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedFreshProbeKeys InternedEdgeResidency InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityRawLeafInventory
open EqualityRawLeafConstruction (ConstraintKey)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Build selected alternatives through actual raw source constructor requests. -/
noncomputable def build (leaf : Leaf initial symbols) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations (rawChoices leaf))

/-- Read exact finite alternatives through their complete physical keys. -/
def read (value : Value (Fin symbols) ConstraintKey) : Leaf initial symbols :=
  fun symbol row => EqualityRawLeafConstruction.read value symbol row.val

/-- Actual finite source construction decodes to exactly the selected raw alternatives. -/
theorem build_read (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) : read (run (build leaf) state).1 = leaf := by
  have decoded := EqualityRawLeafConstruction.build_read (rawChoices leaf) state facts.coherent facts.linked
  change EqualityRawLeafConstruction.read (run (build leaf) state).1 = EqualityRawLeafIdentity.denote (rawChoices leaf) at decoded
  rw [choices_exact] at decoded
  funext symbol row
  change EqualityRawLeafConstruction.read (run (build leaf) state).1 symbol row.val = leaf symbol row
  rw [decoded]
  exact propext (interpret_row leaf symbol row)

/-- The finite source constructor exposes every complete outgoing key and no other key. -/
theorem build_keys (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (key : EdgeKey (Fin symbols) ConstraintKey) :
    (∃ edge ∈ nodeEdges (run (build leaf) state).1, edge.entry.key = key) ↔
      ∃ symbol row, leaf symbol row ∧ EqualityRawLeafConstruction.key (symbol, row.val.val) = key := by
  rw [build, EqualityRawLeafConstruction.build_keys _ state facts.coherent facts.linked]
  constructor
  · rintro ⟨declaration, member, _, same⟩
    obtain ⟨⟨symbol, raw⟩, rawMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨⟨actual, row⟩, choiceMember, equal⟩ := List.mem_map.mp rawMember
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨actual, row, (choices_member leaf actual row).mp choiceMember, same⟩
  · rintro ⟨symbol, row, member, same⟩
    exact ⟨(symbol, row.val.val), List.mem_map.mpr ⟨(symbol, row.val),
      List.mem_map.mpr ⟨(symbol, row), (choices_member leaf symbol row).mpr member, rfl⟩, rfl⟩,
      row.property.2, same⟩

/-- The finite raw compiler preserves complete available records. -/
theorem leaves_available : LeafAvailable (build (initial := initial) (symbols := symbols)) :=
  fun leaf state facts => EqualityRawLeafAvailability.raw_leaves (rawChoices leaf) state facts

/-- The source request keys satisfy all literal constructor safety checks. -/
theorem build_safe (leaf : Leaf initial symbols) : Safe (build leaf) := EqualityRawLeafConstruction.build_safe _

/-- Every finite raw leaf supplies an ordinary physical worker input. -/
theorem leaves_ordinary : EqualityLeafProjectionCompileOrdinary.LeafOrdinary (build (initial := initial) (symbols := symbols)) :=
  fun leaf state facts => EqualityRawLeafAvailability.raw_ordinary (rawChoices leaf) state facts

/-- Build the finite target and call the actual physical source intersection. -/
noncomputable def meet (target : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  EqualityLeafProjectionActualMeet.rawMeet (rawChoices target) value

/-- Actual source leaf intersection preserves the recursive worker's full payload contract. -/
theorem meet_available : EqualityLeafProjectionEditAvailability.MeetAvailable (meet (initial := initial) (symbols := symbols)) :=
  fun target => EqualityLeafProjectionActualMeet.raw_meet_available (rawChoices target)

/-- Actual source leaf intersection derives safe complete-key requests. -/
theorem meet_safe (target : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey) : Safe (meet target value) :=
  EqualityLeafProjectionActualMeet.raw_meet_safe (rawChoices target) value

/-- Actual stateful leaf intersection has exact complete raw readback after target construction. -/
theorem meet_raw_read (target before : Leaf initial symbols) (built state : State (Fin symbols) ConstraintKey)
    (builtFacts : Facts built) (facts : Facts state)
    (growth : Grows (run (build before) built).2 state) :
    EqualityRawLeafConstruction.read (run (meet target (run (build before) built).1) state).1 =
      interpret (intersect target before) := by
  let targetResult := run (build target) state
  have targetFacts := leaves_available target state facts
  have targetGrowth : Grows state targetResult.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have decoded := EqualityRawLeafProduct.intersect_read (rawChoices target) (rawChoices before) state built targetResult.2
    facts.coherent builtFacts.coherent targetFacts.1.coherent facts.linked builtFacts.linked targetFacts.1.linked
    (grows_refl targetResult.2) (grows_trans growth targetGrowth)
  rw [choices_exact, choices_exact] at decoded
  simp only [meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind]
  rw [intersect_exact]
  exact decoded

/-- The finite raw carrier reads exactly the actual stateful intersection result. -/
theorem meet_read (target before : Leaf initial symbols) (built state : State (Fin symbols) ConstraintKey)
    (builtFacts : Facts built) (facts : Facts state)
    (growth : Grows (run (build before) built).2 state) :
    read (run (meet target (run (build before) built).1) state).1 = intersect target before := by
  have decoded := meet_raw_read target before built state builtFacts facts growth
  funext symbol row
  exact (congrArg (fun node => node symbol row.val) decoded).trans (propext (interpret_row _ symbol row))

/-- Equal raw row predicates give complete-record equality after their finite requests complete. -/
theorem raw_records (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (left right after : State (Fin symbols) ConstraintKey)
    (leftValid : Valid left) (rightValid : Valid right) (coherent : Coherent after)
    (leftGrowth : Grows (run (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations first)) left).2 after)
    (rightGrowth : Grows (run (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations second)) right).2 after)
    (same : EqualityRawLeafIdentity.denote first = EqualityRawLeafIdentity.denote second) :
    (run (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations first)) left).1 =
      (run (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations second)) right).1 :=
  EqualityRawLeafIdentity.same_records _ _ left right after leftValid rightValid coherent leftGrowth rightGrowth
    ((EqualityRawLeafIdentity.declarations_iff first second).mpr same)

/-- The actual leaf intersection returns the complete compiled result in a later finite common cache. -/
theorem meet_record (target before : Leaf initial symbols) (built state resultState after : State (Fin symbols) ConstraintKey)
    (builtFacts : Facts built) (facts : Facts state) (resultFacts : Facts resultState) (afterCoherent : Coherent after)
    (inputGrowth : Grows (run (build before) built).2 state)
    (meetGrowth : Grows (run (meet target (run (build before) built).1) state).2 after)
    (resultGrowth : Grows (run (build (intersect target before)) resultState).2 after) :
    (run (meet target (run (build before) built).1) state).1 = (run (build (intersect target before)) resultState).1 := by
  let targetResult := run (build target) state
  have targetFacts := leaves_available target state facts
  have decoded := meet_raw_read target before built state builtFacts facts inputGrowth
  by_cases identity : targetResult.1.referenceOf = (run (build before) built).1.referenceOf
  · have exactRun : run (meet target (run (build before) built).1) state = targetResult := by
      simp only [meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind]
      change run (EqualityRawLeafProduct.intersect targetResult.1 (run (build before) built).1) targetResult.2 = targetResult
      simp only [EqualityRawLeafProduct.intersect, identity, ↓reduceIte, run]
    rw [exactRun] at decoded meetGrowth ⊢
    have same : EqualityRawLeafIdentity.denote (rawChoices target) =
        EqualityRawLeafIdentity.denote (rawChoices (intersect target before)) := by
      have targetRead := EqualityRawLeafConstruction.build_read (rawChoices target) state facts.coherent facts.linked
      change EqualityRawLeafConstruction.read targetResult.1 = EqualityRawLeafIdentity.denote (rawChoices target) at targetRead
      exact targetRead.symm.trans (decoded.trans (choices_exact _).symm)
    exact raw_records _ _ state resultState after facts.coherent.valid resultFacts.coherent.valid afterCoherent
      meetGrowth resultGrowth same
  · obtain ⟨rows, exactWork⟩ := EqualityRawLeafProgress.orderedProduct_certified (rawChoices target) (rawChoices before)
      state built facts.coherent builtFacts.coherent facts.linked builtFacts.linked
    have exactRun : run (meet target (run (build before) built).1) state =
        run (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations rows)) targetResult.2 := by
      simp only [meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind]
      change run (EqualityRawLeafProduct.intersect targetResult.1 (run (build before) built).1) targetResult.2 = _
      rw [EqualityRawLeafProduct.intersect, ite_eq_right identity]
      exact congrArg (fun work => run work targetResult.2) exactWork
    rw [exactRun] at decoded meetGrowth ⊢
    have same : EqualityRawLeafIdentity.denote rows = EqualityRawLeafIdentity.denote (rawChoices (intersect target before)) := by
      have outputRead := EqualityRawLeafConstruction.build_read rows targetResult.2 targetFacts.1.coherent targetFacts.1.linked
      exact outputRead.symm.trans (decoded.trans (choices_exact _).symm)
    exact raw_records _ _ targetResult.2 resultState after targetFacts.1.coherent.valid resultFacts.coherent.valid afterCoherent
      meetGrowth resultGrowth same

/-- Executing the actual meet first constructs a finite later cache for its exact compiled result. -/
theorem meet_completed (target before : Leaf initial symbols) (built state : State (Fin symbols) ConstraintKey)
    (builtFacts : Facts built) (facts : Facts state)
    (inputGrowth : Grows (run (build before) built).2 state) :
    let actual := run (meet target (run (build before) built).1) state
    let prepared := run (build (intersect target before)) actual.2
    Facts prepared.2 ∧ Grows actual.2 prepared.2 ∧
      EqualityLeafProjectionRepresentation.Represents build (.leaf (intersect target before)) prepared.2 actual.1 := by
  let actual := run (meet target (run (build before) built).1) state
  let prepared := run (build (intersect target before)) actual.2
  have inputReplay := replay (build before) built state builtFacts.coherent.valid inputGrowth
  have available := leaves_available before state facts
  rw [inputReplay] at available
  have actualFacts := meet_available target (run (build before) built).1 state facts available.2
  have preparedFacts := leaves_available (intersect target before) actual.2 actualFacts.1
  have growth : Grows actual.2 prepared.2 := (InternedConstructorTemplates.run_correct _ actual.2 actualFacts.1.coherent.valid).2
  have same := meet_record target before built state actual.2 prepared.2 builtFacts facts actualFacts.1
    preparedFacts.1.coherent inputGrowth growth (grows_refl prepared.2)
  change actual.1 = prepared.1 at same
  refine ⟨preparedFacts.1, growth, ?_⟩
  change run (build (intersect target before)) prepared.2 = (actual.1, prepared.2)
  rw [same]
  exact replay (build (intersect target before)) actual.2 prepared.2 actualFacts.1.coherent.valid (grows_refl prepared.2)

/-- A represented original leaf gets an exact represented edited leaf after finite preparation. -/
theorem represented_meet (target before : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (value : Value (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : EqualityLeafProjectionRepresentation.Represents build (.leaf before) state value) :
    let actual := run (meet target value) state
    let prepared := run (build (intersect target before)) actual.2
    Facts prepared.2 ∧ Grows actual.2 prepared.2 ∧
      EqualityLeafProjectionRepresentation.Represents build (.leaf (intersect target before)) prepared.2 actual.1 := by
  have exactInput : run (build before) state = (value, state) := represented
  have growth : Grows (run (build before) state).2 state := by rw [exactInput]; exact grows_refl state
  have completed := meet_completed target before state state facts facts growth
  simpa only [exactInput] using completed

/-- The raw leaf requirement is allocation-free and retains the complete original record. -/
theorem require_exact (leaf : Leaf initial symbols) (paths : List EqualityLeafProjectionSyntax.Path)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    EqualityLeafProjectionWorkers.require paths (run (build leaf) state).1 =
      .pure (some (if EqualityLeafProjectionSyntax.fits paths 0 then (run (build leaf) state).1 else .empty)) :=
  EqualityRawLeafAvailability.built_require paths (rawChoices leaf) state facts

end MicroCFTA.EqualityRawLeafCompiler
