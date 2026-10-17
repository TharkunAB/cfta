import MicroCFTA.InternedFreshOrdinaryLiveInputSupport

/-!
# Live fixed captures for normalized callback comparison

Symbolic labels distinguish names inside fixed records from varying inputs.
The actual Depth callback supplies freshness of its chosen ordinary name.
A missing-key reservation supplies freshness of its new interned name.
These facts do not compare the two callback results.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizationInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedFreeNameSemantics
open InternedBinderProtocol (Reference NodeKey)
variable {Atom : Type}

/-- Fixed names retain their reference tag; varying slots retain their lexical label. -/
def inputNames : Sum (Value Symbol Guard) Atom → List (Sum Reference Atom)
  | .inl value => value.free.map Sum.inl
  | .inr atom => [.inr atom]

/-- Surviving free-name support retains both fixed and varying labels. -/
def support (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    List (Sum Reference Atom) :=
  evaluate expression (inputs.map inputProfile) (inputs.map inputNames)

private theorem instantiated_names (names : Atom → Reference) (selected : Sum (Value Symbol Guard) Atom) :
    (input names selected).free = (inputNames selected).map (Sum.elim id names) := by
  cases selected with
  | inl value => simp [input, inputNames, List.map_map, Function.comp_def]
  | inr atom => rfl

private theorem instantiated_lists (names : Atom → Reference) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map (input names)).map Value.free =
      (inputs.map inputNames).map (List.map (Sum.elim id names)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  exact instantiated_names names selected

/-- Full syntax support commutes with each actual assignment of varying references. -/
theorem instantiated (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) :
    (support expression inputs).map (Sum.elim id names) =
      evaluate expression ((inputs.map (input names)).map InternedRootProfile.profile)
        ((inputs.map (input names)).map Value.free) := by
  rw [input_profiles, instantiated_lists, evaluate_map]
  rfl

/-- Every actual raw result has exactly the instantiated symbolic free-name support. -/
theorem actual_free [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (name : Reference) :
    name ∈ value.free ↔ name ∈ (support expression inputs).map (Sum.elim id names) := by
  rw [instantiated]
  exact (InternedFreshOrdinaryFreeNames.build_free expression _ before context.normal context.inputs
    context.freeNames context.profiles).result value after actual name

/-- A surviving fixed label comes from one actual fixed captured record. -/
theorem fixed_origin (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (name : Reference) (member : .inl name ∈ support expression inputs) :
    ∃ value, .inl value ∈ inputs ∧ name ∈ value.free := by
  obtain ⟨selectedNames, present, included⟩ := evaluate_origins expression (inputs.map inputProfile)
    (inputs.map inputNames) (.inl name) member
  obtain ⟨selected, source, same⟩ := List.mem_map.mp present
  rw [← same] at included
  cases selected with
  | inl value =>
      refine ⟨value, source, ?_⟩
      obtain ⟨original, free, same⟩ := List.mem_map.mp included
      cases same
      exact free
  | inr atom => simp [inputNames] at included

/-- A normalized callback exposes every live fixed name distinct from its supplied argument. -/
theorem callback_fixed [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (argument : Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (available : Available before (.reference argument)) (value : Value Symbol Guard)
    (actual : callback body (inputs.map (input names)) argument before = .done value after)
    (name : Reference) (member : .inl name ∈ support (.binder true body) inputs)
    (different : name ≠ argument) : name ∈ value.free := by
  have mapped : name ∈ (support (.binder true body) inputs).map (Sum.elim id names) :=
    List.mem_map.mpr ⟨.inl name, member, rfl⟩
  rw [instantiated, InternedFreeNameForm.binder_captures] at mapped
  exact (InternedFreshOrdinarySourceFreeNames.callback_other body _ argument before context.normal
    (context.local argument available).inputs context.freeNames context.profiles value after actual name different).mpr mapped

/-- The actual completed Depth callback makes the chosen ordinary marker fresh for live fixed support. -/
theorem ordinary_fresh_fixed [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (depth : Value Symbol Guard)
    (actual : callback body (inputs.map (input names)) .depth before = .done depth after) :
    .inl (.uninterned (ordinaryLevel depth)) ∉ support (.binder true body) inputs := by
  intro member
  exact ordinary_fresh depth (callback_fixed body inputs names .depth before after context
    (InternedNestedProvenance.depth_available before) depth actual _ member (by intro same; cases same))

/-- The actual missing-key reservation makes its interned marker fresh for fixed source support. -/
theorem reserved_fresh_fixed [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (state : State Symbol Guard)
    (context : Context state (inputs.map (input names))) (key : NodeKey)
    (missing : state.nodes.table key = none) :
    .inl (.interned (Cache.intern state.nodes key).1.identity) ∉ support expression inputs := by
  intro member
  obtain ⟨value, source, free⟩ := fixed_origin expression inputs _ member
  have available : Available state value := context.inputs value (List.mem_map.mpr ⟨.inl value, source, rfl⟩)
  obtain ⟨issuedKey, issued⟩ := available.issued _ free
  have smaller := context.normal.facts.coherent.valid.2.1 _ _ issued
  have identity : (Cache.intern state.nodes key).1.identity = state.nodes.next := by
    simp [Cache.intern, missing, reserve, install]
  rw [identity] at smaller
  exact Nat.lt_irrefl _ smaller

end MicroCFTA.SourceCurrentNativeNormalizationInputs
