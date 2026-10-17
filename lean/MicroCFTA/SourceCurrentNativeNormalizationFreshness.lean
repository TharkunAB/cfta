import MicroCFTA.SourceCurrentNativeNormalizationInputs

/-!
# Fresh callback arguments beside all live lexical inputs

Actual probe execution excludes its chosen ordinary argument from every
live name. Actual reservation excludes its new interned argument from
every live name. Varying lexical inputs can alias one another.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizationFreshness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedFreeNameSemantics SourceCurrentNativeNormalizationInputs
open InternedBinderProtocol (Reference NodeKey)

/-- Every instantiated live name comes from one actual lexical input. -/
theorem support_origin (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (name : Reference) (member : name ∈ (support expression inputs).map (Sum.elim id names)) :
    ∃ value ∈ inputs.map (input names), name ∈ value.free := by
  rw [instantiated] at member
  obtain ⟨selected, source, included⟩ := evaluate_origins expression
    ((inputs.map (input names)).map InternedRootProfile.profile)
    ((inputs.map (input names)).map Value.free) name member
  obtain ⟨value, present, same⟩ := List.mem_map.mp source
  exact ⟨value, present, same ▸ included⟩

/-- A completed callback retains each live name distinct from its supplied argument. -/
theorem callback_name [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (argument : Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (available : Available before (.reference argument)) (value : Value Symbol Guard)
    (actual : callback body (inputs.map (input names)) argument before = .done value after)
    (name : Reference) (member : name ∈ (support (.binder true body) inputs).map (Sum.elim id names))
    (different : name ≠ argument) : name ∈ value.free := by
  rw [instantiated, InternedFreeNameForm.binder_captures] at member
  exact (InternedFreshOrdinarySourceFreeNames.callback_other body _ argument before context.normal
    (context.local argument available).inputs context.freeNames context.profiles value after actual name different).mpr member

/-- The actual Depth callback makes the selected ordinary argument fresh for all live inputs. -/
theorem ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (depth : Value Symbol Guard)
    (actual : callback body (inputs.map (input names)) .depth before = .done depth after) :
    .uninterned (ordinaryLevel depth) ∉ (support (.binder true body) inputs).map (Sum.elim id names) := by
  intro member
  exact ordinary_fresh depth (callback_name body inputs names .depth before after context
    (InternedNestedProvenance.depth_available before) depth actual _ member (by intro same; cases same))

/-- A missing-key reservation makes its selected interned argument fresh for all live inputs. -/
theorem reserved (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (state : State Symbol Guard) (context : Context state (inputs.map (input names)))
    (key : NodeKey) (missing : state.nodes.table key = none) :
    .interned (Cache.intern state.nodes key).1.identity ∉ (support expression inputs).map (Sum.elim id names) := by
  intro member
  obtain ⟨value, source, free⟩ := support_origin expression inputs names _ member
  obtain ⟨issuedKey, issued⟩ := (context.inputs value source).issued _ free
  have smaller := context.normal.facts.coherent.valid.2.1 _ _ issued
  have identity : (Cache.intern state.nodes key).1.identity = state.nodes.next := by
    simp [Cache.intern, missing, reserve, install, keepFirst, put]
  rw [identity] at smaller
  exact Nat.lt_irrefl _ smaller

end MicroCFTA.SourceCurrentNativeNormalizationFreshness
