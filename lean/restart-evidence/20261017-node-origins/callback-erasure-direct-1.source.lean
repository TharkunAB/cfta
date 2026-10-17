import MicroCFTA.InternedDeepLocalNormal
import MicroCFTA.InternedFreshOrdinaryDependencies
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Exact reconstruction after actual callback erasure

A normalized callback retains its argument below a constructor or as one
bare reference. If the argument has no deep occurrence, bare-self erasure
removes it from the complete free set. Later stored reconstruction then
has the same full outcome for every replacement of that argument.

This result applies to the returned callback record. It does not exchange
the original callback inputs or equate an earlier Mu body with its probe.
-/
namespace MicroCFTA.SourceCurrentNativeCallbackErasure
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryContext (Context)
open InternedDeepFreeDepth (deepNames)
open InternedBinderProtocol (Reference)
variable {Symbol Guard : Type}

/-- Remove a bare callback argument after the actual root filter has run. -/
def eraseSelf (name : Reference) (value : Value Symbol Guard) : Value Symbol Guard :=
  if value.referenceOf = .ref name then .empty else value

/-- Actual local normal form and no deep occurrence exclude the erased argument. -/
theorem erased_absent (name : Reference) (value : Value Symbol Guard)
    (normal : InternedDeepLocalNormal.Local name value) (unused : name ∉ deepNames value) :
    name ∉ (eraseSelf name value).free := by
  unfold eraseSelf
  split
  · simp only [Value.free, List.not_mem_nil, not_false_eq_true]
  · rename_i different
    intro present
    rcases normal present with deep | bare
    · exact unused deep
    · exact different (by simp only [bare, Value.referenceOf])

private theorem erased_available (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (available : Available state value) :
    Available state (eraseSelf name value) := by
  unfold eraseSelf
  split
  · exact InternedNestedProvenance.empty_available state
  · exact available

/-- The literal callback produces an available erased record with no free argument. -/
theorem callback_result [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before : State Symbol Guard) (context : Context before environment)
    (argument : Available before (.reference name)) (value : Value Symbol Guard)
    (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryFacts.callback expression environment name before = .done value after)
    (unused : name ∉ deepNames value) :
    Context after environment ∧ Available after (eraseSelf name value) ∧
      name ∉ (eraseSelf name value).free := by
  have retained : Context after environment := by
    simpa only [actual, Outcome.state] using context.callback expression name argument
  have available := (InternedFreshOrdinaryFacts.callback_verified expression environment name before
    context.normal.facts (context.local name argument).inputs).result value after actual
  have localNormal := InternedDeepLocalNormal.callback_local expression environment name before
    context.normal (context.local name argument).inputs value after actual
  exact ⟨retained, erased_available name value after available, erased_absent name value localNormal unused⟩

/-- Any two argument replacements give identical full outcomes at a later current heap. -/
theorem callback_replace [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before : State Symbol Guard) (context : Context before environment)
    (argument : Available before (.reference name)) (value : Value Symbol Guard)
    (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryFacts.callback expression environment name before = .done value after)
    (unused : name ∉ deepNames value) (current : State Symbol Guard)
    (growth : Grows after current) (history : Extends after.nodes.issued current.nodes.issued)
    (coherent : Coherent current) (first second : Value Symbol Guard) :
    InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
        (InternedStoredSubstitutionRebind.replacement name first) current =
      InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
        (InternedStoredSubstitutionRebind.replacement name second) current := by
  have returned := callback_result expression environment name before context argument value after actual unused
  apply InternedFreshOrdinaryStoredSubstitution.execute_congr (eraseSelf name value) _ _ current coherent
    (returned.2.1.grows after current growth history)
  intro other member
  have different : other ≠ name := fun same => returned.2.2 (same ▸ member)
  simp only [InternedStoredSubstitutionRebind.replacement, different, ↓reduceIte]

/-- A completed erased reconstruction replays exactly when its argument replacement changes. -/
theorem callback_replay [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before : State Symbol Guard) (context : Context before environment)
    (argument : Available before (.reference name)) (value : Value Symbol Guard)
    (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryFacts.callback expression environment name before = .done value after)
    (unused : name ∉ deepNames value) (first second result : Value Symbol Guard)
    (final current : State Symbol Guard)
    (completed : InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
      (InternedStoredSubstitutionRebind.replacement name first) after = .done result final)
    (growth : Grows final current) :
    InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
      (InternedStoredSubstitutionRebind.replacement name second) current = .done result current := by
  have returned := callback_result expression environment name before context argument value after actual unused
  apply InternedFreshOrdinaryStoredSubstitution.execute_binding_replay (eraseSelf name value) _ _ after current
    returned.1.normal.facts.coherent returned.2.1 _ result final completed growth
  intro other member
  have different : other ≠ name := fun same => returned.2.2 (same ▸ member)
  simp only [InternedStoredSubstitutionRebind.replacement, different, ↓reduceIte]

private theorem native_context [DecidableEq (EdgeKey Symbol Guard)]
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before body) :
    Context before (InternedStoredSubstitution.leaves body) :=
  ⟨semantic.1.normal, InternedStoredSubstitution.leaves_available body before available,
    semantic.1.profiles, semantic.1.freeNames⟩

/-- The actual native callback derives the same erased-record facts from its current source inputs. -/
theorem native_callback_result [DecidableEq (EdgeKey Symbol Guard)]
    (old name : Reference) (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before body) (argument : Available before (.reference name))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.callback old body name before = .done value after)
    (unused : name ∉ deepNames value) :
    Context after (InternedStoredSubstitution.leaves body) ∧
      Available after (eraseSelf name value) ∧ name ∉ (eraseSelf name value).free := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body name before before semantic.1.normal.facts available] at actual
  exact callback_result _ _ name before (native_context body before semantic available) argument value after actual unused

/-- Actual native callback erasure removes all later dependence on its argument replacement. -/
theorem native_callback_replace [DecidableEq (EdgeKey Symbol Guard)]
    (old name : Reference) (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before body) (argument : Available before (.reference name))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.callback old body name before = .done value after)
    (unused : name ∉ deepNames value) (current : State Symbol Guard)
    (growth : Grows after current) (history : Extends after.nodes.issued current.nodes.issued)
    (coherent : Coherent current) (first second : Value Symbol Guard) :
    InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
        (InternedStoredSubstitutionRebind.replacement name first) current =
      InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf name value)
        (InternedStoredSubstitutionRebind.replacement name second) current := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body name before before semantic.1.normal.facts available] at actual
  exact callback_replace _ _ name before (native_context body before semantic available) argument value after actual unused
    current growth history coherent first second

end MicroCFTA.SourceCurrentNativeCallbackErasure
