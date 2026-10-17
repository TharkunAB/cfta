import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentConstrainedCapCallbackCertificates
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Causal guard observations through native constructor calls

Actual stored substitution and optional binders use the source executor.
They retain its guard heap at every stopping state. Complete initial caches
derive finite optional-binder execution. A completed request retains the
exact selected record from its actual final table.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference NodeKey)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConstrainedCapGuardHeap (Heap Checked)
open SourceCurrentConstrainedCapGuardDepth (profile)
open SourceCurrentConstrainedCapGuardSemantics (decode evaluate)
local notation "Context" => SourceCurrentConstrainedCapSourceHistory.Context
variable {Symbol Guard : Type}

/-- The produced guard heap supplies the earlier conditional annotation store. -/
theorem stored (valid : Guard → Prop) (state : State Symbol Guard) (heap : Heap valid state) :
    SourceCurrentHereditaryConstruction.MuStored valid state := by
  intro key entry body depth ordinary present _ ordinaryAnnotated
  apply (SourceCurrentConstrainedCapGuardDepth.profile_zero_iff valid body).mp
  exact (heap key entry body depth ordinary present).trans
    ((SourceCurrentConstrainedCapGuardDepth.profile_zero_iff valid ordinary).mpr ordinaryAnnotated)

/-- Available captures extend the same joint semantic context. -/
theorem context (state : State Symbol Guard) (semantic : SemanticHeap state)
    (environment : List (Value Symbol Guard)) (available : InternedNestedProvenance.Values state environment) :
    Context state environment :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context state semantic environment available, semantic.2⟩

/-- Actual normalized callbacks retain the exact source guard observation. -/
theorem callback_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (marker : Reference)
    (state : State Symbol Guard) (joint : Context state environment)
    (available : Available state (.reference marker)) (heap : Heap valid state) :
    Checked valid (InternedFreshOrdinaryFacts.callback expression environment marker state)
      (fun value => profile valid value =
        (evaluate valid expression (SourceCurrentConstrainedCapGuardSemantics.reference marker ::
          environment.map (decode valid))).guardDepth) := by
  have localContext := joint.local marker available
  have physical := InternedFreshOrdinaryFacts.build_verified expression _ state
    localContext.base.normal.facts localContext.base.inputs
  unfold InternedFreshOrdinaryFacts.callback
  apply SourceCurrentConstrainedCapGuardHeap.bind_checked valid _ _ _ _
    (SourceCurrentConstrainedCapGuardExecution.build_profile valid expression _ state localContext heap)
  intro value after done afterHeap same
  have afterContext : Context after (.reference marker :: environment) := by
    simpa only [done, Outcome.state] using localContext.build expression
  apply SourceCurrentConstrainedCapGuardHeap.done_checked
  · exact SourceCurrentConstrainedCapGuardHeap.preserve valid after _ afterHeap
      (InternedStoredMuOrigins.filter_noNewMu marker value after)
  · rw [SourceCurrentConstrainedCapGuardNormalization.filter_profile valid marker value after
      afterContext.base.normal (physical.result value after done)]
    simpa only [List.map_cons, decode, InternedRecordDepthShape.shape, profile,
      SourceCurrentConstrainedCapGuardSemantics.reference] using same

/-- Actual stored substitution retains guard certificates through open nested binders. -/
theorem execute_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (value : Value Symbol Guard) (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state value)
    (replacements : Replacements state environment) (heap : Heap valid state) :
    Heap valid (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  (SourceCurrentConstrainedCapGuardExecution.build_profile valid _ _ state
    (context state semantic _ (inputs_available value environment state available replacements)) heap).heap

/-- Native callback compilation uses the same actual source observation and stopping heap. -/
theorem native_callback [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (body : Value Symbol Guard) (old marker : Reference) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body)
    (markerAvailable : Available state (.reference marker)) (heap : Heap valid state) :
    Checked valid (SourceRecursiveIntersectionMaybeMu.callback old body marker state)
      (fun value => profile valid value =
        (evaluate valid (encode (leaves body) [old] body)
          (SourceCurrentConstrainedCapGuardSemantics.reference marker :: (leaves body).map (decode valid))).guardDepth) := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body marker state state semantic.1.normal.facts available]
  exact callback_profile valid _ _ marker state
    (context state semantic _ (leaves_available body state available)) markerAvailable heap

/-- Actual optional binders retain every earlier writer at successful and pending outcomes. -/
theorem optional_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body) (heap : Heap valid state) :
    Heap valid (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · exact (SourceCurrentConstrainedCapGuardExecution.build_profile valid _ _ state
      (context state semantic _ (leaves_available body state available)) heap).heap
  · exact heap

/-- A completed canonical request identifies its exact final first-writer record. -/
theorem request_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : request smart depth ordinary call state = .done value after) :
    ∃ winner, after.nodeRecords (muKey depth ordinary) = some winner ∧ value = finish smart winner := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, present] at actual; cases actual
      | some winner =>
          simp only [request, installed, present] at actual
          cases actual
          exact ⟨winner, present, rfl⟩
  | none =>
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      simp only [request, installed] at actual
      change (call (.interned entry.1.identity) allocated).bind _ = .done value after at actual
      cases called : call (.interned entry.1.identity) allocated with
      | pending key stopped => simp only [called, Outcome.bind] at actual; cases actual
      | done body middle =>
          simp only [called, Outcome.bind] at actual
          obtain ⟨winner, present⟩ := keepFirst_present middle.nodeRecords (muKey depth ordinary)
            (.mu entry.1 body depth ordinary)
          dsimp only [entry] at present
          simp only [present, Option.getD_some] at actual
          cases actual
          exact ⟨winner, present, rfl⟩

/-- Complete initial caches derive finite native optional binders and retain their causal guard heap. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body) (covered : Covered [] state)
    (heap : Heap valid state) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after ∧
      SemanticHeap after ∧ Heap valid after ∧ Covered [] after ∧ Available after value ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  obtain ⟨value, after, done, afterContext, afterDepth, afterCovered, output, growth, history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body state semantic.1 available semantic.2 covered
  exact ⟨value, after, done, ⟨afterContext, afterDepth⟩,
    by simpa only [done, Outcome.state] using optional_heap valid pair body state semantic available heap,
    afterCovered, output, growth, history⟩

end MicroCFTA.SourceCurrentConstrainedCapGuardNative
