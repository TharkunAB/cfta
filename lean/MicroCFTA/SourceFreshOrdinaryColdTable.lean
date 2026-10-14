import MicroCFTA.SourceFreshOrdinaryColdSharedTermination

/-!
# Finite repaired cold tables and exact row replay

The actual final issued counter bounds every stored row identity. The
ascending key readback has the exact map domain. Every nonempty child has
a declared row. Each stored row replays its identical ordered edges without
allocation in the final cache. Language preservation is a separate target.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedRecordCoherence InternedNestedProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Inputs ResidentRows CoveredRows put_extends)
open SourcePreparedSharedRows (reference)

/-- Every first-written row remains present throughout an actual repaired trace. -/
theorem Trace.extends [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) : Extends seen result := by
  induction trace with
  | nil => exact extends_refl _
  | empty rest ih | known value identity edges same present rest ih => exact ih
  | read value identity fuel edges same absent done rest ih => exact extends_trans (put_extends _ _ _ absent) ih

/-- Completion declares each initial nonempty pending identity in the final map. -/
theorem Trace.pending_done [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (value : Value Symbol Guard) (member : value ∈ pending)
    (identity : Nat) (same : reference value = some identity) : ∃ edges, result identity = some edges := by
  induction trace with
  | nil => cases member
  | empty rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · exact ih member
  | known first key edges firstRef present rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have equal := Option.some.inj (firstRef.symm.trans same)
        subst identity
        exact ⟨edges, rest.extends key edges present⟩
      · exact ih member
  | read first key fuel edges firstRef absent done rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have equal := Option.some.inj (firstRef.symm.trans same)
        subst identity
        exact ⟨edges, rest.extends key edges (by simp [Cache.put])⟩
      · exact ih (List.mem_append_right _ member)

/-- A completed repaired walk declares all nonempty children of every stored row. -/
theorem Trace.closed [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (old : CoveredRows seen result) : CoveredRows result result := by
  induction trace with
  | nil => exact old
  | empty rest ih | known value identity edges same present rest ih => exact ih old
  | @read seen state after pending result final value identity fuel edges same absent read rest ih =>
      apply ih
      intro key values present edge edgeIn child childIn next childRef
      by_cases equal : key = identity
      · subst key
        have sameEdges : edges = values := by simpa [Cache.put] using present
        subst values
        exact rest.pending_done child
          (List.mem_append_left _ (List.mem_flatMap.mpr ⟨edge, edgeIn, childIn⟩)) next childRef
      · exact old key values (by simpa [Cache.put, equal] using present) edge edgeIn child childIn next childRef

/-- Each stored row has an available closed root that replays the exact row without cache effects. -/
def ReplayedRows [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (rows : Rows Symbol Guard) : Prop :=
  ∀ identity edges, rows identity = some edges → ∃ value fuel, Available state value ∧ reference value = some identity ∧
    value.free = [] ∧ MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges state

/-- Actual repaired read replay retains all earlier rows after cache growth. -/
theorem ReplayedRows.grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (rows : Rows Symbol Guard) (valid : Valid before) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (correct : ReplayedRows before rows) : ReplayedRows after rows := by
  intro identity edges present
  obtain ⟨value, fuel, available, same, closed, read⟩ := correct identity edges present
  exact ⟨value, fuel, available.grows before after growth history, same, closed,
    MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel value before after valid edges before read growth⟩

/-- Every actual first read supplies an allocation-free exact final-cache replay of its row. -/
theorem Trace.replayed [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (inputs : Inputs state pending) (correct : ReplayedRows state seen) : ReplayedRows final result := by
  induction trace with
  | nil => exact correct
  | empty rest ih | known value identity edges same present rest ih =>
      exact ih semantic covered (fun value member => inputs value (List.mem_cons_of_mem _ member)) correct
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value state semantic covered own.1 own.2
      have afterSemantic : SemanticHeap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
      have afterCovered : Covered [] after := by simpa only [done, MergedSourceExposure.Result.state] using checked.covered
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have earlier := ReplayedRows.grows state after seen semantic.1.normal.facts.coherent.valid growth history correct
      have inserted : ReplayedRows after (Cache.put seen identity edges) := by
        intro key values present
        by_cases equal : key = identity
        · subst key
          have sameEdges : edges = values := by simpa [Cache.put] using present
          subst values
          exact ⟨value, fuel, own.1.grows state after growth history, same, own.2,
            MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel value state after
              semantic.1.normal.facts.coherent.valid edges after done (grows_refl _)⟩
        · exact earlier key values (by simpa [Cache.put, equal] using present)
      have next : Inputs after (edges.flatMap EdgeValue.children ++ pending) := by
        intro child member
        rcases List.mem_append.mp member with first | later
        · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
          exact ⟨afterSemantic.1.normal.facts.cached.edges edge.entry.key edge (checked.edges edges after done edge edgeIn) child childIn,
            checked.closed edges after done edge edgeIn child childIn⟩
        · exact ⟨(tail child later).1.grows state after growth history, (tail child later).2⟩
      exact ih afterSemantic afterCovered next inserted

/-- Ascending map readback selects exactly the resident rows in the actual final issued range. -/
def keys (state : State Symbol Guard) (rows : Rows Symbol Guard) : List Nat :=
  (List.range state.nodes.next).filter (fun identity => (rows identity).isSome)

/-- The finite key readback follows the native map's strictly ascending identity order. -/
theorem keys_ascending (state : State Symbol Guard) (rows : Rows Symbol Guard) :
    (keys state rows).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- Resident rows have a finite distinct key list with exactly their actual map domain. -/
theorem keys_exact (state : State Symbol Guard) (facts : Facts state) (rows : Rows Symbol Guard) (resident : ResidentRows state rows) :
    (keys state rows).Nodup ∧ ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys state rows := by
  refine ⟨List.nodup_range.filter _, ?_⟩
  intro identity
  constructor
  · rintro ⟨edges, present⟩
    obtain ⟨value, available, same, _⟩ := resident identity edges present
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (SourcePreparedSharedRows.reference_bounded state facts value available identity same),
      by simp [present]⟩
  · intro member
    have present := (List.mem_filter.mp member).2
    cases found : rows identity with
    | none => simp [found] at present
    | some edges => exact ⟨edges, rfl⟩

/-- A general closed root gives a finite exact map domain, closed children, and exact final-cache row replay. -/
theorem cold_table [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ rows after outer inner, Trace state (fun _ => none) [value] rows after ∧
      SemanticHeap after ∧ Covered [] after ∧ InternedOpenDepthReadback.Heap after ∧ Grows state after ∧
      Extends state.nodes.issued after.nodes.issued ∧ ResidentRows after rows ∧ ReplayedRows after rows ∧
      CoveredRows rows rows ∧ (keys after rows).Nodup ∧
      (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys after rows) ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner state (fun _ => none) [value] = .done rows after := by
  obtain ⟨rows, after, outer, inner, trace, afterHeap, stable⟩ :=
    SourceFreshOrdinaryColdSharedTermination.cold_finite state semantic covered heap value available closed
  have inputs : Inputs state [value] := by intro child member; simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨afterSemantic, afterCovered, growth, history, _, resident⟩ := trace.correct semantic covered inputs noRows
  have replayed := trace.replayed semantic covered inputs (by intro identity edges absent; cases absent)
  have allChildren := trace.closed (by intro identity edges absent; cases absent)
  obtain ⟨distinct, domain⟩ := keys_exact after afterSemantic.1.normal.facts rows resident
  exact ⟨rows, after, outer, inner, trace, afterSemantic, afterCovered, afterHeap, growth, history,
    resident, replayed, allChildren, distinct, domain, stable⟩

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
