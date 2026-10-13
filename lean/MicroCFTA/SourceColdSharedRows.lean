import MicroCFTA.SourcePreparedSharedRows

/-!
# Stateful cold shared-row traversal

The source worklist stores each first exposed row at its canonical identity.
Each actual cold read returns the cache used by the next worklist step.
Read errors and exhausted proof bounds retain that exact cache.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedColdReaderClosedInputs
open SourcePreparedSharedRows (reference)

/-- The shared map retains complete physical edge payloads in source order. -/
abbrev Rows (Symbol Guard : Type) := Cache.Table Nat (List (EdgeValue Symbol Guard))

/-- Cold shared traversal preserves distinct reader failures and exact effects. -/
inductive Result (Symbol Guard : Type) where
  | done (rows : Rows Symbol Guard) (state : State Symbol Guard)
  | unresolved (name : InternedBinderProtocol.Reference) (state : State Symbol Guard)
  | pending (key : InternedBinderProtocol.NodeKey) (state : State Symbol Guard)
  | exhausted (state : State Symbol Guard)

/-- Continue from the exact cache of a successful source row read. -/
def readThen (read : MergedSourceExposure.Result Symbol Guard)
    (next : List (EdgeValue Symbol Guard) → State Symbol Guard → Result Symbol Guard) : Result Symbol Guard :=
  match read with
  | .done edges after => next edges after
  | .unresolved name after => .unresolved name after
  | .pending key after => .pending key after
  | .exhausted after => .exhausted after

/-- Follow the native worklist and store each first actual cold row read. -/
def collect [DecidableEq (EdgeKey Symbol Guard)] : Nat → Nat → State Symbol Guard → Rows Symbol Guard →
    List (Value Symbol Guard) → Result Symbol Guard
  | 0, _, state, _, _ => .exhausted state
  | _ + 1, _, state, seen, [] => .done seen state
  | fuel + 1, readFuel, state, seen, value :: rest =>
      match value with
      | .empty => collect fuel readFuel state seen rest
      | .reference name => .unresolved name state
      | .node entry .. | .union entry .. | .mu entry .. =>
          match seen entry.identity with
          | some _ => collect fuel readFuel state seen rest
          | none => readThen (MergedSourceExposure.nodeEdges readFuel value state) fun edges after =>
              collect fuel readFuel after (Cache.put seen entry.identity edges)
                (edges.flatMap EdgeValue.children ++ rest)

/-- A finite actual source trace retains every read bound and intermediate cache. -/
inductive Trace [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → Rows Symbol Guard →
    List (Value Symbol Guard) → Rows Symbol Guard → State Symbol Guard → Prop where
  | nil (state seen) : Trace state seen [] seen state
  | empty (rest : Trace state seen pending result final) : Trace state seen (.empty :: pending) result final
  | known (value : Value Symbol Guard) (identity : Nat) (edges : List (EdgeValue Symbol Guard))
      (same : reference value = some identity) (present : seen identity = some edges)
      (rest : Trace state seen pending result final) : Trace state seen (value :: pending) result final
  | read (value : Value Symbol Guard) (identity fuel : Nat) (edges : List (EdgeValue Symbol Guard))
      (same : reference value = some identity) (absent : seen identity = none)
      (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after)
      (rest : Trace after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ pending) result final) :
      Trace state seen (value :: pending) result final

/-- Every pending source value is available and closed in the current cache. -/
def Inputs (state : State Symbol Guard) (pending : List (Value Symbol Guard)) : Prop :=
  ∀ value ∈ pending, Available state value ∧ value.free = []

/-- Every stored row retains its original root and resident closed child payloads. -/
def ResidentRows (state : State Symbol Guard) (rows : Rows Symbol Guard) : Prop :=
  ∀ identity edges, rows identity = some edges → ∃ value,
    Available state value ∧ reference value = some identity ∧ value.free = [] ∧
      Edges state edges ∧ ClosedEdges edges

/-- Stored source rows retain their provenance through later physical cache growth. -/
theorem ResidentRows.grows (before after : State Symbol Guard) (rows : Rows Symbol Guard)
    (resident : ResidentRows before rows) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) : ResidentRows after rows := by
  intro identity edges present
  obtain ⟨value, available, same, closed, edgesResident, edgesClosed⟩ := resident identity edges present
  exact ⟨value, available.grows before after growth history, same, closed,
    fun edge member => edge_grows before after growth edge (edgesResident edge member), edgesClosed⟩

/-- A successful closed read at any sufficient bound has closed children. -/
theorem read_closed_of_done [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after) :
    ClosedEdges edges := by
  obtain ⟨otherFuel, otherEdges, otherAfter, otherDone, _, _, _, _, _, _, children, stable⟩ :=
    MergedColdReaderFacts.read_closed value state facts prepared available closed
  have first := MergedColdReaderTermination.nodeEdges_stable fuel otherFuel value state (by rw [done]; trivial)
  have second := stable fuel
  rw [Nat.add_comm otherFuel fuel, first, done] at second
  exact (MergedSourceExposure.Result.done.inj second).1 ▸ children

/-- Cold expansion derives the next available closed worklist in its actual returned cache. -/
theorem next_inputs [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (pending : List (Value Symbol Guard)) (inputs : Inputs state pending)
    (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after) :
    Inputs after (edges.flatMap EdgeValue.children ++ pending) := by
  have checked := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared available
  have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
  have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, MergedSourceExposure.Result.state] using checked.history
  have afterFacts : Facts after := by simpa only [done, MergedSourceExposure.Result.state] using checked.facts
  have resident := checked.edges edges after done
  have children := read_closed_of_done fuel value state facts prepared available closed edges after done
  intro child member
  rcases List.mem_append.mp member with first | later
  · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
    exact ⟨afterFacts.cached.edges edge.entry.key edge (resident edge edgeIn) child childIn, children edge edgeIn child childIn⟩
  · exact ⟨(inputs child later).1.grows state after growth history, (inputs child later).2⟩

/-- Inserting a first cold row preserves every earlier exact stored row. -/
theorem put_extends (seen : Rows Symbol Guard) (identity : Nat) (edges : List (EdgeValue Symbol Guard))
    (absent : seen identity = none) : Extends seen (Cache.put seen identity edges) := by
  have kept := keepFirst_extends seen identity edges
  simpa only [keepFirst, absent] using kept

/-- Every finite cold trace preserves source facts, histories, closed rows, and first-write order. -/
theorem Trace.correct [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (facts : Facts state) (prepared : Prepared state)
    (inputs : Inputs state pending) (resident : ResidentRows state seen) :
    Facts final ∧ Prepared final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      NoNewMu state final ∧ Extends seen result ∧ ResidentRows final result := by
  induction trace with
  | nil state seen => exact ⟨facts, prepared, grows_refl _, extends_refl _, noNewMu_refl _, extends_refl _, resident⟩
  | empty rest ih => exact ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)) resident
  | known value identity edges same present rest ih =>
      exact ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)) resident
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun value member => inputs value (List.mem_cons_of_mem _ member)
      have checked := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared own.1
      have afterFacts : Facts after := by simpa only [done, MergedSourceExposure.Result.state] using checked.facts
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have unchanged : NoNewMu state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.unchanged
      have afterResident : ResidentRows after (Cache.put seen identity edges) := by
        intro key values present
        by_cases equal : key = identity
        · subst key
          have equal : edges = values := by simpa [Cache.put] using present
          subst values
          exact ⟨value, own.1.grows state after growth history, same, own.2, checked.edges edges after done,
            read_closed_of_done fuel value state facts prepared own.1 own.2 edges after done⟩
        · exact resident.grows state after seen growth history key values (by simpa [Cache.put, equal] using present)
      obtain ⟨finalFacts, finalPrepared, laterGrowth, laterHistory, laterUnchanged, rowsGrowth, finalRows⟩ :=
        ih afterFacts (prepared.preserve unchanged)
          (next_inputs fuel value state facts prepared own.1 own.2 edges after pending tail done) afterResident
      exact ⟨finalFacts, finalPrepared, grows_trans growth laterGrowth, extends_trans history laterHistory,
        noNewMu_trans unchanged laterUnchanged, extends_trans (put_extends seen identity edges absent) rowsGrowth, finalRows⟩

end MicroCFTA.SourceColdSharedRows
