import MicroCFTA.SourceColdSharedRowsTermination
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Actual repaired cold shared-row traversal

The shared worklist calls the repaired reader directly. Finite traces retain
their individual read bounds and exact intermediate caches. Existing finite
prepared traces transfer to this executor. General nested termination is
not assumed or proved here.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedShallowHeap MergedPhysicalWarmup
open SourceColdSharedRows (Rows Result readThen Inputs ResidentRows)
open SourcePreparedSharedRows (reference)

/-- Follow the actual shared worklist with repaired cold reads and first-write rows. -/
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
          | none => readThen (MergedFreshOrdinaryExposure.nodeEdges readFuel value state) fun edges after =>
              collect fuel readFuel after (Cache.put seen entry.identity edges)
                (edges.flatMap EdgeValue.children ++ rest)

/-- A finite repaired source trace keeps actual reads, their order, and every intermediate cache. -/
inductive Trace [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → Rows Symbol Guard →
    List (Value Symbol Guard) → Rows Symbol Guard → State Symbol Guard → Prop where
  | nil (state seen) : Trace state seen [] seen state
  | empty (rest : Trace state seen pending result final) : Trace state seen (.empty :: pending) result final
  | known (value : Value Symbol Guard) (identity : Nat) (edges : List (EdgeValue Symbol Guard))
      (same : reference value = some identity) (present : seen identity = some edges)
      (rest : Trace state seen pending result final) : Trace state seen (value :: pending) result final
  | read (value : Value Symbol Guard) (identity fuel : Nat) (edges : List (EdgeValue Symbol Guard))
      (same : reference value = some identity) (absent : seen identity = none)
      (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after)
      (rest : Trace after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ pending) result final) :
      Trace state seen (value :: pending) result final

/-- Earlier prepared traces are actual repaired traces with identical rows and caches. -/
theorem of_prepared [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : SourceColdSharedRows.Trace state seen pending result final) (facts : Facts state)
    (prepared : Prepared state) (inputs : Inputs state pending) : Trace state seen pending result final := by
  induction trace with
  | nil state seen => exact .nil state seen
  | empty rest ih => exact .empty (ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)))
  | known value identity edges same present rest ih =>
      exact .known value identity edges same present (ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)))
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun value member => inputs value (List.mem_cons_of_mem _ member)
      have checked := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared own.1
      have afterFacts : Facts after := by simpa only [done, MergedSourceExposure.Result.state] using checked.facts
      have unchanged : NoNewMu state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.unchanged
      have repaired : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after := by
        rw [MergedFreshOrdinaryExposure.nodeEdges_eq fuel value state facts prepared own.1]
        exact done
      exact .read value identity fuel edges same absent repaired
        (ih afterFacts (prepared.preserve unchanged)
          (SourceColdSharedRows.next_inputs fuel value state facts prepared own.1 own.2 edges after pending tail done))

/-- Actual repaired prepared traces retain the complete earlier physical table and language interface. -/
theorem Trace.to_prepared [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (facts : Facts state)
    (prepared : Prepared state) (inputs : Inputs state pending) : SourceColdSharedRows.Trace state seen pending result final := by
  induction trace with
  | nil state seen => exact .nil state seen
  | empty rest ih => exact .empty (ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)))
  | known value identity edges same present rest ih =>
      exact .known value identity edges same present (ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)))
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun value member => inputs value (List.mem_cons_of_mem _ member)
      have original : MergedSourceExposure.nodeEdges fuel value state = .done edges after := by
        rw [← MergedFreshOrdinaryExposure.nodeEdges_eq fuel value state facts prepared own.1]
        exact done
      have checked := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared own.1
      have afterFacts : Facts after := by simpa only [original, MergedSourceExposure.Result.state] using checked.facts
      have unchanged : NoNewMu state after := by simpa only [original, MergedSourceExposure.Result.state] using checked.unchanged
      exact .read value identity fuel edges same absent original
        (ih afterFacts (prepared.preserve unchanged)
          (SourceColdSharedRows.next_inputs fuel value state facts prepared own.1 own.2 edges after pending tail original))

/-- Actual repaired traces retain complete semantic caches, first-write rows, and closed available children without preparation. -/
theorem Trace.correct [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state) (covered : InternedRecordCoherence.Covered [] state)
    (inputs : Inputs state pending) (resident : ResidentRows state seen) :
    SourceRecursiveIntersectionSemanticHeap.SemanticHeap final ∧ InternedRecordCoherence.Covered [] final ∧
      Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧ Extends seen result ∧ ResidentRows final result := by
  induction trace with
  | nil state seen => exact ⟨semantic, covered, grows_refl _, extends_refl _, extends_refl _, resident⟩
  | empty rest ih => exact ih semantic covered (fun value member => inputs value (List.mem_cons_of_mem _ member)) resident
  | known value identity edges same present rest ih =>
      exact ih semantic covered (fun value member => inputs value (List.mem_cons_of_mem _ member)) resident
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun value member => inputs value (List.mem_cons_of_mem _ member)
      have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value state semantic covered own.1 own.2
      have afterSemantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
      have afterCovered : InternedRecordCoherence.Covered [] after := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.covered
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have edgeResident := checked.edges edges after done
      have edgeClosed := checked.closed edges after done
      have nextInputs : Inputs after (edges.flatMap EdgeValue.children ++ pending) := by
        intro child member
        rcases List.mem_append.mp member with first | later
        · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
          exact ⟨afterSemantic.1.normal.facts.cached.edges edge.entry.key edge (edgeResident edge edgeIn) child childIn,
            edgeClosed edge edgeIn child childIn⟩
        · exact ⟨(tail child later).1.grows state after growth history, (tail child later).2⟩
      have afterResident : ResidentRows after (Cache.put seen identity edges) := by
        intro key values present
        by_cases equal : key = identity
        · subst key
          have equal : edges = values := by simpa [Cache.put] using present
          subst values
          exact ⟨value, own.1.grows state after growth history, same, own.2, edgeResident, edgeClosed⟩
        · exact resident.grows state after seen growth history key values (by simpa [Cache.put, equal] using present)
      obtain ⟨finalSemantic, finalCovered, laterGrowth, laterHistory, rowsGrowth, finalRows⟩ :=
        ih afterSemantic afterCovered nextInputs afterResident
      exact ⟨finalSemantic, finalCovered, grows_trans growth laterGrowth, extends_trans history laterHistory,
        extends_trans (SourceColdSharedRows.put_extends seen identity edges absent) rowsGrowth, finalRows⟩

/-- A finite repaired trace supplies stable finite bounds for reads and the whole worklist. -/
theorem Trace.finite [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) :
    ∃ outer inner, ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
      collect largerOuter largerInner state seen pending = .done result final := by
  induction trace with
  | nil state seen =>
      refine ⟨1, 0, ?_⟩
      intro outer inner enough _
      cases outer with
      | zero => omega
      | succ => rfl
  | empty rest ih =>
      obtain ⟨outer, inner, done⟩ := ih
      refine ⟨outer + 1, inner, ?_⟩
      intro largerOuter largerInner enoughOuter enoughInner
      cases largerOuter with
      | zero => omega
      | succ largerOuter => exact done largerOuter largerInner (by omega) enoughInner
  | known value identity edges same present rest ih =>
      obtain ⟨outer, inner, done⟩ := ih
      refine ⟨outer + 1, inner, ?_⟩
      intro largerOuter largerInner enoughOuter enoughInner
      cases largerOuter with
      | zero => omega
      | succ largerOuter =>
          have next := done largerOuter largerInner (by omega) enoughInner
          cases value <;> simp only [reference] at same <;> try contradiction
          all_goals
            obtain rfl := Option.some.inj same
            simpa only [collect, present] using next
  | @read seen state after pending result final value identity fuel edges same absent returned rest ih =>
      obtain ⟨outer, inner, done⟩ := ih
      refine ⟨outer + 1, max fuel inner, ?_⟩
      intro largerOuter largerInner enoughOuter enoughInner
      cases largerOuter with
      | zero => omega
      | succ largerOuter =>
          have next := done largerOuter largerInner (by omega) (by omega)
          have enough : fuel ≤ largerInner := by omega
          have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel (largerInner - fuel) value state
            (by rw [returned]; trivial)
          have readDone : MergedFreshOrdinaryExposure.nodeEdges largerInner value state = .done edges after := by
            simpa only [Nat.add_sub_cancel' enough, returned] using stable
          cases value <;> simp only [reference] at same <;> try contradiction
          all_goals
            obtain rfl := Option.some.inj same
            simpa only [collect, absent, readDone, readThen] using next

/-- Every successful repaired executable worklist supplies its exact complete source trace. -/
theorem collect_trace [DecidableEq (EdgeKey Symbol Guard)] (outer inner : Nat)
    (state : State Symbol Guard) (seen result : Rows Symbol Guard) (pending : List (Value Symbol Guard))
    (final : State Symbol Guard) (done : collect outer inner state seen pending = .done result final) :
    Trace state seen pending result final := by
  induction outer generalizing state seen pending with
  | zero => cases done
  | succ outer ih =>
      cases pending with
      | nil =>
          obtain ⟨rfl, rfl⟩ := Result.done.inj done
          exact .nil _ _
      | cons value pending =>
          have advance (identity : Nat) (same : reference value = some identity)
              (expanded : collect (outer + 1) inner state seen (value :: pending) =
                match seen identity with
                | some _ => collect outer inner state seen pending
                | none => readThen (MergedFreshOrdinaryExposure.nodeEdges inner value state) fun edges after =>
                    collect outer inner after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ pending)) :
              Trace state seen (value :: pending) result final := by
            rw [expanded] at done
            cases present : seen identity with
            | some edges =>
                exact .known value identity edges same present (ih state seen pending (by simpa only [present] using done))
            | none =>
                cases read : MergedFreshOrdinaryExposure.nodeEdges inner value state with
                | unresolved | pending | exhausted =>
                    simp only [present, read, readThen] at done
                    cases done
                | done edges after =>
                    exact .read value identity inner edges same present read
                      (ih after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ pending)
                        (by simpa only [present, read, readThen] using done))
          cases value with
          | empty => exact .empty (ih state seen pending done)
          | reference => cases done
          | node entry edges depth free | union entry members depth free | mu entry body depth ordinary =>
              exact advance entry.identity rfl rfl


/-- Every prepared closed root derives finite actual repaired shared traversal without a supplied trace. -/
theorem cold_finite [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (value : Value Symbol Guard)
    (available : Available before value) (closed : value.free = []) :
    ∃ rows after outer inner, Trace before (fun _ => none) [value] rows after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner before (fun _ => none) [value] = .done rows after := by
  obtain ⟨rows, after, _, _, original, _⟩ := SourceColdSharedRows.cold_finite before facts prepared value available closed
  have trace := of_prepared original facts prepared (by intro child member; rw [List.mem_singleton.mp member]; exact ⟨available, closed⟩)
  obtain ⟨outer, inner, done⟩ := trace.finite
  exact ⟨rows, after, outer, inner, trace, done⟩

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
