import MicroCFTA.SourceColdSharedRows

/-!
# Exact finite execution and discovery of cold shared rows

Finite source traces and successful executable worklist runs correspond in
both directions. One finite pair of fuel bounds suffices for each trace.
Every larger pair retains the identical rows and final cache. The trace also
derives the finite inventory of newly discovered identities.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates
open SourcePreparedSharedRows (reference)

/-- Additional read fuel retains the exact completed row list and cache. -/
theorem read_larger [DecidableEq (EdgeKey Symbol Guard)] (fuel larger : Nat) (enough : fuel ≤ larger)
    (value : Value Symbol Guard) (state : State Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after) :
    MergedSourceExposure.nodeEdges larger value state = .done edges after := by
  have stable := MergedColdReaderTermination.nodeEdges_stable fuel (larger - fuel) value state (by rw [done]; trivial)
  simpa only [Nat.add_sub_cancel' enough, done] using stable

/-- Each finite actual trace has stable finite executable bounds for the whole stateful walk. -/
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
  | @read seen state after pending result final value identity fuel edges same absent read rest ih =>
      obtain ⟨outer, inner, done⟩ := ih
      refine ⟨outer + 1, max fuel inner, ?_⟩
      intro largerOuter largerInner enoughOuter enoughInner
      cases largerOuter with
      | zero => omega
      | succ largerOuter =>
          have next := done largerOuter largerInner (by omega) (by omega)
          have readDone := read_larger fuel largerInner (by omega) value state edges after read
          cases value <;> simp only [reference] at same <;> try contradiction
          all_goals
            obtain rfl := Option.some.inj same
            simpa only [collect, absent, readDone, readThen] using next

/-- Every successful executable cold walk supplies its complete actual source trace. -/
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
                | none => readThen (MergedSourceExposure.nodeEdges inner value state) fun edges after =>
                    collect outer inner after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ pending)) :
              Trace state seen (value :: pending) result final := by
            rw [expanded] at done
            cases present : seen identity with
            | some edges =>
                exact .known value identity edges same present (ih state seen pending (by simpa only [present] using done))
            | none =>
                cases read : MergedSourceExposure.nodeEdges inner value state with
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

/-- A finite cold trace retains every first-written row independently of cache invariants. -/
theorem Trace.extends [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) : Extends seen result := by
  induction trace with
  | nil => exact extends_refl _
  | empty rest ih | known value identity edges same present rest ih => exact ih
  | read value identity fuel edges same absent done rest ih => exact extends_trans (put_extends _ _ _ absent) ih

/-- Every initial nonempty pending identity is present after a completed actual walk. -/
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

/-- Each source child of the first map is declared in the second map. -/
def CoveredRows (first second : Rows Symbol Guard) : Prop :=
  ∀ identity edges, first identity = some edges → ∀ edge ∈ edges, ∀ child ∈ edge.children,
    ∀ next, reference child = some next → ∃ outgoing, second next = some outgoing

/-- Completion declares every nonempty child of every newly read row. -/
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

/-- The newly discovered identity inventory is finite, distinct, and exact. -/
theorem Trace.discovery [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) :
    ∃ keys : List Nat, keys.Nodup ∧ (∀ identity ∈ keys, seen identity = none) ∧
      ∀ identity, (∃ edges, result identity = some edges) ↔ (∃ edges, seen identity = some edges) ∨ identity ∈ keys := by
  induction trace with
  | nil state seen => exact ⟨[], by simp, by simp, by simp⟩
  | empty rest ih | known value identity edges same present rest ih => exact ih
  | @read seen state after pending result final value identity fuel edges same absent read rest ih =>
      obtain ⟨keys, distinct, fresh, domain⟩ := ih
      have absentKeys : identity ∉ keys := by
        intro member
        have impossible := fresh identity member
        simp [Cache.put] at impossible
      refine ⟨identity :: keys, List.nodup_cons.mpr ⟨absentKeys, distinct⟩, ?_, ?_⟩
      · intro key member
        rcases List.mem_cons.mp member with rfl | member
        · exact absent
        · have old := fresh key member
          by_cases equal : key = identity
          · subst key; exact absent
          · simpa [Cache.put, equal] using old
      · intro key
        rw [domain]
        by_cases equal : key = identity
        · subst key; simp [Cache.put, absent]
        · simp [Cache.put, equal]

end MicroCFTA.SourceColdSharedRows
