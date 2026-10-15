import MicroCFTA.SourceMergedComparisonAncestors

/-!
# Independent finite-term certificates from actual repaired comparison stages

Successful child and cover scans use their actual intermediate caches.
Visited-pair witnesses grow with these caches. Returned row certificates
transfer independent guarded languages through one constructor step.
-/
namespace MicroCFTA.SourceMergedComparisonCertificates
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects SourceMergedComparisonAncestors
open MergedSourceComparison (Result children anyCover)
open MergedFreshOrdinaryComparison (allRows)
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- A recursive callback certificate applies only at its actual scoped available operands and ancestors. -/
def Certifies (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (rank : Nat) (above : List (Nat × Nat)) : Prop :=
  ∀ before, SemanticReady before → Ancestors before holds ambient rank above → ∀ wide narrow,
    Available before wide → Available before narrow → wide.free = [] → narrow.free = [] → ∀ after,
      compare wide narrow before = .done true after → Bounded holds ambient rank wide narrow

/-- An arity-matched successful zip gives complete independent child inclusion certificates. -/
theorem children_certificate
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (rank : Nat) (above : List (Nat × Nat))
    (certifies : Certifies compare holds ambient rank above) (wides narrows : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (ancestors : Ancestors before holds ambient rank above)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows) (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (lengths : wides.length = narrows.length) (after : State Symbol Guard)
    (done : children compare wides narrows before = .done true after) : All₂ (Bounded holds ambient rank) wides narrows := by
  induction wides generalizing narrows before with
  | nil => cases narrows with
      | nil => exact .nil
      | cons => simp at lengths
  | cons wide wides ih =>
      cases narrows with
      | nil => simp at lengths
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ true after).mp done
          cases accepted with
          | false => cases later
          | true =>
              have effects := callback wide narrow before semantic (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
                (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) true middle first
              exact .cons (certifies before semantic ancestors wide narrow (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
                (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) middle first)
                (ih narrows middle effects.2 (ancestors.grows effects.1)
                  (fun value member => effects.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
                  (fun value member => effects.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
                  (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                  (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))
                  (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using lengths) later)

/-- A true ordered cover search selects a full matching wide row and all child certificates. -/
theorem anyCover_certificate [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (rank : Nat) (above : List (Nat × Nat))
    (certifies : Certifies compare holds ambient rank above) (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (ancestors : Ancestors before holds ambient rank above)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done true after) :
    ∃ wide ∈ wides, wide.entry.key.symbol = narrow.entry.key.symbol ∧ clear wide.entry.key.constraint = true ∧
      All₂ (Bounded holds ambient rank) wide.children narrow.children := by
  induction wides generalizing before with
  | nil => cases done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · rename_i matched
        obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ true after).mp done
        have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)
        cases accepted with
        | true =>
            exact ⟨wide, List.mem_cons_self, matched.1, matched.2.2,
              children_certificate compare callback holds ambient rank above certifies wide.children narrow.children before semantic ancestors
                childInputs narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed matched.2.1 middle first⟩
        | false =>
            have effects := children_effect compare callback wide.children narrow.children before semantic childInputs narrowInputs
              (wideClosed _ List.mem_cons_self) narrowClosed false middle first
            obtain ⟨chosen, member, facts⟩ := ih middle effects.2 (ancestors.grows effects.1)
              (fun value member => effects.1.available value (narrowInputs value member))
              (fun edge member => InternedEdgeResidency.edge_grows before middle effects.1.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
              (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later
            exact ⟨chosen, List.mem_cons_of_mem _ member, facts⟩
      · obtain ⟨chosen, member, facts⟩ := ih before semantic ancestors narrowInputs
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done
        exact ⟨chosen, List.mem_cons_of_mem _ member, facts⟩

/-- Every actual narrow row transfers bounded independent terms through its actual wide read and cover search. -/
theorem allRows_certificate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (rank : Nat) (above : List (Nat × Nat))
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (certifies : Certifies compare holds ambient rank above) (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (ancestors : Ancestors before holds ambient rank above)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows) (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done true after) :
    ∀ narrow ∈ narrows, ∀ term, term.height ≤ rank + 1 → EdgeMeaning (meaning holds ambient) holds narrow term → meaning holds ambient wide term := by
  induction narrows generalizing before with
  | nil => simp
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ true after).mp done
      have readTrace := read_graph fuel wide before wides readAfter read
      have readFacts := readTrace.verified semantic wideInput wideClosed
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ true after).mp later
      cases accepted with
      | false => cases rest
      | true =>
          have narrowChildren := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
          have selected := anyCover_certificate clear compare callback holds ambient rank above certifies narrow wides readAfter readFacts.2.1
            (ancestors.grows readFacts.1) (fun value member => readFacts.1.available value (narrowChildren value member)) readFacts.2.2.1
            (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 middle covered
          have coverEffects := anyCover_effect clear compare callback narrow wides readAfter readFacts.2.1
            (fun value member => readFacts.1.available value (narrowChildren value member)) readFacts.2.2.1
            (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 true middle covered
          have growth := readFacts.1.trans coverEffects.1
          intro edge member term height accepted
          rcases List.mem_cons.mp member with rfl | tail
          · obtain ⟨chosen, included, symbol, guard, related⟩ := selected
            obtain ⟨terms, shape, children, _⟩ := accepted
            have childBound : forestHeight terms ≤ rank := by
              rw [shape] at height
              simpa only [Term.height, forestHeight, Nat.add_le_add_iff_right] using height
            have boundedChildren := (all₂_height_iff (meaning holds ambient) edge.children terms rank).mpr ⟨children, childBound⟩
            have coveredChildren := MergedAlternativesSubsumption.all₂_transfer
              (fun left right child comparison run => comparison child run.2 run.1) related boundedChildren
            exact (readTrace.exact semantic wideInput wideClosed holds ambient term).mp
              ⟨chosen, included, terms, shape.trans (by rw [symbol]), coveredChildren, clearTrue _ guard term⟩
          · exact ih middle coverEffects.2 (ancestors.grows growth) (growth.available wide wideInput)
              (fun edge member => InternedEdgeResidency.edge_grows before middle growth.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
              (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest edge tail term height accepted

end MicroCFTA.SourceMergedComparisonCertificates
