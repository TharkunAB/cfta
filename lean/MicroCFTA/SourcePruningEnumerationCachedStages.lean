import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.SourcePruningEnumerationEdgeTraversal

namespace MicroCFTA.SourcePruningEnumerationCachedStages
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Run the actual prepared children and retain the completed-prefix cache. -/
def run
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat) :
    List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended) →
      EnumerationExpandableIndex.Cached Symbol Constraint →
      Option (List (Option (List (Fragments.Fragment Symbol)) ×
        EnumerationExpandableIndex.Cached Symbol Constraint) ×
        EnumerationExpandableIndex.Cached Symbol Constraint)
  | [], before => some ([(some [], before)], before)
  | (value, bucket) :: rest, before =>
      match SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket value with
      | none => some ([(none, before)], before)
      | some _action =>
          (SourcePruningEnumerationCachedPrepare.prepareChild heap fuel bucket value before).bind fun rows =>
            match rows with
            | [] => some ([], before)
            | [(fragment, middle)] =>
                (run heap fuel rest middle).map fun result =>
                  (result.1.map (fun row =>
                    (row.1.map (fun fragments => fragment :: fragments), row.2)), result.2)
            | _ => none

/-- Derive stable cached execution and the exact existing raw child stream. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (roots : Nat → Nat) (coherent : InternedRecordCoherence.Coherent heap) :
    ∀ (before : EnumerationExpandableIndex.Cached Symbol Constraint),
      StorageValid before.core → PendingRealized heap before.core →
      Roots before.core.representatives roots →
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting →
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) →
      (∀ input ∈ inputs, InternedProbeProvenance.Available heap input.1) →
      (∀ input ∈ inputs, input.1.free = []) →
      (∀ input ∈ inputs, ∀ sc ∈ input.2, sc.var < before.core.counter) →
      let staged := inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1))
      ∃ (fuel : Nat)
        (rows : List (Option (List (Fragments.Fragment Symbol)) ×
          EnumerationExpandableIndex.Cached Symbol Constraint))
        (after : EnumerationExpandableIndex.Cached Symbol Constraint),
        (∀ (extra : Nat), run heap (fuel + extra) inputs before = some (rows, after)) ∧
        ExceptT.run (SourcePruningEnumerationEdgeTraversal.runStaged staged before.core) =
          rows.map (fun row => .ok (row.1, row.2.core)) ∧
        before.core.counter ≤ after.core.counter ∧
        after.core.counter = after.core.values.length ∧
        after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
        StorageValid after.core ∧ PendingRealized heap after.core ∧
        EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
        (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
        (rows = [] ∨ ∃ result : Option (List (Fragments.Fragment Symbol)),
          rows = [(result, after)] ∧
          (∀ (fragments : List (Fragments.Fragment Symbol)), result = some fragments →
            FragmentsBound («Symbol» := Symbol) after.core.counter fragments)) := by
  induction inputs with
  | nil =>
    intro before storage realized paths counts flags available closed bounded
    dsimp only
    refine ⟨0, [(some [], before)], before, ?_, rfl, Nat.le_refl _, storage.aligned,
      rfl, paths, storage, realized, counts, flags, Or.inr ⟨some [], rfl, ?_⟩⟩
    · intro extra
      rfl
    · intro fragments same
      cases same
      trivial
  | cons input rest ih =>
    intro before storage realized paths counts flags available closed bounded
    obtain ⟨value, bucket⟩ := input
    dsimp only
    cases prepared : SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) bucket value with
    | none =>
      refine ⟨0, [(none, before)], before, ?_, ?_, Nat.le_refl _, storage.aligned,
        rfl, paths, storage, realized, counts, flags, Or.inr ⟨none, rfl, ?_⟩⟩
      · intro extra
        simp only [run, prepared]
      · simp only [List.map_cons, prepared]
        rfl
      · intro fragments impossible
        cases impossible
    | some action =>
      have nonterminal : value ≠ .empty →
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
        intro nonempty
        apply Classical.byContradiction
        intro terminal
        cases value with
        | empty => exact nonempty rfl
        | reference _name => cases prepared
        | node _entry _edges _depth _free =>
          simp only [SourcePruningEnumerationShallowChild.prepareChild,
            Bool.of_not_eq_false terminal, ↓reduceIte] at prepared
          cases prepared
        | union _entry _members _depth _free =>
          simp only [SourcePruningEnumerationShallowChild.prepareChild,
            Bool.of_not_eq_false terminal, ↓reduceIte] at prepared
          cases prepared
        | mu _entry _body _depthShape _ordinaryShape =>
          simp only [SourcePruningEnumerationShallowChild.prepareChild,
            Bool.of_not_eq_false terminal, ↓reduceIte] at prepared
          cases prepared
      obtain ⟨headAction, headFuel, childRows, headPrepared, headRun, headRaw, headShape⟩ :=
        SourcePruningEnumerationCachedPrepare.complete heap before value bucket roots coherent
          (available _ (List.mem_cons_self ..)) (closed _ (List.mem_cons_self ..))
          storage realized paths counts flags (bounded _ (List.mem_cons_self ..)) nonterminal
      have sameAction : headAction = action := by
        exact Option.some.inj (headPrepared.symm.trans prepared)
      rw [sameAction] at headRaw
      rcases headShape with ⟨_emptyValue, childEmpty⟩ |
        ⟨middle, _nonempty, childSingleton, middleCounter, _middleAligned, middleForest,
          middlePaths, middleStorage, middleRealized, middleCounts, middleFlags, headBound⟩
      · refine ⟨headFuel, [], before, ?_, ?_, Nat.le_refl _, storage.aligned,
          rfl, paths, storage, realized, counts, flags, Or.inl rfl⟩
        · intro extra
          simp only [run, prepared, headRun extra, childEmpty, Option.bind_some]
        · rw [childEmpty, List.map_nil] at headRaw
          simp only [List.map_cons, prepared]
          rw [SourcePruningEnumerationEdgeTraversal.runStaged, run_bind, headRaw]
          rfl
      ·
        have tailBounded : ∀ input ∈ rest, ∀ sc ∈ input.2,
            sc.var < middle.core.counter := by
          intro input member sc inside
          exact Nat.lt_of_lt_of_le
            (bounded input (List.mem_cons_of_mem _ member) sc inside) (by omega)
        obtain ⟨tailFuel, rows, after, tailRun, tailRaw, grows, alignedAfter, forestSame,
          pathsAfter, storageAfter, realizedAfter, countsAfter, flagsAfter, tailShape⟩ :=
          ih middle middleStorage middleRealized middlePaths middleCounts middleFlags
            (fun input member => available input (List.mem_cons_of_mem _ member))
            (fun input member => closed input (List.mem_cons_of_mem _ member)) tailBounded
        let lifted : List (Option (List (Fragments.Fragment Symbol)) ×
            EnumerationExpandableIndex.Cached Symbol Constraint) :=
          rows.map (fun row =>
            (row.1.map (fun fragments => Fragments.Fragment.hole before.core.counter :: fragments), row.2))
        refine ⟨headFuel + tailFuel, lifted, after, ?_, ?_, (by omega), alignedAfter,
          forestSame.trans middleForest, pathsAfter, storageAfter, realizedAfter,
          countsAfter, flagsAfter, ?_⟩
        · intro extra
          rw [show headFuel + tailFuel + extra = headFuel + (tailFuel + extra) by omega]
          rw [run, prepared, headRun (tailFuel + extra)]
          simp only [childSingleton, Option.bind_some]
          rw [show headFuel + (tailFuel + extra) = tailFuel + (headFuel + extra) by omega,
            tailRun (headFuel + extra)]
          rfl
        · simp only [List.map_cons, prepared]
          rw [SourcePruningEnumerationEdgeTraversal.runStaged]
          rw [bind_single _ _ before.core middle.core (.hole before.core.counter)
            (by simpa only [ExceptT.run, childSingleton, List.map_cons, List.map_nil] using headRaw)]
          rw [run_bind, tailRaw]
          dsimp only [lifted]
          rcases tailShape with tailEmpty | ⟨result, tailSingleton, _tailBound⟩
          · rw [tailEmpty]
            rfl
          · rw [tailSingleton]
            rfl
        · rcases tailShape with tailEmpty | ⟨result, tailSingleton, tailBound⟩
          · exact Or.inl (by simp only [lifted, tailEmpty, List.map_nil])
          · refine Or.inr ⟨result.map (fun fragments =>
              Fragments.Fragment.hole before.core.counter :: fragments), ?_, ?_⟩
            · simp only [lifted, tailSingleton, List.map_cons, List.map_nil]
            · intro fragments same
              cases result with
              | none => cases same
              | some tailFragments =>
                simp only [Option.map_some, Option.some.injEq] at same
                subst fragments
                exact ⟨Nat.lt_of_lt_of_le headBound grows, tailBound tailFragments rfl⟩

end MicroCFTA.SourcePruningEnumerationCachedStages
