import MicroCFTA.SourcePruningEnumerationEdgePrefix
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.MergedColdReaderClosed
import MicroCFTA.InternedLiveEdges

namespace MicroCFTA.SourcePruningEnumerationEdgeTraversal
open Fragments EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

local instance traversalMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run captured child actions in order and retain the actual state at the first unsupported child. -/
def runStaged : List (InternedConstructorTemplates.Value Symbol Constraint ×
    List EnumerationState.Suspended ×
    Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) →
    EnumerateM Symbol Constraint (Option (List (Fragments.Fragment Symbol)))
 :=
  fun stages => match stages with
  | [] => pure (some [])
  | (_, _, none) :: _ => pure none
  | (_, _, some childAction) :: rest =>
      childAction >>= fun fragment =>
        runStaged rest >>= fun result => pure (result.map (fun tail => fragment :: tail))

/-- Derive the actual completed-prefix endpoint, including the first unsupported child. -/
theorem runStaged_complete
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (coherent : InternedRecordCoherence.Coherent heap) :
    ∀ (before : EnumerationState.State Symbol Constraint),
      PendingRealized heap before → before.counter = before.values.length →
      (∀ input ∈ inputs, InternedProbeProvenance.Available heap input.1) →
      (∀ input ∈ inputs, input.1.free = []) → (∀ input ∈ inputs, input.1 ≠ .empty) →
      let staged := inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1))
      let stop := staged.findIdx (fun stage => stage.2.2.isNone)
      ∃ (result : Option (List (Fragments.Fragment Symbol))) (after : EnumerationState.State Symbol Constraint),
        Success (runStaged staged) before result after ∧
        Success (runStaged (staged.take stop)) before
          (some ((List.range' before.counter stop).map (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) after ∧
        result = (if stop < staged.length then none else
          some ((List.range' before.counter staged.length).map (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) ∧
        after.counter = before.counter + stop ∧ after.counter = after.values.length ∧
        PendingRealized heap after
 := by
  induction inputs with
  | nil =>
    intro before realized aligned available closed nonempty
    refine ⟨some [], before, ?_, ?_, ?_, ?_, aligned, realized⟩ <;>
      simp [runStaged, success_pure]
  | cons input rest ih =>
    intro before realized aligned available closed nonempty
    obtain ⟨value, bucket⟩ := input
    by_cases nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
    · obtain ⟨node, _encoded, _decoded, _emptyCase, nonemptyCase⟩ :=
        SourcePruningEnumerationShallowChild.prepareChild_complete heap before bucket value coherent
          (available _ (List.mem_cons_self ..)) (closed _ (List.mem_cons_self ..)) realized aligned nonterminal
      obtain ⟨childAction, middle, prepared, headSuccess, _middleShape, _middleSlot,
        middleCounter, middleAligned, middleRealized⟩ := nonemptyCase (nonempty _ (List.mem_cons_self ..))
      obtain ⟨tailResult, after, tailSuccess, completedPrefixSuccess, resultShape,
        afterCounter, afterAligned, afterRealized⟩ :=
        ih middle middleRealized middleAligned
          (fun input member => available input (List.mem_cons_of_mem _ member))
          (fun input member => closed input (List.mem_cons_of_mem _ member))
          (fun input member => nonempty input (List.mem_cons_of_mem _ member))
      dsimp only
      simp only [List.map_cons, prepared, List.findIdx_cons, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, List.length_cons, List.take_succ_cons]
      refine ⟨tailResult.map (fun tailFragments => .hole before.counter :: tailFragments), after,
        ?_, ?_, ?_, ?_, afterAligned, afterRealized⟩
      · apply (success_bind _ _ _ _ _).mpr
        refine ⟨.hole before.counter, middle, headSuccess, ?_⟩
        exact (success_bind _ _ _ _ _).mpr
          ⟨tailResult, after, tailSuccess, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
      · simp only [List.range'_succ, List.map_cons]
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨.hole before.counter, middle, headSuccess, ?_⟩
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨_, after, completedPrefixSuccess, ?_⟩
        simp only [success_pure, Option.map_some, middleCounter, and_self]
      · rw [resultShape]
        split <;> simp_all [List.range'_succ, Nat.succ_lt_succ_iff]
      · omega
    ·
      have absent : SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) bucket value = none := by
        cases value with
        | empty => exact False.elim (nonempty _ (List.mem_cons_self ..) rfl)
        | reference name => cases closed _ (List.mem_cons_self ..)
        | node | union | mu =>
          simp only [SourcePruningEnumerationShallowChild.prepareChild,
            Bool.of_not_eq_false nonterminal, ↓reduceIte]
      dsimp only
      simp only [List.map_cons, absent, List.findIdx_cons, Option.isNone_none, ↓reduceIte]
      refine ⟨none, before, ?_, ?_, ?_, ?_, aligned, realized⟩ <;>
        simp [runStaged, success_pure]

/-- Run one captured edge prefix and record its residual only after every child completes. -/
noncomputable def prepare (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) :
    Option (EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
 :=
  match SourcePruningEnumerationEdgePrefix.prepare scs edge with
  | none => none
  | some prefixAction => some (prefixAction >>= fun packet =>
      runStaged packet.2.1 >>= fun childrenResult =>
        match childrenResult with
        | none => pure none
        | some fragments =>
            let fragment := Fragments.Fragment.node packet.1 fragments
            EnumerationSchedule.recordResidual packet.2.2 fragment >>= fun _ => pure (some fragment))

/-- Derive the actual edge traversal and its exact residual update from the same ordinary parent. -/
theorem prepare_complete (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : InternedProbeProvenance.Available heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (before : EnumerationState.State Symbol Constraint) (realized : PendingRealized heap before)
    (aligned : before.counter = before.values.length)
    (allowed : arityAllows edge.children.length scs = true) :
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => prepare scs edge = none
    | some (tries, residual) =>
        let own : List EnumerationState.Suspended := suspendedVars before.counter tries
        let staged := edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
        let stop := staged.findIdx (fun stage => stage.2.2.isNone)
        ∃ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
          (childrenResult : Option (List (Fragments.Fragment Symbol)))
          (childrenAfter after : EnumerationState.State Symbol Constraint),
          prepare scs edge = some action ∧
          Success (runStaged staged) (suspendedState tries.length before) childrenResult childrenAfter ∧
          Success (runStaged (staged.take stop)) (suspendedState tries.length before)
            (some ((List.range' (before.counter + tries.length) stop).map
              (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) childrenAfter ∧
          childrenResult = (if stop < staged.length then none else
            some ((List.range' (before.counter + tries.length) staged.length).map
              (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) ∧
          after = (match childrenResult with
            | none => childrenAfter
            | some fragments => match residual with
              | none => childrenAfter
              | some guard => {childrenAfter with obligations :=
                  (guard, Fragments.Fragment.node edge.entry.key.symbol fragments) :: childrenAfter.obligations}) ∧
          Success action before (childrenResult.map (fun fragments =>
            Fragments.Fragment.node edge.entry.key.symbol fragments)) after ∧
          after.counter = before.counter + tries.length + stop ∧
          after.counter = after.values.length ∧ PendingRealized heap after
 := by
  cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
  | none => simp [prepare, SourcePruningEnumerationEdgePrefix.prepare, allowed, projected]
  | some pair =>
    obtain ⟨tries, residual⟩ := pair
    dsimp only
    obtain ⟨prefixAction, prefixPrepared, prefixExact, prefixCounter, prefixAligned, prefixRealized⟩ :=
      by simpa only [allowed, ↓reduceIte, projected] using
        SourcePruningEnumerationEdgePrefix.prepare_complete scs edge heap before realized aligned
    have prefixSuccess : Success prefixAction before
        (edge.entry.key.symbol,
          edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries),
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)) indexed.1)), residual)
        (suspendedState tries.length before) := by
      simp only [Success, ExceptT.run, prefixExact, List.mem_singleton]
    have childrenAvailable : ∀ child ∈ edge.children, InternedProbeProvenance.Available heap child := by
      intro child member
      exact parentAvailable.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)
    have childrenClosed : ∀ child ∈ edge.children, child.free = [] := by
      exact MergedColdReaderClosed.node_children_closed heap ready.semantic.1.normal.facts
        parentEntry edges depth free parentAvailable parentClosed edge selected
    have childrenNonempty : ∀ child ∈ edge.children, child ≠ .empty := by
      intro child member emptyChild
      subst child
      exact (List.any_eq_false.mp
        (InternedLiveEdges.resident_live heap ready.semantic.1.normal.live
          (.node parentEntry edges depth free) parentAvailable.resident edge selected))
        .empty member (by rfl)
    let inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended) :=
      edge.children.zipIdx.map (fun indexed =>
        (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)))
    have stagedSame : inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1)) =
      edge.children.zipIdx.map (fun indexed =>
        (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries),
          SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
            (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)) indexed.1)) := by
      simp only [inputs, List.map_map]
      rfl
    obtain ⟨childrenResult, childrenAfter, childrenSuccess, completedPrefixSuccess, resultShape,
      afterCounter, afterAligned, afterRealized⟩ :=
      runStaged_complete inputs heap ready.semantic.1.normal.facts.coherent
        (suspendedState tries.length before) prefixRealized prefixAligned
        (by
          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenAvailable indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
        (by
          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenClosed indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
        (by
          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenNonempty indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
    rw [stagedSame] at childrenSuccess completedPrefixSuccess resultShape afterCounter
    rw [prefixCounter] at completedPrefixSuccess resultShape afterCounter
    refine ⟨prefixAction >>= fun packet =>
      runStaged packet.2.1 >>= fun childrenResult =>
        match childrenResult with
        | none => pure none
        | some fragments => EnumerationSchedule.recordResidual packet.2.2 (.node packet.1 fragments)
            >>= fun _ => pure (some (.node packet.1 fragments)),
      childrenResult, childrenAfter, _, ?_, childrenSuccess, completedPrefixSuccess,
      resultShape, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [prepare, prefixPrepared]
      rfl
    · apply (success_bind _ _ _ _ _).mpr
      refine ⟨_, suspendedState tries.length before, prefixSuccess, ?_⟩
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨childrenResult, childrenAfter, childrenSuccess, ?_⟩
      cases childrenResult with
      | none => exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
      | some fragments =>
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨(), _, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        cases residual with
        | none => exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
        | some guard => exact (EnumerationDriver.modify_success _ _ _).mpr rfl
    · cases childrenResult with
      | none => exact afterCounter
      | some fragments => cases residual <;> exact afterCounter
    · cases childrenResult with
      | none => exact afterAligned
      | some fragments => cases residual <;> exact afterAligned
    · cases childrenResult with
      | none => exact afterRealized
      | some fragments => cases residual <;> exact afterRealized

end MicroCFTA.SourcePruningEnumerationEdgeTraversal
