import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationCachedStages

namespace MicroCFTA.SourcePruningEnumerationCachedEdge
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Run the selected edge and record its residual after the children finish. -/
noncomputable def prepare
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Option (List (Option (Fragments.Fragment Symbol) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) :=
  (SourcePruningEnumerationCachedOwn.prepare heap scs edge before).bind fun prefixes =>
    match prefixes with
    | [] => some ([], before)
    | [((symbol, staged, residual), middle)] =>
        (SourcePruningEnumerationCachedStages.run heap fuel
          (staged.map (fun stage => (stage.1, stage.2.1))) middle).bind fun result =>
          match result.1 with
          | [] => some ([], result.2)
          | [(none, last)] => some ([(none, last)], last)
          | [(some fragments, last)] =>
              let fragment : Fragments.Fragment Symbol :=
                .node symbol fragments
              let finished : EnumerationExpandableIndex.Cached Symbol Constraint :=
                EnumerationExpandableIndex.Cached.frame
                  {last.core with obligations :=
                    match residual with
                    | none => last.core.obligations
                    | some guard => (guard, fragment) :: last.core.obligations} last
              some ([(some fragment, finished)], finished)
          | _ => none
    | _ => none

/-- Derive the selected edge outcome, its exact raw rows and its cache invariants. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : InternedProbeProvenance.Available heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) :
    ∃ (fuel : Nat)
      (outcome : Option (List (Option (Fragments.Fragment Symbol) ×
        EnumerationExpandableIndex.Cached Symbol Constraint) ×
        EnumerationExpandableIndex.Cached Symbol Constraint)),
      (∀ (extra : Nat), prepare heap (fuel + extra) scs edge before = outcome) ∧
      (SourcePruningEnumerationEdgeTraversal.prepare scs edge = none ↔ outcome = none) ∧
      (∀ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol))),
        SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action →
        ∃ (rows : List (Option (Fragments.Fragment Symbol) ×
            EnumerationExpandableIndex.Cached Symbol Constraint))
          (after : EnumerationExpandableIndex.Cached Symbol Constraint),
          outcome = some (rows, after) ∧
          ExceptT.run (action before.core) = rows.map (fun row => .ok (row.1, row.2.core)) ∧
          before.core.counter ≤ after.core.counter ∧
          after.core.counter = after.core.values.length ∧
          after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
          StorageValid after.core ∧ PendingRealized heap after.core ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          (rows = [] ∨ ∃ result : Option (Fragments.Fragment Symbol),
            rows = [(result, after)] ∧
            (∀ (fragment : Fragments.Fragment Symbol), result = some fragment →
              FragmentBound («Symbol» := Symbol) after.core.counter fragment))) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      refine ⟨0, none, ?_, ?_, ?_⟩
      · intro extra
        simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.bind_none]
      · simp only [SourcePruningEnumerationEdgeTraversal.prepare,
          SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, projected]
      · intro action prepared
        simp only [SourcePruningEnumerationEdgeTraversal.prepare,
          SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, projected] at prepared
        cases prepared
    | some pair =>
      obtain ⟨tries, residual⟩ := pair
      obtain ⟨prefixAction, ownAfter, prefixPrepared, ownRun, prefixRaw, _ownCore,
        ownCounter, _ownAligned, ownForest, ownPaths, ownStorage, ownRealized,
        ownCounts, _ownWaiting, _ownFlagsSame, ownFlags⟩ :=
          SourcePruningEnumerationCachedOwn.complete heap before scs edge roots
            storage realized paths counts flags
          |> (by simpa only [allowed, ↓reduceIte, projected] using ·)
      have childrenAvailable : ∀ child ∈ edge.children,
        InternedProbeProvenance.Available heap child := by
        intro child member
        exact parentAvailable.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)
      have childrenClosed : ∀ child ∈ edge.children, child.free = [] := by
        exact MergedColdReaderClosed.node_children_closed heap ready.semantic.1.normal.facts
          parentEntry edges depth free parentAvailable parentClosed edge selected
      let inputs : List (InternedConstructorTemplates.Value Symbol Constraint ×
          List EnumerationState.Suspended) :=
        edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++
            descendScs indexed.2 (suspendedVars before.core.counter tries)))
      have inputsAvailable : ∀ input ∈ inputs,
        InternedProbeProvenance.Available heap input.1 := by
        intro input member
        obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
        subst input
        exact childrenAvailable indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember)
      have inputsClosed : ∀ input ∈ inputs, input.1.free = [] := by
        intro input member
        obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
        subst input
        exact childrenClosed indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember)
      have inputsBounded : ∀ input ∈ inputs, ∀ sc ∈ input.2,
        sc.var < ownAfter.core.counter := by
        intro input member sc inside
        obtain ⟨indexed, _indexedMember, inputSame⟩ := List.mem_map.mp member
        subst input
        rcases List.mem_append.mp inside with inherited | own
        · exact Nat.lt_of_lt_of_le (descend_bounded before.core.counter indexed.2 scs bounded sc inherited)
            (by omega)
        · simpa only [ownCounter] using
            descend_bounded (before.core.counter + tries.length) indexed.2
              (suspendedVars before.core.counter tries) (suspended_bounded before.core.counter tries) sc own
      have stagedSame : inputs.map (fun input =>
          (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) input.2 input.1)) =
        edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++
            descendScs indexed.2 (suspendedVars before.core.counter tries),
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++
                descendScs indexed.2 (suspendedVars before.core.counter tries)) indexed.1)) := by
        simp only [inputs, List.map_map]
        rfl
      obtain ⟨childFuel, childrenRows, childrenAfter, childrenRun, childrenRaw, childGrows,
        childrenAligned, childrenForest, childrenPaths, childrenStorage, childrenRealized,
        childrenCounts, childrenFlags, childrenShape⟩ :=
          SourcePruningEnumerationCachedStages.complete heap inputs roots
            ready.semantic.1.normal.facts.coherent ownAfter ownStorage ownRealized ownPaths
            ownCounts ownFlags inputsAvailable inputsClosed inputsBounded
      rcases childrenShape with emptyRows | ⟨result, singletonRows, fragmentBounds⟩
      · refine ⟨childFuel, some ([], childrenAfter), ?_, ?_, ?_⟩
        · intro extra
          rw [prepare, ownRun]
          simp only [Option.bind_some]
          change (SourcePruningEnumerationCachedStages.run heap (childFuel + extra) inputs ownAfter).bind _ = _
          rw [childrenRun extra]
          simp only [Option.bind_some, emptyRows]
        · simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
            reduceCtorEq, iff_self]
        · intro action prepared
          simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
            Option.some.injEq] at prepared
          subst action
          refine ⟨[], childrenAfter, rfl, ?_, (by omega), childrenAligned,
            childrenForest.trans ownForest, childrenPaths, childrenStorage, childrenRealized,
            childrenCounts, childrenFlags, Or.inl rfl⟩
          rw [bind_single _ _ before.core ownAfter.core _ (by simpa only [ExceptT.run] using prefixRaw)]
          rw [← stagedSame, run_bind, childrenRaw, emptyRows]
          rfl
      · cases result with
        | none =>
          refine ⟨childFuel, some ([(none, childrenAfter)], childrenAfter), ?_, ?_, ?_⟩
          · intro extra
            rw [prepare, ownRun]
            simp only [Option.bind_some]
            change (SourcePruningEnumerationCachedStages.run heap (childFuel + extra) inputs ownAfter).bind _ = _
            rw [childrenRun extra]
            simp only [Option.bind_some, singletonRows]
          · simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
              reduceCtorEq, iff_self]
          · intro action prepared
            simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
              Option.some.injEq] at prepared
            subst action
            refine ⟨[(none, childrenAfter)], childrenAfter, rfl, ?_, (by omega), childrenAligned,
              childrenForest.trans ownForest, childrenPaths, childrenStorage, childrenRealized,
              childrenCounts, childrenFlags, Or.inr ⟨none, rfl, ?_⟩⟩
            · rw [bind_single _ _ before.core ownAfter.core _ (by simpa only [ExceptT.run] using prefixRaw)]
              rw [← stagedSame]
              rw [bind_single _ _ ownAfter.core childrenAfter.core none
                (by simpa only [ExceptT.run, singletonRows, List.map_cons, List.map_nil] using childrenRaw)]
              rfl
            · intro returned impossible
              cases impossible
        | some fragments =>
          let fragment : Fragments.Fragment Symbol :=
            .node edge.entry.key.symbol fragments
          let finished : EnumerationExpandableIndex.Cached Symbol Constraint :=
            EnumerationExpandableIndex.Cached.frame
              {childrenAfter.core with obligations :=
                match residual with
                | none => childrenAfter.core.obligations
                | some guard => (guard, fragment) :: childrenAfter.core.obligations} childrenAfter
          have nodeBound : FragmentBound («Symbol» := Symbol) childrenAfter.core.counter fragment := by
            exact fragmentBounds fragments rfl
          refine ⟨childFuel, some ([(some fragment, finished)], finished), ?_, ?_, ?_⟩
          · intro extra
            rw [prepare, ownRun]
            simp only [Option.bind_some]
            change (SourcePruningEnumerationCachedStages.run heap (childFuel + extra) inputs ownAfter).bind _ = _
            rw [childrenRun extra]
            simp only [Option.bind_some, singletonRows]
            rfl
          · simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
              reduceCtorEq, iff_self]
          · intro action prepared
            simp only [SourcePruningEnumerationEdgeTraversal.prepare, prefixPrepared,
              Option.some.injEq] at prepared
            subst action
            refine ⟨[(some fragment, finished)], finished, rfl, ?_, (by dsimp only [finished,
              EnumerationExpandableIndex.Cached.frame]; omega), childrenAligned,
              childrenForest.trans ownForest, childrenPaths, ?_, childrenRealized,
              childrenCounts, childrenFlags, Or.inr ⟨some fragment, rfl, ?_⟩⟩
            · rw [bind_single _ _ before.core ownAfter.core _ (by simpa only [ExceptT.run] using prefixRaw)]
              rw [← stagedSame]
              rw [bind_single _ _ ownAfter.core childrenAfter.core (some fragments)
                (by simpa only [ExceptT.run, singletonRows, List.map_cons, List.map_nil] using childrenRaw)]
              cases residual with
              | none => rfl
              | some guard =>
                simp only [recordResidual, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont,
                  modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                  pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
                  List.map_cons, List.map_nil, finished, fragment, EnumerationExpandableIndex.Cached.frame]
            · cases residual with
              | none => exact childrenStorage
              | some guard => exact guard_storage childrenAfter.core childrenStorage guard fragment nodeBound
            · intro returned same
              cases same
              exact nodeBound
  · refine ⟨0, some ([], before), ?_, ?_, ?_⟩
    · intro extra
      simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
        Option.bind_some]
    · simp only [SourcePruningEnumerationEdgeTraversal.prepare,
        SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, reduceCtorEq, iff_self]
    · intro action prepared
      simp only [SourcePruningEnumerationEdgeTraversal.prepare,
        SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, Option.some.injEq] at prepared
      subst action
      refine ⟨[], before, rfl, ?_, Nat.le_refl _, storage.aligned, rfl, paths, storage,
        realized, counts, flags, Or.inl rfl⟩
      rw [run_bind]
      rfl

end MicroCFTA.SourcePruningEnumerationCachedEdge
