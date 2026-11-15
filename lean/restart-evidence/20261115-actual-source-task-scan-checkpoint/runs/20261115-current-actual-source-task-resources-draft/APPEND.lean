namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSourceTaskResourceInduction
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (finish)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

attribute [local irreducible] nodePlan tuplePlan fallbackPlan identity_actual_frame_plan
  identity_actual_frame_reserved IdentityActualSourceRoot.limit IdentityActualSourceRoot.own

/-- Strong induction on actual work establishes resources for every actual source task. -/
private theorem identity_actual_source_task_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (root : IdentityActualSourceRoot bits)
    (selectionMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (task : IdentityActualSourceTask bits) :
    IdentityActualSourceCorrectAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root task := by
  have allTasks : ∀ (amount : Nat) (candidate : IdentityActualSourceTask bits),
      candidate.work root.limit = amount →
      IdentityActualSourceCorrectAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root candidate := by
    intro amount
    induction amount using Nat.strongRecOn with
    | ind amount smallerIH =>
      intro candidate measured
      have taskIH : ∀ smaller : IdentityActualSourceTask bits,
          smaller.work root.limit < candidate.work root.limit →
          IdentityActualSourceCorrectAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root smaller := by
        intro smaller decreased
        exact smallerIH (smaller.work root.limit) (by omega) smaller rfl
      cases candidate with
      | tuple point remaining =>
        cases remaining with
        | nil =>
          exact identity_actual_source_tuple_nil_resources graph checkEmpty edgesOf recursiveDepth workFuel
            metadata uv formulas solver workerIH root point selectionMembers selectionLength taskIH
        | cons head rest =>
          obtain ⟨incoming, bucket⟩ := head
          cases point with
          | mk frame completed caller before queries height count bound mass seed =>
            cases count with
            | zero =>
              intro scopeOriginal scopeBefore allInputs ancestors origin current
              obtain ⟨inputs, _fits, _known, _reserved⟩ := current
              obtain ⟨_shapes, _kept, _inventory, _memos, _packet, _query, _previous,
                _mass, capacity, _included, _genuine⟩ := inputs
              change ((incoming, bucket) :: rest).length ≤ 0 at capacity
              simp only [List.length_cons] at capacity
              omega
            | succ count =>
              let prior : IdentityActualSourcePoint bits := {
                frame := frame
                completed := completed
                caller := caller
                before := before
                queries := queries
                height := height
                count := count
                bound := bound
                mass := mass
                seed := seed }
              exact identity_actual_source_tuple_cons_resources graph checkEmpty edgesOf recursiveDepth workFuel
                metadata uv formulas solver root prior count incoming bucket rest taskIH
      | child point incoming bucket rest =>
        by_cases ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true
        · cases point with
          | mk frame completed caller before queries height count bound mass seed =>
            cases height with
            | zero =>
              intro scopeOriginal scopeBefore allInputs ancestors origin current
              obtain ⟨inputs, _fits, _known, _reserved⟩ := current
              obtain ⟨_shapes, _kept, _inventory, _memos, _packet, _query, _previous,
                _mass, _capacity, _included, genuine⟩ := inputs
              have ranked := (genuine incoming bucket List.mem_cons_self).2.2.1
              change MergedOrdinaryHeight.height incoming ≤ 0 at ranked
              cases incoming with
              | empty => cases ordinary
              | reference name => cases ordinary
              | node entry rows depth free =>
                  simp only [MergedOrdinaryHeight.height] at ranked
                  omega
              | union entry members depth free => cases ordinary
              | mu entry body depth payload => cases ordinary
            | succ height =>
              let prior : IdentityActualSourcePoint bits := {
                frame := frame
                completed := completed
                caller := caller
                before := before
                queries := queries
                height := height
                count := count
                bound := bound
                mass := mass
                seed := seed }
              exact identity_actual_source_ordinary_resources graph checkEmpty edgesOf recursiveDepth workFuel
                metadata uv formulas solver root prior height incoming bucket rest ordinary taskIH
        · have fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false := by
            cases classified : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming with
            | false => rfl
            | true => exact (ordinary classified).elim
          exact identity_actual_source_fallback_resources graph checkEmpty edgesOf recursiveDepth workFuel
            metadata uv formulas solver root point incoming bucket rest fallback taskIH
      | rows height point incoming bucket rest =>
        intro scopeOriginal scopeBefore allInputs ancestors origin current
        cases origin with
        | ordinaryRows basePoint sourceHeight sourceIncoming sourceBucket sourceRest previous ordinary =>
          cases incoming with
          | empty => cases ordinary
          | reference name => cases ordinary
          | union entry members depth free => cases ordinary
          | mu entry body depth payload => cases ordinary
          | node entry alternatives depth free =>
            exact identity_actual_source_rows_resources graph checkEmpty edgesOf recursiveDepth workFuel
              metadata uv formulas solver root basePoint height entry alternatives depth free bucket rest
              selectionMembers selectionLength taskIH scopeOriginal scopeBefore allInputs ancestors
              (.ordinaryRows basePoint height (.node entry alternatives depth free) bucket rest previous ordinary) current
  exact allTasks (task.work root.limit) task rfl

end ActualSourceTaskResourceInduction
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
