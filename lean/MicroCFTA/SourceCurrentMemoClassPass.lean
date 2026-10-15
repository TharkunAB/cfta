import MicroCFTA.SourceCurrentMemoSharedEditComplete
import MicroCFTA.SourceCurrentMemoSharedEditRetention
import MicroCFTA.SourceCurrentClassFoldDomains

/-!
# Class folds with the actual completed merge table

Each class captures the forest and merge table returned by its tail.
Class target slots start empty. Completed merge entries pass between classes.
Final empty propagation changes the forest and retains both returned states.
Word checks refer to the actual reached prefixes.
-/
namespace MicroCFTA.SourceCurrentMemoClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedEditGraph SourceCurrentMemoSharedEditRanges
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeOrigins (Produced)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A class keeps the current source edit trie and starts only its target slots empty. -/
inductive Class [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) :
    List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard →
      List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | edit (actual : EditList emptyGuard conjoin clear top record values
        (SourceEqualityClassFoldGraph.edits record) values (initial before memo) results shared) :
      Class emptyGuard conjoin clear top record values before memo results shared.native shared.memo

/-- The earlier class uses the exact forest, native state, and merge table returned by the tail. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard →
      List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | nil : Fold emptyGuard conjoin clear top [] values before memo values before memo
  | cons (tail : Fold emptyGuard conjoin clear top records values before memo middle next current)
      (head : Class emptyGuard conjoin clear top record middle next current results after saved) :
      Fold emptyGuard conjoin clear top (record :: records) values before memo results after saved

/-- Literal empty propagation runs once after every class has completed. -/
inductive Pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard →
      List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | done (fold : Fold emptyGuard conjoin clear top records values before memo results after saved) :
      Pass emptyGuard conjoin clear top records values before memo (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved

/-- One class needs only the checks reached from its actual captured state and merge table. -/
def ClassRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Native width Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  ListRanges emptyGuard conjoin clear top record values (SourceEqualityClassFoldGraph.edits record) values (initial before memo)

/-- Each next range plan uses an actual completed tail and its returned merge table. -/
inductive Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | nil : Ranges emptyGuard conjoin clear top [] values before memo
  | cons (tail : Ranges emptyGuard conjoin clear top records values before memo)
      (head : ∀ middle next current, Fold emptyGuard conjoin clear top records values before memo middle next current →
        ClassRanges emptyGuard conjoin clear top record middle next current) :
      Ranges emptyGuard conjoin clear top (record :: records) values before memo

private theorem compiled_safe (pairs : List (SourceEqualityEdits.Path × Action))
    (disjoint : pairs.Pairwise (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1))
    (values : List (Value Symbol Guard))
    (domains : ∀ path action, (path, action) ∈ pairs → ForestClosed path values)
    (entries : List (Int × Edits Action)) (compiled : build pairs = .editBelow entries) : ChildrenSafe entries 0 values := by
  intro query child found value selected path action retained
  have member : (Int.ofNat query :: path, action) ∈ leaves (build pairs) := by
    rw [compiled]
    exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves pairs disjoint).mem_iff.mp member
  exact domains (Int.ofNat query :: path) action original value
    (by simpa only [SourceCurrentEditDomains.select_natural] using selected)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- An actual class retains stored merge entries, producer histories, and every original selected domain. -/
theorem class_effects {record values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before memo results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ CostHeap after.machine.heap ∧ Stored after.machine.heap saved ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ query, ForestClosed query values → ForestClosed query results) ∧ Extends memo saved ∧
      (Produced clear top memo → Produced clear top saved) := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have nonroot := SourceEqualityClassEdits.edits_nonroot record.paths
    (SourceEqualityClassEdits.supported_nonroot record.paths supported active) id
  have originalDomains : ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → ForestClosed path values := by
    intro path action member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact domains original included
  cases actual with
  | edit actual =>
      change EditList emptyGuard conjoin clear top record values
        (build (SourceEqualityClassEdits.edits record.paths id)) values (initial before memo) results _ at actual
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before memo ready
        (pure_keeps _ ready.semantic.ready) costs stored
      have populated := build_populated (SourceEqualityClassEdits.edits record.paths id)
      have allowed := SourceEqualitySharedClassEdits.compiled_allowed record
      generalize compiled : build (SourceEqualityClassEdits.edits record.paths id) = edits at actual populated allowed
      cases actual with
      | leaf => exact False.elim (SourceEqualityEditCompiledPaths.build_not_leaf _ disjoint nonroot _ compiled)
      | @children entries _ _ _ _ children =>
          have safe := compiled_safe _ disjoint values originalDomains entries compiled
          have checked := SourceCurrentMemoSharedEditDomains.children_domains emptyGuard conjoin clear top record values
            before.machine.heap available domains children populated allowed initialReady available safe
          have entries := SourceCurrentMemoSharedEditRetention.children_entries emptyGuard conjoin clear top record values children
          exact ⟨checked.1.native, checked.1.costs, checked.1.stored, checked.2.1, checked.2.2.1,
            transport_forest checked.2.2.2, entries.1, entries.2⟩

/-- Reached word checks derive one finite class without closing unrelated siblings. -/
theorem class_complete (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : ClassRanges emptyGuard conjoin clear top record values before memo)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after saved, Class emptyGuard conjoin clear top record values before memo results after saved := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have nonroot := SourceEqualityClassEdits.edits_nonroot record.paths
    (SourceEqualityClassEdits.supported_nonroot record.paths supported active) id
  have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before memo ready
    (pure_keeps _ ready.semantic.ready) costs stored
  have populated := build_populated (SourceEqualityClassEdits.edits record.paths id)
  have allowed := SourceEqualitySharedClassEdits.compiled_allowed record
  change ListRanges emptyGuard conjoin clear top record values
    (build (SourceEqualityClassEdits.edits record.paths id)) values (initial before memo) at ranges
  generalize compiled : build (SourceEqualityClassEdits.edits record.paths id) = edits at ranges populated allowed
  have completed : ∃ results shared, EditList emptyGuard conjoin clear top record values edits values (initial before memo) results shared := by
    cases edits with
    | editAt target => exact False.elim (SourceEqualityEditCompiledPaths.build_not_leaf _ disjoint nonroot target compiled)
    | editBelow entries =>
        have originalDomains : ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → ForestClosed path values := by
          intro path action member
          obtain ⟨original, included, same⟩ := List.mem_map.mp member
          cases same
          exact domains original included
        have safe := compiled_safe _ disjoint values originalDomains entries compiled
        obtain ⟨results, shared, actual, _⟩ := SourceCurrentMemoSharedEditComplete.children_complete
          emptyGuard conjoin clear top record values before.machine.heap available domains
          ranges populated allowed initialReady available safe
        exact ⟨results, shared, .children actual⟩
  obtain ⟨results, shared, actual⟩ := completed
  exact ⟨results, shared.native, shared.memo, .edit (by simpa only [SourceEqualityClassFoldGraph.edits, compiled] using actual)⟩

/-- The actual right fold retains both states and derives each head domain from its tail. -/
theorem fold_effects {records values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ CostHeap after.machine.heap ∧ Stored after.machine.heap saved ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ query, ForestClosed query values → ForestClosed query results) ∧ Extends memo saved ∧
      (Produced clear top memo → Produced clear top saved) := by
  induction actual with
  | nil => exact ⟨ready, costs, stored, pure_keeps _ ready.semantic.ready, available, (fun _ domain => domain), extends_refl _, id⟩
  | cons tail head ih =>
      obtain ⟨nextReady, nextCosts, nextStored, firstKeeps, firstAvailable, firstDomains, firstEntries, firstOrigins⟩ :=
        ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
          (fun record member => domains record (List.mem_cons_of_mem _ member))
      obtain ⟨finalReady, finalCosts, finalStored, lastKeeps, resultAvailable, resultDomains, lastEntries, lastOrigins⟩ :=
        class_effects emptyGuard conjoin clear top head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
          nextReady nextCosts nextStored firstAvailable (fun path member => firstDomains _ (domains _ List.mem_cons_self path member))
      exact ⟨finalReady, finalCosts, finalStored, firstKeeps.trans lastKeeps, resultAvailable,
        (fun path domain => resultDomains path (firstDomains path domain)), extends_trans firstEntries lastEntries,
        fun produced => lastOrigins (firstOrigins produced)⟩

/-- Finite actual-prefix checks construct the right fold with its returned merge table. -/
theorem fold_complete {records values} {before : Native width Symbol Guard} {memo : Memo Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after saved, Fold emptyGuard conjoin clear top records values before memo results after saved := by
  induction ranges with
  | nil => exact ⟨_, _, _, .nil⟩
  | cons tail head ih =>
      obtain ⟨middle, next, current, first⟩ := ih
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
        (fun record member => domains record (List.mem_cons_of_mem _ member))
      obtain ⟨nextReady, nextCosts, nextStored, _, firstAvailable, firstDomains, _⟩ :=
        fold_effects emptyGuard conjoin clear top first
          (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
          (fun record member => domains record (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, saved, last⟩ := class_complete emptyGuard conjoin clear top _
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) middle next current
        (head middle next current first) nextReady nextCosts nextStored firstAvailable
        (fun path member => firstDomains _ (domains _ List.mem_cons_self path member))
      exact ⟨results, after, saved, .cons first last⟩

/-- A finite pass retains physical invariants and actual producers through final empty propagation. -/
theorem finite {records values} {before : Native width Symbol Guard} {memo : Memo Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after saved, Pass emptyGuard conjoin clear top records values before memo results after saved ∧
      IdleReady emptyGuard conjoin after ∧ CostHeap after.machine.heap ∧ Stored after.machine.heap saved ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ query, ForestClosed query values → ForestClosed query results) ∧ Extends memo saved ∧
      (Produced clear top memo → Produced clear top saved) := by
  obtain ⟨results, after, saved, actual⟩ := fold_complete emptyGuard conjoin clear top ranges coherent active ready costs stored available domains
  obtain ⟨finalReady, finalCosts, finalStored, kept, resultAvailable, resultDomains, entries, origins⟩ :=
    fold_effects emptyGuard conjoin clear top actual coherent active ready costs stored available domains
  exact ⟨_, after, saved, .done actual, finalReady, finalCosts, finalStored, kept,
    SourceCurrentClassFoldDomains.propagate_available _ _ resultAvailable,
    (fun path domain => SourceCurrentClassFoldDomains.propagate_domains _ path (resultDomains path domain)), entries, origins⟩

/-- An empty merge table derives every completed entry from an actual producer in this pass. -/
theorem finite_cold {records values} {before : Native width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before SourceCurrentMemoMergeGraph.empty)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after saved, Pass emptyGuard conjoin clear top records values before SourceCurrentMemoMergeGraph.empty results after saved ∧
      IdleReady emptyGuard conjoin after ∧ CostHeap after.machine.heap ∧ Stored after.machine.heap saved ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ query, ForestClosed query values → ForestClosed query results) ∧ Produced clear top saved := by
  obtain ⟨results, after, saved, actual, finalReady, finalCosts, finalStored, kept, resultAvailable, resultDomains, _, origins⟩ :=
    finite emptyGuard conjoin clear top ranges coherent active ready costs
      (SourceCurrentMemoMergeEffects.stored_empty _) available domains
  exact ⟨results, after, saved, actual, finalReady, finalCosts, finalStored, kept, resultAvailable, resultDomains,
    origins (SourceCurrentMemoMergeOrigins.produced_empty clear top)⟩

end MicroCFTA.SourceCurrentMemoClassPass
