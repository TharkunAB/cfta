import MicroCFTA.SourceCurrentMemoSharedEditLanguage
import MicroCFTA.SourceCurrentMemoClassPass
import MicroCFTA.SourceEqualityEmptyPropagation

/-!
# Independent language of memo-aware class passes

Every class captures its actual tail result and completed merge table.
Selected path domains and language cache coverage pass through that tail.
The pass narrows the input forest and retains accepted terms that satisfy
all original classes. Final empty propagation preserves membership.
-/
namespace MicroCFTA.SourceCurrentMemoClassPassLanguage
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedEditGraph SourceCurrentMemoClassPass
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open InternedGuardedLanguage (meaning)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
variable (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))

include clearTrue topTrue conjoined

/-- An actual class derives returned cache coverage and its independent language bounds. -/
theorem class_language {record values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before memo results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (covered : CacheCovers holds ambient memo) :
    CacheCovers holds ambient saved ∧ ∀ symbol terms,
      (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (EqualityNormalize.ClassSat (.node symbol terms) record.paths →
        (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms)) := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have safe : SourceCurrentMemoSharedEditLanguage.ListSafe (build (SourceEqualityClassEdits.edits record.paths id)) values := by
    cases compiled : build (SourceEqualityClassEdits.edits record.paths id) with
    | editAt target => trivial
    | editBelow entries =>
        intro query child found value selected path action retained
        have member : (Int.ofNat query :: path, action) ∈ leaves (build (SourceEqualityClassEdits.edits record.paths id)) := by
          rw [compiled]
          exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
        obtain ⟨original, included, same⟩ := List.mem_map.mp ((SourceEqualityEditCompiledPaths.build_leaves _ disjoint).mem_iff.mp member)
        have domain := domains original included
        have same := congrArg Prod.fst same
        dsimp at same
        rw [same] at domain
        apply domain value
        change SourceEqualityProjectionGraph.select values (Int.ofNat query) = some value
        rw [select_natural]
        exact selected
  cases actual with
  | edit actual =>
      change EditList emptyGuard conjoin clear top record values
        (build (SourceEqualityClassEdits.edits record.paths id)) values (initial before memo) results _ at actual
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before memo ready
        (pure_keeps _ ready.semantic.ready) costs stored
      have nextCovered := SourceCurrentMemoSharedEditCaches.list_covered emptyGuard conjoin clear top record values before.machine.heap
        available domains holds ambient clearTrue topTrue conjoined actual (build_populated _)
        (SourceEqualitySharedClassEdits.compiled_allowed record) initialReady available safe covered
      refine ⟨nextCovered, ?_⟩
      intro symbol terms
      have matched : SourceEqualityEditAPI.ListCondition (fun path part => (Term.node symbol terms).atPath path = some part)
          (build (SourceEqualityClassEdits.edits record.paths id)) terms := by
        apply (SourceEqualityEditCompiledPaths.list_condition_exact _ _ disjoint
          (SourceEqualityClassEdits.edits_nonroot record.paths (SourceEqualityClassEdits.supported_nonroot record.paths supported active) id)
          symbol terms).mpr
        exact (SourceEqualityClassEdits.conditions_exact _ record.paths id (.node symbol terms)).mpr (fun _ _ _ selected => selected)
      have bounds := SourceCurrentMemoSharedEditLanguage.list emptyGuard conjoin clear top record values before.machine.heap available domains holds ambient
        (.node symbol terms) symbol terms coherent active clearTrue topTrue conjoined rfl actual
        (build_valid _) (build_populated _) (SourceEqualitySharedClassEdits.compiled_allowed record)
        initialReady covered available safe terms
      exact ⟨bounds.1, fun satisfied => ⟨bounds.1, fun accepted => bounds.2 accepted satisfied matched accepted⟩⟩

/-- The actual right fold derives each class domain and warm cache from its completed tail. -/
theorem fold_language {records values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (covered : CacheCovers holds ambient memo) :
    CacheCovers holds ambient saved ∧ ∀ symbol terms,
      (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms)) := by
  induction actual with
  | nil => exact ⟨covered, fun _ _ => ⟨id, fun _ => Iff.rfl⟩⟩
  | cons tail head ih =>
      have first := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
        (fun record member => domains record (List.mem_cons_of_mem _ member)) covered
      obtain ⟨nextReady, nextCosts, nextStored, _, firstAvailable, firstDomains, _⟩ :=
        fold_effects emptyGuard conjoin clear top tail
          (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
          (fun record member => domains record (List.mem_cons_of_mem _ member))
      have last := class_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
        head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) nextReady nextCosts nextStored firstAvailable
        (fun path member => firstDomains _ (domains _ List.mem_cons_self path member)) first.1
      refine ⟨last.1, ?_⟩
      intro symbol terms
      have firstBounds := first.2 symbol terms
      have lastBounds := last.2 symbol terms
      refine ⟨fun accepted => firstBounds.1 (lastBounds.1 accepted), ?_⟩
      intro satisfied
      exact ⟨fun accepted => firstBounds.1 (lastBounds.1 accepted), fun accepted =>
        (lastBounds.2 (satisfied _ List.mem_cons_self)).mpr
          ((firstBounds.2 (fun record member => satisfied record (List.mem_cons_of_mem _ member))).mpr accepted)⟩

/-- Literal final empty propagation preserves the bounds and returned cache coverage. -/
theorem pass_language {records values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (covered : CacheCovers holds ambient memo) :
    CacheCovers holds ambient saved ∧ ∀ symbol terms,
      (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms)) := by
  cases actual with
  | done fold =>
      have checked := fold_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
        fold coherent active ready costs stored available domains covered
      refine ⟨checked.1, ?_⟩
      intro symbol terms
      rw [SourceEqualityEmptyPropagation.exact holds ambient]
      exact checked.2 symbol terms

end MicroCFTA.SourceCurrentMemoClassPassLanguage
