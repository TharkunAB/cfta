import MicroCFTA.SourceSynthesisNormalizedVariablePaths
import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourceEqualityInheritedPayload

/-!
# Inherited path progress along Top-only Type segments

Joint prefix freedom prevents normalization from adding endpoints. Actual
Top combination preserves that property. Actual trie descent removes one
child index. Original generalized-Type readback supplies the initial
property and its original-Type budget. A new non-Top guard can invalidate
joint prefix freedom. These laws do not cover that conjunction or establish
whole Type progress, reached-state closure, or a total execution bound.
-/
namespace MicroCFTA.SourceSynthesisTypeDescentProgress
open EqualityNormalize SourceEqualityClassOrder
open SourceSynthesisTypeSyntax (Ty)
open SourceSynthesisGeneralizeSyntax (top eqGuard equalityClasses)
open SourceEqualityDescend (WellFormed descend)
local notation "Payload" => SourceEqualityPrecheck.Constraint
local notation "classes" => SourceEqualityInheritedPayload.classes
local notation "combine" => SourceEqualityInheritedPayload.combine

/-- Read the finite endpoint set from the actual physical payload. -/
def endpoints (input : Payload) : List Path := members ((classes input).getD [])

/-- Prefix freedom ranges jointly over every physical class. -/
def JointPrefixFree (input : Payload) : Prop :=
  ∀ first ∈ endpoints input, ∀ second ∈ endpoints input, first.IsPrefix second → first = second

/-- Use the existing trie budget, one plus the maximum endpoint length. -/
def budget (input : Payload) : Nat := EqualityTrie.pathBudget (endpoints input)

/-- One actual Top step derives these facts about its combined payload and all children. -/
structure Progress (inherited combined : Payload) : Prop where
  wellFormed : WellFormed combined
  prefixFree : JointPrefixFree combined
  budget_le : budget combined ≤ budget inherited
  child_prefixFree : ∀ index, JointPrefixFree (descend combined index)
  child_endpoints : ∀ index path, path ∈ endpoints (descend combined index) → path.length + 1 < budget inherited
  child_strict : ∀ index, 1 < budget inherited → budget (descend combined index) < budget inherited

private theorem read_classes (equalities : Option Constraints)
    (cached : SourceEqualityGuardReadback.Cached equalities) (payload : Payload)
    (actual : SourceEqualityPhysicalPayload.read equalities = .ok payload) : classes payload = equalities := by
  cases equalities with
  | none =>
      have same : payload = none := by
        simpa only [SourceEqualityPhysicalPayload.read, Except.ok.injEq] using actual.symm
      subst payload
      rfl
  | some originals =>
      obtain ⟨records, built, _valid, paths⟩ := SourceEqualityPhysicalPayload.normal_records originals (cached originals rfl)
      have same : payload = some records := by
        simpa only [SourceEqualityPhysicalPayload.read, built, Except.ok.injEq] using actual.symm
      subst payload
      change some (records.map Record.paths) = some originals
      exact congrArg some paths

private theorem pathBudget_le (paths : List Path) (bound : Nat) (positive : 0 < bound) :
    (∀ path ∈ paths, path.length < bound) → EqualityTrie.pathBudget paths ≤ bound := by
  induction paths with
  | nil => intro _; exact positive
  | cons first rest ih =>
      intro bounded
      have firstBound := bounded first List.mem_cons_self
      have tailBound := ih (fun path member => bounded path (List.mem_cons_of_mem _ member))
      unfold EqualityTrie.pathBudget at tailBound ⊢
      simp only [List.map_cons, List.foldr_cons]
      have maximum : Nat.max first.length ((rest.map List.length).foldr Nat.max 0) < bound :=
        Nat.max_lt.mpr ⟨firstBound, by omega⟩
      omega

private theorem budget_positive (input : Payload) : 0 < budget input := by
  unfold budget EqualityTrie.pathBudget
  omega

private theorem top_classes_origin (input : Option Constraints)
    (prefixFree : ∀ first ∈ members (input.getD []), ∀ second ∈ members (input.getD []),
      first.IsPrefix second → first = second) :
    ∀ path ∈ members ((SourceCompactGuards.combineEqualities input (some [])).getD []),
      path ∈ members (input.getD []) := by
  cases input with
  | none => simp [SourceCompactGuards.combineEqualities, members]
  | some originals =>
      cases originals with
      | nil => simp [SourceCompactGuards.combineEqualities, members]
      | cons first rest =>
          change ∀ path ∈ members ((SourceCompactGuards.normalize ((first :: rest) ++ [])).getD []),
            path ∈ members (first :: rest)
          simp only [List.append_nil]
          cases computed : SourceCompactGuards.normalize (first :: rest) with
          | none => simp [members]
          | some output =>
              intro path member
              change path ∈ members output at member
              exact EqualityNormalizePrefixFree.normalize_mem_original (first :: rest) output
                prefixFree computed path member

private theorem top_origins {inherited combined : Payload} (prefixFree : JointPrefixFree inherited)
    (actual : combine inherited (some []) = .ok combined) :
    ∀ path ∈ endpoints combined, path ∈ endpoints inherited := by
  have same := read_classes (SourceCompactGuards.combineEqualities (classes inherited) (some []))
    (SourceEqualityGuardReadback.combine_cached _ _) combined actual
  intro path member
  apply top_classes_origin (classes inherited) prefixFree path
  simpa only [endpoints, same] using member

private theorem descend_origin (input : Payload) (wellFormed : WellFormed input) (index : Nat)
    (path : Path) (member : path ∈ endpoints (descend input index)) : index :: path ∈ endpoints input := by
  cases input with
  | none => simp [endpoints, SourceEqualityInheritedPayload.classes, descend, members] at member
  | some originals =>
      cases originals with
      | nil => simp [endpoints, SourceEqualityInheritedPayload.classes, descend, members] at member
      | cons first rest =>
          obtain ⟨paths, mapped, found⟩ := (mem_members _ _).mp member
          obtain ⟨output, present, rfl⟩ := List.mem_map.mp mapped
          have kept := (SourceEqualityDescend.records_perm index (first :: rest)).mem_iff.mp present
          obtain ⟨original, included, built⟩ := List.mem_filterMap.mp kept
          have source := (SourceEqualityDescend.record_pairs index original
            (wellFormed (first :: rest) rfl original included).1 output built path).mp found
          exact (mem_members _ _).mpr
            ⟨original.paths, List.mem_map.mpr ⟨original, included, rfl⟩, source⟩

private theorem type_positive (typ : Ty) : 0 < sizeOf typ := by
  cases typ with
  | tVar name => simp only [Ty.tVar.sizeOf_spec]; omega
  | tFun argument result => simp only [Ty.tFun.sizeOf_spec]; omega
  | tCons name arguments => simp only [Ty.tCons.sizeOf_spec]; omega

/-- Actual generalized-Type readback derives the initial joint invariant and original-Type budget. -/
theorem source_read (typ : Ty) (payload : Payload)
    (actual : SourceEqualityPhysicalPayload.own (eqGuard (equalityClasses typ)) = .ok payload) :
    JointPrefixFree payload ∧ budget payload ≤ sizeOf typ ∧ WellFormed payload := by
  have cached : SourceEqualityGuardReadback.Cached (eqGuard (equalityClasses typ)).equalities := by
    rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
    exact SourceEqualityGuardReadback.normalize_cached _
  have readDone : SourceEqualityPhysicalPayload.read (eqGuard (equalityClasses typ)).equalities = .ok payload := by
    simpa only [SourceEqualityPhysicalPayload.own, SourceSynthesisGuardRegions.eqGuard_accessor] using actual
  have same := read_classes _ cached payload readDone
  have paths : endpoints payload = members ((eqGuard (equalityClasses typ)).equalities.getD []) := by
    rw [endpoints, same]
  refine ⟨?_, ?_, SourceEqualityInheritedPayload.read_wellFormed _ cached payload readDone⟩
  · intro first firstIn second secondIn pfx
    rw [paths] at firstIn secondIn
    exact SourceSynthesisNormalizedVariablePaths.eqGuard_prefix_free typ first second firstIn secondIn pfx
  · apply pathBudget_le _ _ (type_positive typ)
    intro path member
    rw [paths] at member
    exact SourceSynthesisNormalizedVariablePaths.eqGuard_length_lt_sizeOf typ path member

/-- Actual Top combination and trie descent preserve joint prefix freedom and decrease positive endpoint budgets. -/
theorem top_descend (inherited combined : Payload) (prefixFree : JointPrefixFree inherited)
    (actual : combine inherited (some []) = .ok combined) : Progress inherited combined := by
  have wellFormed := (SourceEqualityInheritedPayload.combine_exact (Symbol := Unit) actual).1
  have original := top_origins prefixFree actual
  have childOriginal : ∀ index path, path ∈ endpoints (descend combined index) →
      index :: path ∈ endpoints inherited :=
    fun index path member => original _ (descend_origin combined wellFormed index path member)
  have childBound : ∀ index path, path ∈ endpoints (descend combined index) → path.length + 1 < budget inherited := by
    intro index path member
    have bound := EqualityTrie.pathBudget_sufficient (endpoints inherited) (index :: path) (childOriginal index path member)
    simpa only [List.length_cons, budget] using bound
  refine ⟨wellFormed, ?_, ?_, ?_, childBound, ?_⟩
  · intro first firstIn second secondIn pfx
    exact prefixFree first (original first firstIn) second (original second secondIn) pfx
  · apply pathBudget_le _ _ (budget_positive inherited)
    intro path member
    exact EqualityTrie.pathBudget_sufficient (endpoints inherited) path (original path member)
  · intro index first firstIn second secondIn pfx
    have same := prefixFree (index :: first) (childOriginal index first firstIn)
      (index :: second) (childOriginal index second secondIn) (List.cons_prefix_cons.mpr ⟨rfl, pfx⟩)
    exact (List.cons.inj same).2
  · intro index positive
    have reduced : budget (descend combined index) ≤ budget inherited - 1 := by
      apply pathBudget_le _ _ (by omega)
      intro path member
      have bound := childBound index path member
      omega
    omega

/-- The actual Top accessor and combination complete without a supplied normalizer outcome. -/
theorem top_complete (inherited : Payload) (prefixFree : JointPrefixFree inherited) :
    ∃ combined, SourceEqualityPhysicalPayload.own top = .ok (some []) ∧
      combine inherited (some []) = .ok combined ∧ Progress inherited combined := by
  obtain ⟨combined, actual, _wellFormed, _meaning⟩ :=
    SourceEqualityInheritedPayload.combine_complete (Symbol := Unit) inherited (some [])
  exact ⟨combined, rfl, actual, top_descend inherited combined prefixFree actual⟩

/-- Original generalized-Type syntax supplies the start of an actual Top-only progress segment. -/
theorem source_step (typ : Ty) :
    ∃ inherited combined, SourceEqualityPhysicalPayload.own (eqGuard (equalityClasses typ)) = .ok inherited ∧
      SourceEqualityPhysicalPayload.own top = .ok (some []) ∧
      combine inherited (some []) = .ok combined ∧ budget inherited ≤ sizeOf typ ∧ Progress inherited combined := by
  have cached : SourceEqualityGuardReadback.Cached (eqGuard (equalityClasses typ)).equalities := by
    rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
    exact SourceEqualityGuardReadback.normalize_cached _
  obtain ⟨inherited, readDone, _wellFormed, _meaning⟩ := SourceEqualityInheritedPayload.read_complete
    (Symbol := Unit) (eqGuard (equalityClasses typ)).equalities cached
  have ownDone : SourceEqualityPhysicalPayload.own (eqGuard (equalityClasses typ)) = .ok inherited := by
    simpa only [SourceEqualityPhysicalPayload.own, SourceSynthesisGuardRegions.eqGuard_accessor] using readDone
  have source := source_read typ inherited ownDone
  obtain ⟨combined, ownTop, actual, progress⟩ := top_complete inherited source.1
  exact ⟨inherited, combined, ownDone, ownTop, actual, source.2.1, progress⟩

end MicroCFTA.SourceSynthesisTypeDescentProgress
