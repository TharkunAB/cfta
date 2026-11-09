import MicroCFTA.SourceCurrentAllocatedReadDeterminism
import MicroCFTA.SourceEqualityProjectionOutcomeGlobalMemos

/-!
# Unique returned memos for literal projection reads

The proof compares the same bounded read sequence. It retains each stopped
prefix and every repeated exposure. No heap invariant or memo correctness
assumption is required. Global bundles also retain their exact query tables.
-/
namespace MicroCFTA.SourceEqualityProjectionOutcomeReadDeterminism
open Cache InternedConstructorTemplates
open SourceEqualityProjectionOutcomeMemos (ProjectReads RowsReads ForestReads)
open SourceEqualityProjectionOutcomePrimitives (ReadAllReads HeadReads UnionReads)
open SourceEqualityRequiredGraph (Recursive)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One ordered operand exposure has one returned unfolding table, on every outcome. -/
theorem readAll_unique {h : Nat} {values : List Node} {before : Heap} {memo first second : UMemo}
    (left : ReadAllReads h values before memo first) (right : ReadAllReads h values before memo second) :
    first = second := by
  induction values generalizing before memo first second with
  | nil => cases left; cases right; rfl
  | cons value values ih =>
      cases left with
      | cons actualLeft firstLeft restLeft =>
          cases right with
          | cons actualRight firstRight restRight =>
              obtain ⟨rfl, rfl⟩ := MergedSourceExposure.Result.done.inj (actualLeft.symm.trans actualRight)
              have same := SourceCurrentAllocatedReadDeterminism.exposure_unique firstLeft firstRight
              cases same
              exact ih restLeft restRight
          | pending actualRight callsRight =>
              rw [actualLeft] at actualRight
              cases actualRight
          | unresolved actualRight callsRight =>
              rw [actualLeft] at actualRight
              cases actualRight
          | exhausted actualRight callsRight =>
              rw [actualLeft] at actualRight
              cases actualRight
      | pending actualLeft callsLeft =>
          cases right with
          | cons actualRight firstRight restRight =>
              rw [actualLeft] at actualRight
              cases actualRight
          | pending actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | unresolved actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | exhausted actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
      | unresolved actualLeft callsLeft =>
          cases right with
          | cons actualRight firstRight restRight =>
              rw [actualLeft] at actualRight
              cases actualRight
          | pending actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | unresolved actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | exhausted actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
      | exhausted actualLeft callsLeft =>
          cases right with
          | cons actualRight firstRight restRight =>
              rw [actualLeft] at actualRight
              cases actualRight
          | pending actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | unresolved actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight
          | exhausted actualRight callsRight =>
              exact SourceCurrentAllocatedReadDeterminism.exposure_unique callsLeft callsRight

/-- Head reconstruction retains the unique memo from its sole actual exposure. -/
theorem head_unique {h : Nat} {value : Node} {before : Heap} {memo first second : UMemo}
    (left : HeadReads h value before memo first) (right : HeadReads h value before memo second) :
    first = second := by
  cases left with
  | read left =>
      cases right with
      | read right => exact SourceCurrentAllocatedReadDeterminism.exposure_unique left right

/-- Union reconstruction retains one exact ordered exposure memo on every outcome. -/
theorem union_unique {h : Nat} {values : List Node} {before : Heap} {memo first second : UMemo}
    (left : UnionReads h values before memo first) (right : UnionReads h values before memo second) :
    first = second := by
  cases left with
  | read left =>
      cases right with
      | read right => exact readAll_unique left right

private theorem rows_unique_from {p h : Nat} {path : List Int}
    (smaller : ∀ {value : Node} {before : Heap} {memo first second : UMemo},
      ProjectReads p h path value before memo first → ProjectReads p h path value before memo second → first = second)
    {index : Int} {edges : List Edge} {before : Heap} {memo first second : UMemo}
    (left : RowsReads p h path index edges before memo first)
    (right : RowsReads p h path index edges before memo second) : first = second := by
  induction edges generalizing before memo first second with
  | nil => cases left; cases right; rfl
  | cons edge edges ih =>
      cases left with
      | missing absentLeft restLeft =>
          cases right with
          | missing absentRight restRight =>
              exact ih restLeft restRight
          | selected foundRight actualRight firstRight restRight =>
              have impossible := absentLeft.symm.trans foundRight
              cases impossible
          | pending foundRight actualRight callsRight =>
              have impossible := absentLeft.symm.trans foundRight
              cases impossible
          | unresolved foundRight actualRight callsRight =>
              have impossible := absentLeft.symm.trans foundRight
              cases impossible
          | exhausted foundRight actualRight callsRight =>
              have impossible := absentLeft.symm.trans foundRight
              cases impossible
      | selected foundLeft actualLeft firstLeft restLeft =>
          cases right with
          | missing absentRight restRight =>
              have impossible := foundLeft.symm.trans absentRight
              cases impossible
          | selected foundRight actualRight firstRight restRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              obtain ⟨rfl, rfl⟩ := SourceEqualityRequiredWorker.Result.done.inj (actualLeft.symm.trans actualRight)
              have same := smaller firstLeft firstRight
              cases same
              exact ih restLeft restRight
          | pending foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
          | unresolved foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
          | exhausted foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
      | pending foundLeft actualLeft callsLeft =>
          cases right with
          | missing absentRight restRight =>
              have impossible := foundLeft.symm.trans absentRight
              cases impossible
          | selected foundRight actualRight firstRight restRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
          | pending foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | unresolved foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | exhausted foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
      | unresolved foundLeft actualLeft callsLeft =>
          cases right with
          | missing absentRight restRight =>
              have impossible := foundLeft.symm.trans absentRight
              cases impossible
          | selected foundRight actualRight firstRight restRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
          | pending foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | unresolved foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | exhausted foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
      | exhausted foundLeft actualLeft callsLeft =>
          cases right with
          | missing absentRight restRight =>
              have impossible := foundLeft.symm.trans absentRight
              cases impossible
          | selected foundRight actualRight firstRight restRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              rw [actualLeft] at actualRight
              cases actualRight
          | pending foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | unresolved foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight
          | exhausted foundRight actualRight callsRight =>
              have sameChild := Option.some.inj (foundLeft.symm.trans foundRight)
              cases sameChild
              exact smaller callsLeft callsRight

private theorem recursive_unique_from {p h : Nat} {path : List Int} {index : Int} {original : Node}
    (isRecursive : Recursive original)
    (smaller : ∀ {path : List Int} {value : Node} {before : Heap} {memo first second : UMemo},
      ProjectReads p h path value before memo first → ProjectReads p h path value before memo second → first = second)
    {before : Heap} {memo first second : UMemo}
    (left : ProjectReads (p + 1) h (index :: path) original before memo first)
    (right : ProjectReads (p + 1) h (index :: path) original before memo second) : first = second := by
  cases left <;> cases right
  case recursive.recursive =>
    rename_i value middle middleMemo recursiveLeft actualLeft firstLeft lastLeft
      other otherHeap otherMemo recursiveRight actualRight firstRight lastRight
    obtain ⟨rfl, rfl⟩ := SourceEqualityRequiredWorker.Result.done.inj (actualLeft.symm.trans actualRight)
    have same := head_unique firstLeft firstRight
    cases same
    exact smaller lastLeft lastRight
  case recursive_pending.recursive_pending =>
    exact head_unique (by assumption) (by assumption)
  case recursive_unresolved.recursive_unresolved =>
    exact head_unique (by assumption) (by assumption)
  case recursive_exhausted.recursive_exhausted =>
    exact head_unique (by assumption) (by assumption)
  all_goals simp_all [Recursive]

/-- One bounded node projection determines the returned unfolding table, including stopped prefixes. -/
theorem project_unique {p h : Nat} {path : List Int} {value : Node} {before : Heap}
    {memo first second : UMemo}
    (left : ProjectReads p h path value before memo first) (right : ProjectReads p h path value before memo second) :
    first = second := by
  induction p generalizing path value before memo first second with
  | zero => cases left; cases right; rfl
  | succ p ih =>
      cases path with
      | nil => cases left; cases right; rfl
      | cons index path =>
          cases value with
          | empty => cases left <;> cases right <;> simp_all [Recursive]
          | reference name => cases left <;> cases right <;> simp_all [Recursive]
          | node entry edges depth free =>
              have rowsUnique : ∀ {before : Heap} {memo first second : UMemo},
                  RowsReads p h path index edges before memo first →
                  RowsReads p h path index edges before memo second → first = second :=
                rows_unique_from (by intro value before memo first second left right; exact ih left right)
              cases left <;> cases right
              case ordinary.ordinary =>
                rename_i values middle middleMemo actualLeft firstLeft lastLeft
                  other otherHeap otherMemo actualRight firstRight lastRight
                obtain ⟨rfl, rfl⟩ := SourceEqualityRequiredWorker.Result.done.inj (actualLeft.symm.trans actualRight)
                have same := rowsUnique firstLeft firstRight
                cases same
                exact union_unique lastLeft lastRight
              case ordinary_pending.ordinary_pending =>
                exact rowsUnique (by assumption) (by assumption)
              case ordinary_unresolved.ordinary_unresolved =>
                exact rowsUnique (by assumption) (by assumption)
              case ordinary_exhausted.ordinary_exhausted =>
                exact rowsUnique (by assumption) (by assumption)
              all_goals simp_all [Recursive]
          | mu entry body depth ordinary =>
              exact recursive_unique_from (original := .mu entry body depth ordinary) trivial
                (by intro path value before memo first second left right; exact ih left right) left right
          | union entry members depth free =>
              exact recursive_unique_from (original := .union entry members depth free) trivial
                (by intro path value before memo first second left right; exact ih left right) left right

/-- One bounded row projection determines its exact ordered returned unfolding table. -/
theorem rows_unique {p h : Nat} {path : List Int} {index : Int} {edges : List Edge} {before : Heap}
    {memo first second : UMemo}
    (left : RowsReads p h path index edges before memo first)
    (right : RowsReads p h path index edges before memo second) : first = second :=
  rows_unique_from (by intro value before memo first second left right; exact project_unique left right) left right

/-- The same bounded forest projection has one returned unfolding table on every outcome. -/
theorem forest_unique {p h : Nat} {path : List Int} {values : List Node} {before : Heap}
    {memo first second : UMemo}
    (left : ForestReads p h path values before memo first) (right : ForestReads p h path values before memo second) :
    first = second := by
  cases path with
  | nil =>
      cases left with
      | root left =>
          cases right with
          | root right => exact union_unique left right
  | cons index path =>
      cases left with
      | missing absent =>
          cases right with
          | missing => rfl
          | selected found calls =>
              have impossible := absent.symm.trans found
              cases impossible
      | selected found left =>
          cases right with
          | missing absent =>
              have impossible := found.symm.trans absent
              cases impossible
          | selected other right =>
              have same := Option.some.inj (found.symm.trans other)
              cases same
              exact project_unique left right

/-- Ordered forest reads also determine the whole global memo bundle. -/
theorem forest_global_unique {p h : Nat} {path : List Int} {values : List Node} {before : Heap}
    {memo first second : Memos}
    (left : SourceEqualityProjectionOutcomeGlobalMemos.ForestReads p h path values before memo first)
    (right : SourceEqualityProjectionOutcomeGlobalMemos.ForestReads p h path values before memo second) :
    first = second := by
  have unfolding := forest_unique left.1 right.1
  have query := left.2.trans right.2.symm
  cases first
  cases second
  congr 1
  all_goals assumption

end MicroCFTA.SourceEqualityProjectionOutcomeReadDeterminism
