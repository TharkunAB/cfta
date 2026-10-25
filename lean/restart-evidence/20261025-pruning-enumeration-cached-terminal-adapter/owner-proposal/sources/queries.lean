import MicroCFTA.SourceEndpointReachability
import MicroCFTA.SourceUnconstrainedMemo

/-!
# Ordered completed calls of the endpoint descendant memo

Each recursive child call performs its own memo lookup. Mu calls use the
existing constraint-predicate memo. False children pass both returned memos
to the next child. True children stop the scan. The constructor heap is read
only. These are completed memo entries. Lazy publication, in-flight entries,
concurrency, typed cache selection, and native storage remain source limits.
-/
namespace MicroCFTA.SourceEndpointMemo
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex
open InternedBinderProtocol (NodeRef)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- The descendant memo retains complete immutable inputs and completed Boolean reads. -/
abbrev Memo := NodeRef → Option (Value Symbol Guard × Bool)

/-- Saved descendant answers match the physical record and the concrete source predicate. -/
def Correct (heap : State Symbol Guard) (memo : Memo) : Prop :=
  ∀ key input answer, memo key = some (input, answer) → input.referenceOf = key ∧
    Available heap input ∧ answer = SourceEndpointReachability.reaches SourceMemoGate.unconstrained input

/-- A descendant traversal carries its own memo and the separate constraint-predicate memo. -/
structure Memos where
  descendants : Memo
  predicate : SourceUnconstrainedMemo.Memo

/-- Both memo families retain complete resident inputs and exact answers. -/
structure Valid (heap : State Symbol Guard) (memos : Memos) : Prop where
  descendants : Correct heap memos.descendants
  predicate : SourceUnconstrainedMemo.Correct heap memos.predicate

/-- Every earlier completed entry remains unchanged in its own memo family. -/
structure Keeps (before after : Memos) : Prop where
  descendants : Extends before.descendants after.descendants
  predicate : Extends before.predicate after.predicate

/-- Both memo families start without saved results. -/
def empty : Memos := ⟨fun _ => none, SourceUnconstrainedMemo.empty⟩

/-- Empty memo families are valid in every physical heap. -/
theorem empty_valid (heap : State Symbol Guard) : Valid heap empty := by
  constructor
  · intro key input answer impossible; cases impossible
  · exact SourceUnconstrainedMemo.empty_correct heap

/-- No memo effect preserves every earlier completed entry. -/
theorem keeps_refl (memos : Memos) : Keeps memos memos := ⟨extends_refl _, extends_refl _⟩

/-- Consecutive completed calls preserve both memo histories. -/
theorem keeps_trans (first : Keeps before middle) (second : Keeps middle after) : Keeps before after :=
  ⟨extends_trans first.descendants second.descendants, extends_trans first.predicate second.predicate⟩

/-- Save the first completed value under its actual tagged physical identity. -/
def save (memo : Memo) (input : Value Symbol Guard) (answer : Bool) : Memo :=
  match memo input.referenceOf with
  | some _ => memo
  | none => fun key => if key = input.referenceOf then some (input, answer) else memo key

/-- Saving a completed descendant query retains every previous entry. -/
theorem save_extends (memo : Memo) (input : Value Symbol Guard) (answer : Bool) :
    Extends memo (save memo input answer) := by
  cases absent : memo input.referenceOf with
  | some pair => simpa only [save, absent] using extends_refl memo
  | none =>
      intro key original found
      simp only [save, absent]
      split
      · rename_i same
        subst key
        rw [absent] at found
        cases found
      · exact found

/-- A new completed answer preserves the exact descendant-memo invariant. -/
theorem save_correct (heap : State Symbol Guard) (memo : Memo) (correct : Correct heap memo)
    (input : Value Symbol Guard) (available : Available heap input) (answer : Bool)
    (actual : answer = SourceEndpointReachability.reaches SourceMemoGate.unconstrained input) :
    Correct heap (save memo input answer) := by
  cases absent : memo input.referenceOf with
  | some pair => simpa only [save, absent] using correct
  | none =>
      intro key original result found
      simp only [save, absent] at found
      split at found
      · rename_i same
        have fields : input = original ∧ answer = result := by
          simpa only [Option.some.injEq, Prod.mk.injEq] using found
        rcases fields with ⟨rfl, rfl⟩
        exact ⟨same.symm, available, actual⟩
      · exact correct key original result found

/-- Actual constructor and reservation growth preserve both memo families. -/
theorem grows (before after : State Symbol Guard) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (memos : Memos) (valid : Valid before memos) :
    Valid after memos := by
  refine ⟨?_, SourceUnconstrainedMemo.grows before after growth history memos.predicate valid.predicate⟩
  intro key input answer found
  obtain ⟨identity, available, actual⟩ := valid.descendants key input answer found
  exact ⟨identity, available.grows before after growth history, actual⟩

/-- Constraint-predicate memo execution also retains every earlier completed entry. -/
theorem predicate_extends (input : Value Symbol Guard) (memo : SourceUnconstrainedMemo.Memo) :
    Extends memo (SourceUnconstrainedMemo.run input memo).2 := by
  cases found : memo input.referenceOf with
  | some pair => simpa only [SourceUnconstrainedMemo.run, found] using extends_refl memo
  | none =>
      intro key original present
      simp only [SourceUnconstrainedMemo.run, found, SourceUnconstrainedMemo.insert]
      split
      · rename_i same
        subst key
        rw [found] at present
        cases present
      · exact present

mutual
/-- Execute lookup, the actual recursive helper body, and first-value storage. -/
noncomputable def run (value : Value Symbol Guard) (memos : Memos) : Bool × Memos :=
  match memos.descendants value.referenceOf with
  | some (_, answer) => (answer, memos)
  | none =>
      let result :=
        if value.depth == 0 then (false, memos) else
          match value with
          | .mu .. =>
              let predicate := SourceUnconstrainedMemo.run value memos.predicate
              (!predicate.1, { memos with predicate := predicate.2 })
          | .union _ members _ _ => many members memos
          | .node _ edges _ _ => rows edges memos
          | _ => (false, memos)
      (result.1, {result.2 with descendants := save result.2.descendants value result.1})
termination_by sizeOf value

/-- Each false child passes both memos to the next original child. -/
noncomputable def many (values : List (Value Symbol Guard)) (memos : Memos) : Bool × Memos :=
  match values with
  | [] => (false, memos)
  | first :: rest =>
      let head := run first memos
      if head.1 then head else many rest head.2
termination_by sizeOf values

/-- Each false edge passes both memos to the next original edge. -/
noncomputable def rows (edges : List (EdgeValue Symbol Guard)) (memos : Memos) : Bool × Memos :=
  match edges with
  | [] => (false, memos)
  | .mk _ children :: rest =>
      let head := many children memos
      if head.1 then head else rows rest head.2
termination_by sizeOf edges
end

end MicroCFTA.SourceEndpointMemo
