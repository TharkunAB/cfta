import MicroCFTA.SourceEqualityOriginalAllocationHistory
import MicroCFTA.Language

/-!
# Serial preparation of original equality fields

Each constructor receives the interner returned by the preceding field.
The first error retains its reached interner and skips the remaining list.
Normalized inputs derive one actual history and exact final field loads.
This schedule does not assert GHC field demand order.
-/
namespace MicroCFTA.SourceEqualityOriginalAllocationPreparation
open Cache Language SourceEqualityConstraintAllocation
open SourceEqualityOriginalAllocationHistory
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Guard" => SourceSymbolicIndex.Constraint

/-- Construct each listed field in order while retaining the caller's interner. -/
def prepare : List (Guard Formula) → Cache.State Key → Except String (List Value) × Cache.State Key
  | [], before => (.ok [], before)
  | original :: rest, before =>
      let first := construct original.equalities before
      match first.1 with
      | .error message => (.error message, first.2)
      | .ok value =>
          let tail := prepare rest first.2
          (tail.1.map (fun values => value :: values), tail.2)

/-- A failed head retains its actual cache and does not evaluate its suffix. -/
theorem prepare_head_error (original : Guard Formula) (rest : List (Guard Formula))
    (before after : Cache.State Key) (message : String)
    (failed : construct original.equalities before = (.error message, after)) :
    prepare (original :: rest) before = (.error message, after) := by
  simp only [prepare, failed]

/-- A failed tail retains every earlier constructor effect and its exact error. -/
theorem prepare_tail_error (original : Guard Formula) (rest : List (Guard Formula))
    (before middle after : Cache.State Key) (value : Value) (message : String)
    (first : construct original.equalities before = (.ok value, middle))
    (tail : prepare rest middle = (.error message, after)) :
    prepare (original :: rest) before = (.error message, after) := by
  simp only [prepare, first, tail, Except.map]

/-- Successful serial construction keeps the literal list order and returned cache. -/
theorem prepare_cons_done (original : Guard Formula) (rest : List (Guard Formula))
    (before middle after : Cache.State Key) (value : Value) (values : List Value)
    (first : construct original.equalities before = (.ok value, middle))
    (tail : prepare rest middle = (.ok values, after)) :
    prepare (original :: rest) before = (.ok (value :: values), after) := by
  simp only [prepare, first, tail, Except.map]

private theorem history_append {before middle after : Cache.State Key}
    {first second : List (Guard Formula)} (earlier : History before middle first)
    (later : History middle after second) : History before after (first ++ second) := by
  induction later with
  | start => simpa only [List.append_nil] using earlier
  | construct history cached done ih =>
      simpa only [List.append_assoc] using History.construct ih cached done
  | interleave history steps ih => exact History.interleave ih steps

/-- Each listed result retains its exact source field at the final interner. -/
def Field (cache : Cache.State Key) (original : Guard Formula) (value : Value) : Prop :=
  Ready cache value ∧
    SourceEqualityConstraintFieldLookup.load original cache = .ok (some ⟨value, original.guard⟩) ∧
    SourceEqualityConjoinAllocation.readback (⟨value, original.guard⟩ : SourceEqualityConjoinAllocation.Constraint Formula) = original ∧
    SourceEqualityPhysicalPayload.read original.equalities = .ok value.payload ∧
    SourceEqualityInheritedPayload.classes value.payload = original.equalities

/-- The completed list has one causal history and ordered final readback receipts. -/
structure Receipt (originals : List (Guard Formula)) (before : Cache.State Key)
    (values : List Value) (after : Cache.State Key) : Prop where
  done : prepare originals before = (.ok values, after)
  history : History before after originals
  valid : Cache.Valid after
  steps : Cache.Steps before after
  origins : ∀ original ∈ originals, SourceEqualityOriginalFieldOrigins.Origin after original
  fields : All₂ (Field after) originals values

/-- Actual atomic allocation steps retain every earlier canonical entry. -/
theorem Receipt.retained {originals : List (Guard Formula)} {before after : Cache.State Key} {values : List Value}
    (receipt : Receipt originals before values after) : Cache.Extends before.table after.table :=
  Cache.steps_table_extends receipt.steps

/-- Normalized fields derive finite serial completion without a supplied allocation result. -/
theorem prepare_complete (originals : List (Guard Formula)) (before : Cache.State Key) (valid : Cache.Valid before)
    (cached : ∀ original ∈ originals, SourceEqualityGuardReadback.Cached original.equalities) :
    ∃ values after, Receipt originals before values after := by
  induction originals generalizing before with
  | nil =>
      exact ⟨[], before, ⟨rfl, .start before, valid, .refl before,
        (by intro original absent; cases absent), .nil⟩⟩
  | cons original rest ih =>
      have firstCached := cached original List.mem_cons_self
      obtain ⟨value, middle, done, middleValid, ready, firstSteps, read, classes⟩ :=
        construct_complete original.equalities firstCached before valid
      obtain ⟨values, after, tail⟩ := ih middle middleValid
        (fun field member => cached field (List.mem_cons_of_mem original member))
      have history : History before after (original :: rest) := by
        simpa only [List.nil_append, List.singleton_append] using
          history_append (History.construct (.start before) firstCached done) tail.history
      have finalReady := ready.grows (Cache.steps_table_extends tail.steps)
      obtain ⟨loaded, readback, _⟩ := SourceEqualityConstraintFieldLookup.load_of_receipt original after firstCached value read finalReady
      exact ⟨value :: values, after,
        ⟨prepare_cons_done original rest before middle after value values done tail.done, history, tail.valid,
          steps_trans firstSteps tail.steps, (history.verified valid).2.2,
          .cons ⟨finalReady, loaded, readback, read, classes⟩ tail.fields⟩⟩

/-- Each listed original derives a successful read-only load from the prepared final cache. -/
theorem Receipt.load {originals : List (Guard Formula)} {before after : Cache.State Key} {values : List Value}
    (receipt : Receipt originals before values after) (original : Guard Formula) (member : original ∈ originals) :
    ∃ value : SourceEqualityConjoinAllocation.Constraint Formula,
      SourceEqualityConstraintFieldLookup.load original after = .ok (some value) ∧
      SourceEqualityConjoinAllocation.readback value = original ∧ Ready after value.stored ∧
      SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload := by
  have fields := receipt.fields
  clear receipt
  induction fields with
  | nil => cases member
  | @cons first value rest values field tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst original
        exact ⟨⟨value, first.guard⟩, field.2.1, field.2.2.1, field.1, field.2.2.2.1⟩
      · exact ih later

end MicroCFTA.SourceEqualityOriginalAllocationPreparation
