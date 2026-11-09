import MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement

/-!
# Coupled cell and row-spine origins

One origin list records the descriptors of all allocated requirement cells.
One source list records the raw tuples of all allocated row-spine handles.
A cached row identifies its chosen tuple, descriptor range, and exact tail
source in these same lists. The global per-handle assertion supplies each
tail assertion. It does not define another recursive executor or assume
semantic coverage of a final table.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsSemantics
open InternedConstructorTemplates (Value EdgeValue EdgeKey)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Refined" => SourceCurrentConjunctionRequirementCellsRefinement.Invariant

/-- The original tuple's combined classes use the actual source edge view. -/
noncomputable abbrev combined (tuple : Tuple) : Option EqualityNormalize.Constraints :=
  SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionEquality.edgeView)

/-- Each current spine retains its original raw source and exact registered descriptor handles. -/
def Spec (origins : List Cell) (sources : List (List Tuple)) (original : List Tuple) :
    Spine Symbol Formula → Prop
  | .pending tuples => tuples = original
  | .done none => ∀ tuple ∈ original, combined tuple = none
  | .done (some (handles, tail)) => ∃ skipped chosen rest constraints offset,
      original = skipped ++ chosen :: rest ∧
      (∀ tuple ∈ skipped, combined tuple = none) ∧
      combined chosen = some constraints ∧
      handles = List.range' offset (descriptors chosen constraints).length ∧
      (∀ index cell, (descriptors chosen constraints)[index]? = some cell →
        origins[offset + index]? = some cell) ∧
      sources[tail]? = some rest

/-- Cell and spine claims refer to the same current storage and immutable origin lists. -/
structure Invariant (origins : List Cell) (sources : List (List Tuple)) (before : Storage) : Prop where
  cells : Refined origins before.requirements
  length : sources.length = before.spines.length
  spines : ∀ handle original spine, sources[handle]? = some original →
    lookupSpine handle before = some spine → Spec origins sources original spine

/-- Appending origins preserves every old descriptor and tail-source lookup. -/
theorem Spec.weaken {origins : List Cell} {sources : List (List Tuple)} {original : List Tuple}
    {spine : Spine Symbol Formula} (spec : Spec origins sources original spine)
    (addedOrigins : List Cell) (addedSources : List (List Tuple)) :
    Spec (origins ++ addedOrigins) (sources ++ addedSources) original spine := by
  cases spine with
  | pending tuples => exact spec
  | done row =>
      cases row with
      | none => exact spec
      | some pair =>
          rcases pair with ⟨handles, tail⟩
          obtain ⟨skipped, chosen, rest, constraints, offset, source, rejected, live, ordered, registered, next⟩ := spec
          refine ⟨skipped, chosen, rest, constraints, offset, source, rejected, live, ordered, ?_, ?_⟩
          · intro index cell found
            have old := registered index cell found
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp old).1]
            exact old
          · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp next).1]
            exact next

/-- Actual empty row storage starts with both origin lists empty. -/
theorem initial (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Invariant [] [] (SourceCurrentConjunctionRequirementRows.initial before) := by
  refine ⟨SourceCurrentConjunctionRequirementCellsRefinement.initial before, rfl, ?_⟩
  intro handle original spine found _
  cases handle <;> cases found

/-- Appending cell origins preserves spine claims when the actual spine list is unchanged. -/
theorem reframe {origins : List Cell} {sources : List (List Tuple)} {before after : Storage}
    (invariant : Invariant origins sources before) (added : List Cell)
    (refined : Refined (origins ++ added) after.requirements) (same : after.spines = before.spines) :
    Invariant (origins ++ added) sources after := by
  refine ⟨refined, invariant.length.trans (congrArg List.length same).symm, ?_⟩
  intro handle original spine sourceFound spineFound
  have old : lookupSpine handle before = some spine := by
    simpa only [lookupSpine, same] using spineFound
  have preserved := Spec.weaken (invariant.spines handle original spine sourceFound old) added []
  simpa only [List.append_nil] using preserved

/-- Changes to physical fields preserve the coupled invariant when both private lists are unchanged. -/
theorem same_cells_spines {origins : List Cell} {sources : List (List Tuple)} {before after : Storage}
    (invariant : Invariant origins sources before)
    (cells : after.requirements.cells = before.requirements.cells) (spines : after.spines = before.spines) :
    Invariant origins sources after := by
  have refined : Refined origins after.requirements := by
    refine ⟨invariant.cells.length.trans (congrArg List.length cells).symm, ?_⟩
    intro handle original current originFound currentFound
    apply invariant.cells.cells handle original current originFound
    simpa only [SourceCurrentConjunctionRequirementCells.lookup, cells] using currentFound
  have retained := reframe invariant [] (by simpa only [List.append_nil] using refined) spines
  simpa only [List.append_nil] using retained

/-- A raw-spine allocation appends that exact raw source at its stable returned handle. -/
theorem allocate_pending (tuples : List Tuple) (before : Storage) (origins : List Cell)
    (sources : List (List Tuple)) (invariant : Invariant origins sources before) :
    Invariant origins (sources ++ [tuples]) (allocateSpine (.pending tuples) before).2 := by
  refine ⟨invariant.cells, ?_, ?_⟩
  · simp only [allocateSpine, List.length_append, List.length_singleton, invariant.length]
  · intro handle original spine sourceFound spineFound
    by_cases old : handle < sources.length
    · have originalFound : sources[handle]? = some original := by
        simpa only [List.getElem?_append_left old] using sourceFound
      have inside : handle < before.spines.length := by simpa only [invariant.length] using old
      have prior : lookupSpine handle before = some spine := by
        change before.spines[handle]? = some spine
        change (before.spines ++ [.pending tuples])[handle]? = some spine at spineFound
        simpa only [List.getElem?_append_left inside] using spineFound
      have preserved := Spec.weaken (invariant.spines handle original spine originalFound prior) [] [tuples]
      simpa only [List.append_nil] using preserved
    · have inside := (List.getElem?_eq_some_iff.mp sourceFound).1
      have atEnd : handle = sources.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      subst handle
      have sourceSame : tuples = original := by simpa using sourceFound
      have present := lookupSpine_allocate (.pending tuples) before
      change lookupSpine before.spines.length (allocateSpine (.pending tuples) before).2 =
        some (.pending tuples) at present
      rw [← invariant.length] at present
      have spineSame : spine = .pending tuples := Option.some.inj (spineFound.symm.trans present)
      rw [spineSame]
      exact sourceSame

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Actual successful cell forcing preserves these same cell origins and spine sources. -/
theorem force_success {p h target : Nat} {before : Storage} {after : Cells} {nodes : List Node}
    {origins : List Cell} {sources : List (List Tuple)}
    (actual : SourceCurrentConjunctionRequirementCells.force p h target before.requirements = .done nodes after)
    (ready : Ready before.requirements.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before.requirements)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before.requirements)
    (invariant : Invariant origins sources before) :
    Invariant origins sources {before with requirements := after} := by
  refine ⟨SourceCurrentConjunctionRequirementCellsRefinement.force_success actual ready values closed invariant.cells,
    invariant.length, ?_⟩
  intro handle original spine sourceFound spineFound
  exact invariant.spines handle original spine sourceFound spineFound

end MicroCFTA.SourceCurrentConjunctionRequirementRowsSemantics
