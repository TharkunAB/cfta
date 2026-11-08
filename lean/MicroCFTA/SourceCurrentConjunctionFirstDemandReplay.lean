import MicroCFTA.SourceCurrentConjunctionFirstDemandResources

set_option autoImplicit false

/-!
The first-demand resource bound covers every actual read entry.
Each entry has an actual successful prefix from the original heap.
Compression bounds that prefix without changing its final heap.
The computed reader allowance therefore replays the original sequence,
including repeated operands, in its original order and with its full heap.
The allowance need not exceed the original successful read allowances.
-/
namespace MicroCFTA.SourceCurrentConjunctionFirstDemandReplay
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceEqualityProjectionRead (Read)
open SourceCurrentConjunctionCompletionReads (Exposures)
open SourceCurrentConjunctionExposureResources (forecast)
open SourceCurrentProjectionUnionResources (readFuel)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem snoc {earlier : List Node} {initial current next : State Symbol Guard}
    {prefixRows : List (List Edge)} {node : Node} {own : List Edge}
    (prefixActual : Exposures earlier initial prefixRows current) (actual : Read node current own next) :
    Exposures (earlier ++ [node]) initial (prefixRows ++ [own]) next := by
  induction prefixActual with
  | nil => exact .cons actual .nil
  | cons first rest ih => exact .cons first (ih actual)

private theorem replay_from (support : List Node) (resource : Nat) (initial : State Symbol Guard)
    (initialSemantic : SemanticReady initial) (initialCosts : CostHeap initial)
    (initialAvailable : Values initial support) (closed : ClosedValues support) (initialFits : Fits resource initial)
    {demands : List Node} {before after : State Symbol Guard} {rows : List (List Edge)}
    (actual : Exposures demands before rows after) :
    ∀ earlier prefixRows, Exposures earlier initial prefixRows before →
      (∀ node ∈ earlier, node ∈ support) → (∀ node ∈ demands, node ∈ support) →
      SemanticReady before → CostHeap before → Values before support →
      ∀ operations fuel, readFuel (forecast support.length resource) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel demands ⟨before, operations⟩ =
          .done rows ⟨after, operations⟩ := by
  induction actual with
  | nil => intros; rfl
  | @cons node before own middle demands more after first rest ih =>
      intro earlier prefixRows prefixActual prefixIncluded included semantic costs available operations fuel enough
      obtain ⟨_, _, _, _, _, _, currentFits, _, _, _⟩ :=
        SourceCurrentConjunctionFirstDemandResources.bounded prefixActual support prefixIncluded resource
          initialSemantic initialCosts initialAvailable closed initialFits
      have headAvailable := available node (included node List.mem_cons_self)
      have headClosed := closed node (included node List.mem_cons_self)
      have headReady := SourceCurrentProjectionUnionResources.read_ready first
        (forecast support.length resource) (forecast support.length resource)
        semantic headAvailable headClosed currentFits (Nat.le_refl _)
      have headDone := SourceCurrentProjectionNumericReplay.ReadReady.mono headReady enough
      have effect := SourceEqualityProjectionCosts.read_effects first semantic costs headAvailable
      have nextPrefix := snoc prefixActual first
      have nextIncluded : ∀ value ∈ earlier ++ [node], value ∈ support := by
        intro value member
        rcases List.mem_append.mp member with previous | added
        · exact prefixIncluded value previous
        · simpa only [List.mem_singleton.mp added] using included node List.mem_cons_self
      have later := ih (earlier ++ [node]) (prefixRows ++ [own]) nextPrefix nextIncluded
        (fun value member => included value (List.mem_cons_of_mem _ member))
        effect.2.1 effect.2.2.1
        (fun value member => effect.1.available value (available value member)) operations fuel enough
      simp only [SourceCurrentConjunctionRowsWorker.exposures, headDone, later,
        SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- The computed initial bound replays every original demand and its exact returned heap. -/
theorem original_replay {demands : List Node} {before after : State Symbol Guard} {rows : List (List Edge)}
    (actual : Exposures demands before rows after) (support : List Node)
    (included : ∀ node ∈ demands, node ∈ support) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before support) (closed : ClosedValues support) (fits : Fits resource before) :
    ∀ operations fuel, readFuel (forecast support.length resource) ≤ fuel →
      SourceCurrentConjunctionRowsWorker.exposures fuel demands ⟨before, operations⟩ =
        .done rows ⟨after, operations⟩ :=
  replay_from support resource before semantic costs available closed fits actual [] [] .nil
    (by intro node member; cases member) included semantic costs available

end MicroCFTA.SourceCurrentConjunctionFirstDemandReplay
