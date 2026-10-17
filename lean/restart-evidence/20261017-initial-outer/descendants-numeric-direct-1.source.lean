import MicroCFTA.SourceCurrentInheritedNumeric
import MicroCFTA.SourceCurrentRawRebuildNumeric
import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Initial numeric completion of terminal outer descendants

An initial inherited combination that returns contradiction erases all
child slots. An edge with no children uses an empty live walk instead.
Both branches construct their own prefix and raw reconstruction. They
retain the same inventory and need no recursive child call or Room.
-/
namespace MicroCFTA.SourceCurrentDescendantsNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads (DescendantsReads ChildrenReads WalkReads)
open SourceCurrentAllocatedPartialChecks (Checks descendantsTrace childrenTrace)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "constructorProfile" => SourceCurrentRawRebuildNumeric.constructorProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}

private theorem terminal_children_checks {combined : EqValue} {values results : List Node}
    {before after : Caller width} (actual : Children budget combined values before results after)
    (terminal : combined = .contradiction ∨ values = []) : Checks (childrenTrace actual) := by
  cases actual with
  | contradiction =>
      intro request first result last body reached
      cases reached with
      | step first rest => cases first
  | live walk =>
      rcases terminal with impossible | empty
      · cases impossible
      · subst values
        cases walk
        intro request first result last body reached
        cases reached with
        | step first rest =>
            cases first with
            | children_walk =>
                cases rest with
                | step first tail => cases first

private theorem terminal_checks {inherited combined : EqValue} {edge result : Edge}
    {before middle after : Caller width} {results : List Node}
    (combinedDone : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some combined))
    (children : Children budget combined edge.children (prefixState before edge inherited) results middle)
    (terminal : combined = .contradiction ∨ edge.children = [])
    (sameResult : result = (rawEdge edge results middle.checked).1)
    (sameAfter : after = advance middle (rawEdge edge results middle.checked).2 middle.fourth middle.merge) :
    Checks (descendantsTrace (Descendants.run combinedDone children)) := by
  have childChecks := terminal_children_checks children terminal
  intro request first output last body reached
  cases reached with
  | step first rest =>
      cases first with
      | descendants_children => exact childChecks request _ output _ body rest

private theorem terminal_children_run {combined : EqValue} {values results : List Node}
    {before : Caller width} (actual : Children budget combined values before results before)
    (terminal : combined = .contradiction ∨ values = []) (f g s r e p h m c n : Nat) :
    SourceCurrentAllocatedPartialWorker.children f g s r e p h m c n budget combined values before = .done results before := by
  cases actual with
  | contradiction => rfl
  | live walk =>
      rcases terminal with impossible | empty
      · cases impossible
      · subst values
        cases walk
        rfl

/-- A terminal descendants call retains its exact graph, resources, and guarded language law. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (inherited : EqValue) (edge : Edge)
    (before : Caller width) (memos : Memos) (result : Edge) (after : Caller width) : Prop where
  /-- The own prefix and terminal child branch determine the actual result. -/
  actual : Descendants budget inherited edge before result after
  /-- No terminal child branch invokes a global query. -/
  reads : DescendantsReads formulas solver actual memos memos
  /-- No edge body is reached from this terminal graph. -/
  checks : Checks (descendantsTrace actual)
  /-- The full caller retains the same inventory and global memo bundle. -/
  post : Post formulas solver inventory before after memos
  /-- The literal raw constructor returns a resident edge. -/
  resident : EdgeResident after.checked.native.machine.heap result
  /-- The returned checked state retains the same query Frame. -/
  frame : Frame formulas solver inventory after.checked
  /-- One constructor profile bounds the original slot count. -/
  fits : Fits (constructorProfile edge.children.length profile) after.checked
  /-- The result satisfies the existing inherited outer edge law. -/
  law : EdgeLaw formulas solver ⟨inherited, edge⟩ result
  /-- All ten worker fuels are arbitrary, including zero. -/
  run : ∀ f g s r e p h m c n,
    SourceCurrentAllocatedPartialWorker.descendants f g s r e p h m c n budget inherited edge before = .done result after

/-- Initial prefix contradiction or an empty child list constructs the complete descendants call. -/
theorem terminal_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (inherited : EqValue) (edge : Edge) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (terminal : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some .contradiction) ∨ edge.children = []) :
    ∃ result after, Receipt formulas solver inventory profile budget inherited edge before memos result after := by
  obtain ⟨combined, prefixReceipt, firstFrame, firstFits, firstPost⟩ :=
    SourceCurrentInheritedNumeric.resident_complete formulas solver inventory edge inherited before memos initial frame profile fits
      (fun _ => resident) (fun _ => inheritedReady)
  have terminal : combined = .contradiction ∨ edge.children = [] := by
    rcases terminal with contradiction | empty
    · have same := prefixReceipt.actual.symm.trans contradiction
      exact Or.inl (by cases same; rfl)
    · exact Or.inr empty
  have branch : ∃ results, ∃ children : Children budget combined edge.children (prefixState before edge inherited) results
        (prefixState before edge inherited),
      ChildrenReads formulas solver children memos memos ∧
      Values (prefixState before edge inherited).checked.native.machine.heap results := by
    cases combined with
    | contradiction =>
        refine ⟨EqualityLeafProjectionRuntimeEmpty.erase edge.children, .contradiction, .contradiction, ?_⟩
        intro value member
        obtain ⟨original, _, same⟩ := List.mem_map.mp member
        subst value
        exact empty_available _
    | live identity records =>
        have empty : edge.children = [] := terminal.resolve_left (by intro impossible; cases impossible)
        subst empty
        exact ⟨[], .live .nil, .live .nil, by intro value member; cases member⟩
  obtain ⟨results, children, childReads, available⟩ := branch
  have same := children.length
  have kept := InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth edge resident
  have rebuilt := SourceCurrentRawRebuildNumeric.edge formulas solver inventory edge results
    (prefixState before edge inherited).checked firstFrame profile firstFits kept available same
  have last := (SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver inventory (prefixState before edge inherited)
    memos firstPost.context edge results kept available same).2
  let actual : Descendants budget inherited edge before (rawEdge edge results (prefixState before edge inherited).checked).1
      (advance (prefixState before edge inherited) (rawEdge edge results (prefixState before edge inherited).checked).2
        (prefixState before edge inherited).fourth (prefixState before edge inherited).merge) := .run prefixReceipt.actual children
  have reads : DescendantsReads formulas solver actual memos memos := .run childReads
  have checks : Checks (descendantsTrace actual) := terminal_checks prefixReceipt.actual children terminal rfl rfl
  obtain ⟨next, post, output, law⟩ :=
    SourceCurrentAllocatedPartialActual.descendants formulas solver reads inventory checks initial inheritedReady resident
  refine ⟨_, _, actual, reads, checks, firstPost.trans last, rebuilt.1.resident, rebuilt.2.1, ?_, law, ?_⟩
  · simpa only [same] using rebuilt.2.2.1
  · intro f g s r e p h m c n
    have done := terminal_children_run children terminal f g s r e p h m c n
    simpa only [SourceCurrentAllocatedPartialWorker.descendants, prefixReceipt.actual,
      SourceCurrentAllocatedPartialGraph.prefixState, SourceCurrentAllocatedInheritedPrefix.state,
      SourceCurrentAllocatedPartialWorker.Outcome.bind] using done

end MicroCFTA.SourceCurrentDescendantsNumeric
