import MicroCFTA.SourceSynthesisProgramRolesCompression
import MicroCFTA.SourceSynthesisNoPendingProgramSlot
import MicroCFTA.SourceSynthesisProgramTermSize
import MicroCFTA.SourcePruningEnumerationPartialOutput
import MicroCFTA.SourcePruningPositions

/-!
# Program projection of the actual partial root

Finished selection excludes pending marked Program slots.
The actual ordered readback retains the marked fragment layouts.
Opaque Type subtrees need no completion. The same compression endpoint is retained.
The complete driver must still establish the supplied Program-slot invariant.
-/
namespace MicroCFTA.SourceSynthesisProgramRoleReadback
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame EnumerationObservations EnumerationUntil
open SourceSynthesisProgramEnumerationRoles (FragmentRoles SlotRole ProgramSlots)
open SourceSynthesisProgramRolesCompression (compression_frame_program_slots)
open SourceSynthesisProgramTermSize (Program Projection)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "PartialTerm" => SourcePruningTemplates.PartialTerm
attribute [local instance] EnumerationObservations.partialTransportMonadList
  EnumerationObservations.partialTransportLawfulMonadList

private def EnumeratedSlots (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (marked : Nat → Prop) (state : Core) : Prop :=
  ProgramSlots valid literal heap state marked ∧
    ∀ uv, marked uv → ∃ fragment,
      state.values[uv]? = some (.enumerated fragment) ∧ FragmentRoles literal marked fragment

section Readback
variable {valid : Constraint → Prop} {literal : String → Symbol}
    {heap : NativeHeap} {marked : Nat → Prop}

private theorem frame_slots (before after : Core) (frame : Frame before after)
    (slots : EnumeratedSlots valid literal heap marked before) :
    EnumeratedSlots valid literal heap marked after := by
  refine ⟨compression_frame_program_slots heap before after marked frame slots.1, ?_⟩
  intro uv known
  obtain ⟨fragment, stored, fragmentRoles⟩ := slots.2 uv known
  refine ⟨fragment, ?_, fragmentRoles⟩
  rw [frame.values]
  exact stored

private theorem marked_read (fuel uv : Nat) (before after : Core) (value : UVarValue Symbol)
    (total : UnionFind.Total before.representatives)
    (slots : EnumeratedSlots valid literal heap marked before) (known : marked uv)
    (actual : Success (getValue fuel uv) before value after) :
    ∃ fragment, value = .enumerated fragment ∧ FragmentRoles literal marked fragment := by
  obtain ⟨fragment, original, fragmentRoles⟩ := slots.2 uv known
  obtain ⟨_frame, actualRoot, _size, path, _afterPath, stored⟩ :=
    getValue_frame fuel uv before after value total actual
  obtain ⟨_selfSize, selfPath⟩ := slots.1.roots uv known
  have rootSame : actualRoot = uv := (UnionFind.reaches_unique path selfPath).1
  subst actualRoot
  exact ⟨fragment, Option.some.inj (stored.symm.trans original), fragmentRoles⟩

private theorem node_outputs (graph : Graph Symbol Constraint) (fuel : Nat)
    (recurse : ∀ (fragment : Fragment Symbol) (before after : Core) (partialTerm : PartialTerm),
      UnionFind.Total before.representatives → EnumeratedSlots valid literal heap marked before →
      FragmentRoles literal marked fragment →
      Success (EnumerationState.expandPartial graph fuel fragment) before partialTerm after →
      ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true partialTerm) program)
    (symbol : Symbol) (children : List (Fragment Symbol))
    (before after : Core) (partialTerm : PartialTerm)
    (total : UnionFind.Total before.representatives)
    (slots : EnumeratedSlots valid literal heap marked before)
    (actual : Success (EnumerationState.expandPartial graph (fuel + 1) (.node symbol children))
      before partialTerm after) :
    ∃ partials, partialTerm = .node (.concrete symbol) partials ∧
      All₂ (fun child output => FragmentRoles literal marked child →
        ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true output) program)
        children partials := by
  change Success (children.mapM (EnumerationState.expandPartial graph fuel) >>= fun terms =>
    pure (.node (.concrete symbol) terms)) before partialTerm after at actual
  obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp actual
  obtain ⟨rfl, _afterSame⟩ := (success_pure _ _ _ _).mp final
  have step : ∀ (child : Fragment Symbol) (previous : Core) (output : PartialTerm) (next : Core),
      Frame before previous →
      Success (EnumerationState.expandPartial graph fuel child) previous output next →
      Frame before next ∧ (FragmentRoles literal marked child →
        ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true output) program) := by
    intro child previous output next earlierFrame childRead
    have currentTotal := earlierFrame.total total
    refine ⟨earlierFrame.trans (expandPartial_frame graph fuel child previous next output currentTotal childRead), ?_⟩
    intro childRoles
    exact recurse child previous next output currentTotal
      (frame_slots before previous earlierFrame slots) childRoles childRead
  have related := (mapM_sound (EnumerationState.expandPartial graph fuel) (Frame before)
    (fun child output => FragmentRoles literal marked child →
      ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true output) program)
    step children before middle terms (Frame.refl before) traversed).2
  exact ⟨terms, rfl, related⟩

private theorem expand_projected (graph : Graph Symbol Constraint) (fuel : Nat) :
    ∀ (fragment : Fragment Symbol) (before after : Core) (partialTerm : PartialTerm),
      UnionFind.Total before.representatives → EnumeratedSlots valid literal heap marked before →
      FragmentRoles literal marked fragment →
      Success (EnumerationState.expandPartial graph fuel fragment) before partialTerm after →
      ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true partialTerm) program := by
  induction fuel with
  | zero =>
      intro fragment before after partialTerm _total _slots _roles actual
      exact (success_failure .fuelExhausted before after partialTerm actual).elim
  | succ fuel ih =>
      intro fragment before after partialTerm total slots roles actual
      cases roles with
      | hole uv known =>
          rw [EnumerationState.expandPartial] at actual
          obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
          obtain ⟨stored, rfl, storedRoles⟩ := marked_read (fuel + 1) uv before middle value total slots known reading
          have frame := (getValue_frame (fuel + 1) uv before middle (.enumerated stored) total reading).1
          exact ih stored middle after partialTerm (frame.total total)
            (frame_slots before middle frame slots) storedRoles continued
      | component symbol annotation =>
          obtain ⟨partials, rfl, related⟩ :=
            node_outputs graph fuel ih symbol [annotation] before after partialTerm total slots actual
          cases related with
          | cons _ tail =>
              cases tail
              refine ⟨.var (Prod.fst symbol), ?_⟩
              rw [SourcePruningPositions.openProgram_type_node]
              exact .component symbol _
      | application annotation marker function argument first second =>
          obtain ⟨partials, rfl, related⟩ := node_outputs graph fuel ih (literal "app")
            [annotation, marker, function, argument] before after partialTerm total slots actual
          cases related with
          | cons _ rest =>
              cases rest with
              | cons _ rest =>
                  cases rest with
                  | cons firstRelated rest =>
                      cases rest with
                      | cons secondRelated tail =>
                          cases tail
                          obtain ⟨firstProgram, firstProjected⟩ := firstRelated first
                          obtain ⟨secondProgram, secondProjected⟩ := secondRelated second
                          refine ⟨.app firstProgram secondProgram, ?_⟩
                          rw [SourcePruningPositions.openProgram_type_node]
                          exact .application _ _ firstProjected secondProjected
      | filter goal candidates body =>
          obtain ⟨partials, rfl, related⟩ := node_outputs graph fuel ih (literal "filter")
            [goal, candidates] before after partialTerm total slots actual
          cases related with
          | cons _ rest =>
              cases rest with
              | cons bodyRelated tail =>
                  cases tail
                  obtain ⟨program, projected⟩ := bodyRelated body
                  refine ⟨program, ?_⟩
                  rw [SourcePruningPositions.openProgram_type_node]
                  exact .filter _ projected
end Readback

variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width}
    {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    {valid : Constraint → Prop} {literal : String → Symbol}

/-- The same actual finished partial root retains a Program projection and complete frame. -/
theorem root_partial_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after := by
  have slots : EnumeratedSlots valid literal caller.checked.native.machine.heap marked before.core := by
    refine ⟨roles, ?_⟩
    intro uv known
    obtain ⟨payload, stored, payloadRoles⟩ := roles.stored uv known
    cases payloadRoles with
    | pending handle scs value decoded fields _validTries _annotationPaths =>
        exact (SourceSynthesisNoPendingProgramSlot.no_pending_program_slot
          packet finished uv handle scs value stored decoded fields).elim
    | enumerated fragment fragmentRoles => exact ⟨fragment, stored, fragmentRoles⟩
  unfold SourcePruningEnumerationPartialOutput.rootPartial at actual
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before.core middle fragment).mp rootRead
  obtain ⟨storedRoot, rfl, rootRoles⟩ :=
    marked_read (fuel + 1) 0 before.core middle value packet.safe.1.total slots root reading
  have fragmentSame : fragment = storedRoot := projected
  subst fragment
  have frame := (getValue_frame (fuel + 1) 0 before.core middle
    (.enumerated storedRoot) packet.safe.1.total reading).1
  unfold SourcePruningEnumerationPartialOutput.expandPartial at rendered
  obtain ⟨program, projectedProgram⟩ := expand_projected _ fuel storedRoot middle after actualPartial
    (frame.total packet.safe.1.total) (frame_slots before.core middle frame slots) rootRoles rendered
  exact ⟨program, projectedProgram,
    frame.trans (expandPartial_frame _ fuel storedRoot middle after actualPartial
      (frame.total packet.safe.1.total) rendered)⟩

end MicroCFTA.SourceSynthesisProgramRoleReadback
