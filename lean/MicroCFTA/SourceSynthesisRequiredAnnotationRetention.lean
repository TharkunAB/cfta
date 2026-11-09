import MicroCFTA.SourceEqualityRequiredPathShape
import MicroCFTA.SourceCurrentSharedRequiredPathShape
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationSharedChildStableNeutral

/-!
# Retention at an actual required Type annotation

A selected required path continues below child zero of a Program operand.
The literal requireAll result therefore has an ordinary annotation there.
The actual successful shared annotation-child row retains its full bucket.
The path membership and current constructor inputs remain explicit.
Later native edits need a separate preservation result.
-/
namespace MicroCFTA.SourceSynthesisRequiredAnnotationRetention
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded SourceEqualityRequiredPathShape
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error
  (Fragment × EnumerationState.State Symbol Constraint))
variable {width : Nat}

private theorem demanded_child {entries : List (Int × Needed)} {index : Int} {suffix : Path}
    (demand : demands (.node entries) (index :: suffix) = true) :
    ∃ child, SourceEqualityNeededMap.lookup index entries = some child ∧ demands child suffix = true := by
  cases found : SourceEqualityNeededMap.lookup index entries with
  | none => simp only [demands, found, Bool.false_eq_true] at demand
  | some child => exact ⟨child, rfl, by simpa only [demands, found] using demand⟩

/-- A source path below an annotation compiles to its nonempty required child map. -/
theorem required_annotation_route (paths : List Path) (index : Nat) (descendant : Int) (tail : Path)
    (included : (index :: 0 :: descendant :: tail : Path) ∈ paths) :
    ∃ roots operands annotations : List (Int × Needed),
      build paths = .node roots ∧
      SourceEqualityNeededMap.lookup (index : Int) roots = some (.node operands) ∧
      SourceEqualityNeededMap.lookup 0 operands = some (.node annotations) ∧ annotations ≠ [] := by
  have demand : demands (build paths) (index :: 0 :: descendant :: tail : Path) = true :=
    (demands_build paths _).mpr (Or.inr ⟨_, included, List.prefix_refl _⟩)
  cases compiled : build paths with
  | node roots =>
      rw [compiled] at demand
      obtain ⟨operand, operandStored, operandDemand⟩ := demanded_child demand
      cases operand with
      | node operands =>
          obtain ⟨annotation, annotationStored, annotationDemand⟩ := demanded_child operandDemand
          cases annotation with
          | node annotations =>
              refine ⟨roots, operands, annotations, rfl, operandStored, annotationStored, ?_⟩
              intro empty
              have impossible : (false : Bool) = true := by
                simpa only [empty, demands, SourceEqualityNeededMap.lookup] using annotationDemand
              cases impossible

section Required
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The literal successful required result exposes the selected annotation as ordinary. -/
theorem required_annotation_ordinary
    {fuel readFuel index : Nat} {paths : List Path} {descendant : Int} {tail : Path}
    {values results : List Node} {before after : InternedConstructorTemplates.State Symbol Constraint}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Constraint)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {edge : EdgeValue Symbol Constraint} {annotation : Node}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (ready : SourceEqualityRequiredCache.Ready before) (available : Values before values)
    (closed : ClosedValues values)
    (included : (index :: 0 :: descendant :: tail : Path) ∈ paths)
    (operand : results[index]? = some (.node entry rows depth free))
    (selected : edge ∈ rows) (stored : edge.children[0]? = some annotation) :
    SourceEqualityRequiredCache.Ordinary annotation := by
  obtain ⟨roots, operands, annotations, compiled, operandStored, annotationStored, nonempty⟩ :=
    required_annotation_route paths index descendant tail included
  have shape := requireAll_shape actual ready available closed
  rw [compiled] at shape
  have operandShape : PrefixShape (.node operands) (.node entry rows depth free) :=
    shape index _ _ operand (by simpa only [Nat.zero_add] using operandStored)
  exact (operandShape.child selected stored annotationStored).ordinary nonempty

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem child_input_stored {edge : EdgeValue Symbol Constraint}
    {scs bucket : List Suspended} {start index : Nat} {tries : List EqualityTrie.Trie} {incoming : Node}
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket)) : edge.children[index]? = some incoming := by
  rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at input
  obtain ⟨indexed, indexedStored, pairSame⟩ := Option.map_eq_some_iff.mp input
  rw [List.getElem?_zipIdx] at indexedStored
  obtain ⟨child, childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
  have same : child = incoming := congrArg Prod.fst pairSame
  exact same ▸ childStored

variable [DecidableEq Symbol] [DecidableEq Node]

/-- The same current shared preparation exposes a selected required annotation. -/
theorem shared_preparation_annotation_ordinary
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory entryInventory profile budget records values before memos outcome kept results after saved final}
    {index : Nat} {descendant : Int} {tail : Path}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Constraint)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {edge : EdgeValue Symbol Constraint} {annotation : Node}
    (receipt : SourceCurrentSharedScanRequiredNumeric.Receipt (width := width)
      formulas solver inventory profile budget records values before memos outcome kept results after saved final)
    (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver entryInventory before memos)
    (available : Values before.checked.native.machine.heap values) (closed : ClosedValues values)
    (included : (index :: 0 :: descendant :: tail : Path) ∈
      SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths))
    (operand : results[index]? = some (.node entry rows depth free))
    (selected : edge ∈ rows) (stored : edge.children[0]? = some annotation) :
    SourceEqualityRequiredCache.Ordinary annotation := by
  obtain ⟨roots, operands, annotations, compiled, operandStored, annotationStored, nonempty⟩ :=
    required_annotation_route _ index descendant tail included
  have shape := SourceCurrentSharedRequiredPathShape.receipt_shape receipt initial available closed
  rw [compiled] at shape
  have operandShape : PrefixShape (.node operands) (.node entry rows depth free) :=
    shape index _ _ operand (by simpa only [Nat.zero_add] using operandStored)
  exact (operandShape.child selected stored annotationStored).ordinary nonempty

/-- An actual successful shared annotation child retains all inherited and own restrictions. -/
theorem required_annotation_retained
    {fuel readFuel index : Nat} {paths : List Path} {descendant : Int} {tail : Path}
    {values results : List Node} {beforeHeap : InternedConstructorTemplates.State Symbol Constraint}
    {beforeCaller afterCaller : Caller width}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Constraint)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {scs bucket : List Suspended} {start : Nat} {tries : List EqualityTrie.Trie} {incoming : Node}
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values beforeHeap =
      .done results beforeCaller.checked.native.machine.heap)
    (ready : SourceEqualityRequiredCache.Ready beforeHeap) (available : Values beforeHeap values)
    (closed : ClosedValues values)
    (included : (index :: 0 :: descendant :: tail : Path) ∈ paths)
    (operand : results[index]? = some (.node entry rows depth free)) (selected : edge ∈ rows)
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[0]? = some (incoming, bucket))
    {checkEmpty : Bool} {r n p h k : Nat}
    {before : Cached} {queries savedQueries : Queries} {raw : Raw}
    {outer : EnumerationState.State Symbol Constraint} {waiting : EnumerationWaitingIndex.Waiting}
    {cached : Option Cached} {fragment : Fragment} {output : EnumerationState.State Symbol Constraint}
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming beforeCaller before queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), cached))
    (member : Except.ok (fragment, output) ∈ raw) :
    (match incoming with | .node _ _ _ _ => True | _ => False) ∧
      (match incoming with
        | .node _ _ _ _ => bucket
        | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) = bucket := by
  have ordinary := required_annotation_ordinary required ready available closed included operand selected
    (child_input_stored input)
  have nonempty : incoming ≠ .empty := by
    intro empty
    have projected := congrArg (fun observation => observation.1.1) actual
    have rawSame : [] = raw := by
      simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
        ite_eq_left empty, Except.ok.injEq, Option.some.injEq] using projected
    rw [← rawSame] at member
    cases member
  cases incoming with
  | empty => exact (nonempty rfl).elim
  | node => exact ⟨True.intro, rfl⟩
  | reference | union | mu => cases ordinary
end Required
end MicroCFTA.SourceSynthesisRequiredAnnotationRetention
