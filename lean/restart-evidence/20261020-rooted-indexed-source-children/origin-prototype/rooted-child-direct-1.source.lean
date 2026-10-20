import MicroCFTA.SourceCurrentIndexedRowCallChildren
import MicroCFTA.InternedFreshOrdinarySourceHistory

/-!
# Rooted actual source children and explicit stops

The same source row supplies an indexed child call or an exact capture
or stored-winner stop. Actual source-union prefixes retain the original
rooted route at the selected entry. All source sizes use original syntax.
-/
namespace MicroCFTA.SourceCurrentRootedRowChildOrigins
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome request finish)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback buildMany_verified)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)

/-- The selected source child is actual, or it stops at an exact capture or selected stored body. -/
inductive Origin [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (original : Syntax Symbol Guard) (parentRow : EdgeValue Symbol Guard)
    (childIndex : Nat) (child : Value Symbol Guard) : Prop where
  /-- An original node row supplies the complete selected source-child interval and rooted entry. -/
  | node {expressions inputs before raw after rows middle symbol guard children sourceIndex outputIndex}
      (built : buildEdges expressions inputs before = .done rows middle)
      (made : run (makeNode rows) middle = (raw,after))
      (canonical : (nodeEdges raw)[outputIndex]? = some parentRow)
      (call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children)
      (same : call.output = parentRow)
      (childSyntax : Syntax Symbol Guard) (current next : State Symbol Guard)
      (source : children[childIndex]? = some childSyntax)
      (value : call.values[childIndex]? = some child)
      (prefix : buildMany (children.take childIndex) inputs call.current =
        .done (call.values.take childIndex) current)
      (context : Context current inputs)
      (called : build childSyntax inputs current = .done child next)
      (suffix : buildMany (children.drop (childIndex + 1)) inputs next =
        .done (call.values.drop (childIndex + 1)) call.middle)
      (growth : Grows before current)
      (issued : Extends before.nodes.issued current.nodes.issued)
      (reached : Reached root initial childSyntax inputs current)
      (smaller : sizeOf childSyntax < sizeOf original) :
      Origin root initial original parentRow childIndex child
  /-- A variable stops at its exact captured value and rooted call. -/
  | capture {inputs state value slot}
      (selected : inputs[slot]? = some value)
      (inside : RowAt value parentRow)
      (childSelected : parentRow.children[childIndex]? = some child)
      (reached : Reached root initial (.var slot) inputs state) :
      Origin root initial original parentRow childIndex child
  /-- A binder stops at its exact selected complete payload and current request. -/
  | binder {smart expression inputs before raw after depth afterDepth ordinary cut entry body}
      (depthDone : callback expression inputs .depth before = .done depth afterDepth)
      (ordinaryDone : callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth =
        .done ordinary cut)
      (requested : request smart depth ordinary (callback expression inputs) cut = .done raw after)
      (selected : after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary))
      (returned : raw = finish smart (.mu entry body depth ordinary))
      (inside : RowAt body parentRow)
      (childSelected : parentRow.children[childIndex]? = some child)
      (reached : Reached root initial (.binder smart expression) inputs before) :
      Origin root initial original parentRow childIndex child

/-- The same source row derives an actual rooted child call or an exact capture or binder stop. -/
theorem from_source_row [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {parentRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached root initial expression inputs before)
    (source : SourceRow expression inputs before raw after parentRow)
    (childIndex : Nat) (child : Value Symbol Guard)
    (selected : parentRow.children[childIndex]? = some child) :
    Origin root initial expression parentRow childIndex child := by
  have descend {currentExpression : Syntax Symbol Guard} {currentInputs : List (Value Symbol Guard)}
      {start : State Symbol Guard} {value : Value Symbol Guard} {stop : State Symbol Guard}
      {row : EdgeValue Symbol Guard}
      (part : SourceRow currentExpression currentInputs start value stop row) :
      Context start currentInputs → Reached root initial currentExpression currentInputs start →
      sizeOf currentExpression ≤ sizeOf expression →
      row.children[childIndex]? = some child →
      Origin root initial expression row childIndex child := by
    induction part with
    | @capture currentInputs state value row slot found inside =>
      intro _ currentReached _ childFound
      exact .capture found inside childFound currentReached
    | @node expressions currentInputs start value stop rows middle symbol guard children row
        sourceIndex outputIndex built made canonical call same =>
      intro currentContext currentReached bound childFound
      have actualSelected : call.output.children[childIndex]? = some child := by
        rw [same]
        exact childFound
      obtain ⟨childSyntax,current,next,syntaxSelected,valueSelected,prefix,childContext,
        called,suffix,growth,issued,small⟩ :=
        SourceCurrentIndexedRowCallChildren.indexed_child expressions currentInputs start rows middle stop
          currentContext sourceIndex symbol guard children call childIndex child actualSelected
      have childReached : Reached root initial childSyntax currentInputs current :=
        (currentReached.node (List.mem_of_getElem? call.source) (List.mem_of_getElem? syntaxSelected)).grows growth
      exact .node built made canonical call same childSyntax current next syntaxSelected valueSelected
        prefix childContext called suffix growth issued childReached (Nat.lt_of_lt_of_le small bound)
    | @union expressions currentInputs start value stop values middle member memberValue current next row
        index built made syntaxSelected valueSelected prefix memberContext called suffix nested ih =>
      intro currentContext currentReached bound childFound
      have checked := buildMany_verified (expressions.take index) currentInputs start
        currentContext.base.normal.facts currentContext.base.inputs
      have growth : Grows start current := by
        simpa only [prefix,Outcome.state] using checked.growth
      have memberReached : Reached root initial member currentInputs current :=
        (currentReached.union (List.mem_of_getElem? syntaxSelected)).grows growth
      have smaller : sizeOf member < sizeOf (Syntax.union expressions) := by
        have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxSelected)
        simp only [Syntax.union.sizeOf_spec]
        omega
      exact ih memberContext memberReached (Nat.le_trans (Nat.le_of_lt smaller) bound) childFound
    | @binder smart body currentInputs start value stop depth afterDepth ordinary cut entry stored row
        depthDone ordinaryDone requested present returned inside =>
      intro _ currentReached _ childFound
      exact .binder depthDone ordinaryDone requested present returned inside childFound currentReached
  exact descend source context reached (Nat.le_refl _) selected

end MicroCFTA.SourceCurrentRootedRowChildOrigins
