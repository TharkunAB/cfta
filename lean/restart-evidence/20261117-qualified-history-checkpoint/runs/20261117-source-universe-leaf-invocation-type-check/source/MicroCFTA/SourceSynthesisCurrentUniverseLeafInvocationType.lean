import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceSynthesisFiniteTypeWitnesses
import MicroCFTA.SourcePruningEnumerationSharedInvocationInversions

namespace MicroCFTA.SourceSynthesisCurrentUniverseLeafInvocationType
open Cache Language Fragments EnumerationState InternedConstructorTemplates
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
set_option autoImplicit false

/- Note [Source universe leaf typing at an actual invocation]
The original stored universe fixes the catalog and four rigid leaf rows.
A selected row with no children cannot be the distinguished arrow row.
The actual preparation therefore has no staged child inputs.
The same invocation trace returns the literal source leaf fragment.
Its filled term is finite Type syntax under every assignment.
This is a base case for causal Type-demand preservation.
It does not identify every later target with this fragment.
See Note [Indexed invocation ancestry] in
MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.
-/

private theorem output_origin {A B : Type} {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (aligned : All₂ R inputs outputs) : ∀ value ∈ outputs, ∃ input ∈ inputs, R input value := by
  induction aligned with
  | nil => intro value member; cases member
  | @cons first value rest values own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, own⟩
      · obtain ⟨input, present, related⟩ := ih selected later
        exact ⟨input, List.mem_cons_of_mem _ present, related⟩

private theorem descriptor_leaf_type (catalog : List (String × Nat)) (descriptor : String × Nat)
    (present : descriptor ∈ SourceSynthesisUniverseBody.descriptors catalog) (zero : descriptor.2 = 0) :
    TypeIn catalog (.node (literal descriptor.1) []) := by
  rcases descriptor with ⟨name, arity⟩
  dsimp only at zero
  subst arity
  rw [SourceSynthesisUniverseBody.descriptors, List.mem_append] at present
  rcases present with rigid | declared
  · have names := List.mem_map_of_mem (f := Prod.fst) rigid
    exact TypeIn.leaf name (by simpa only [List.map_cons, List.map_nil] using names)
  · exact TypeIn.node name [] declared (by intro child member; cases member)

private theorem prepared_leaf_staged
    (heap : InternedConstructorTemplates.State Symbol Constraint) (bucket : List Suspended)
    (edge : Edge) (before middle : Cached) (symbol : Symbol) (staged : List Input)
    (residual : Option Constraint) (leaf : edge.children = [])
    (actual : SourcePruningEnumerationCachedOwn.prepare heap bucket edge before =
      some [((symbol, staged, residual), middle)]) :
    symbol = edge.entry.key.symbol ∧ staged = [] := by
  unfold SourcePruningEnumerationCachedOwn.prepare at actual
  split at actual
  next allowed =>
    generalize projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = plan at actual
    cases plan with
    | none => cases actual
    | some plan =>
        rcases plan with ⟨tries, kept⟩
        dsimp only at actual
        generalize allocated : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = allocation at actual
        cases allocation with
        | none => cases actual
        | some allocation =>
            rcases allocation with ⟨own, ownAfter⟩
            have rowSame := (List.cons.inj (Option.some.inj actual)).1
            have symbolSame := congrArg (fun row : Row => row.1.1) rowSame
            have stagedSame := congrArg (fun row : Row => row.1.2.1) rowSame
            exact ⟨symbolSame.symm, by
              simpa only [leaf, List.zipIdx_nil, List.map_nil] using stagedSame.symm⟩
  next rejected => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem selected_leaf_fragment
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (bucket : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before finished : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat) (leaf : edge.children = [])
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume bucket edge caller before queries
      index output (.complete fragment reached saved finished) consumerIndex) :
    fragment = .node edge.entry.key.symbol [] := by
  obtain ⟨symbol, staged, residual, middle, fragments, afterChildren,
      prepared, children, assembled, _finishedEq⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf policy consume bucket edge caller before queries
      index output fragment reached saved finished consumerIndex trace
  obtain ⟨symbolSame, stagedEmpty⟩ := prepared_leaf_staged caller.checked.native.machine.heap
    bucket edge before middle symbol staged residual leaf prepared
  subst staged
  have fragmentsEmpty : fragments = [] := by
    cases children
    rfl
  simpa only [fragmentsEmpty, symbolSame] using assembled

theorem original_universe_leaf_selected_type
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (edge : Edge) (present : edge ∈ InternedEdgeResidency.nodeEdges body) (leaf : edge.children = [])
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (parentBucket : List Suspended) (caller reached : Caller width) (before finished : Cached)
    (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume parentBucket edge
      caller before queries index output (.complete fragment reached saved finished) consumerIndex) :
    fragment = .node edge.entry.key.symbol [] ∧
      ∀ assignment : Nat → Term Symbol,
        TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) (fill assignment fragment)
 := by
  have fragmentShape := selected_leaf_fragment checkEmpty r n p h k edgesOf policy consume
    parentBucket edge caller reached before finished queries saved index output fragment consumerIndex leaf trace
  have typed : TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query)
      (.node edge.entry.key.symbol []) := by
    obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, _markerRead, arrowChildren, _arrowKey,
        aligned, _markerClosed, _markerAvailable, _kinds, _arrowRetained⟩ :=
      SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    have retained : edge ∈ canonicalEdges (arrow :: rows) := by
      simpa only [bodyEq, InternedEdgeResidency.nodeEdges] using present
    have original := (List.mem_filter.mp (canonicalEdges_member _ edge retained)).1
    rcases List.mem_cons.mp original with same | later
    · subst edge
      rw [leaf] at arrowChildren
      cases arrowChildren
    · obtain ⟨descriptor, described, related⟩ := output_origin aligned edge later
      have zero : descriptor.2 = 0 := by
        have lengths := congrArg List.length related.1
        simpa only [leaf, List.length_nil, List.length_replicate] using lengths.symm
      have symbolSame : edge.entry.key.symbol = literal descriptor.1 :=
        congrArg EdgeKey.symbol related.2
      rw [symbolSame]
      exact descriptor_leaf_type (SourceSynthesisCurrentContext.constructorCatalog lib query) descriptor described zero
  refine ⟨fragmentShape, ?_⟩
  intro assignment
  rw [fragmentShape]
  simpa only [fill, List.map_nil] using typed

end MicroCFTA.SourceSynthesisCurrentUniverseLeafInvocationType

#check @MicroCFTA.SourceSynthesisCurrentUniverseLeafInvocationType.original_universe_leaf_selected_type
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseLeafInvocationType.original_universe_leaf_selected_type
