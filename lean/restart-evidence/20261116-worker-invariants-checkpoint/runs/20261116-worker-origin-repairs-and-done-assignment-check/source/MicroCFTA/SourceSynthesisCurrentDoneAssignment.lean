import MicroCFTA.SourceSynthesisCurrentDonePendingTypes
import MicroCFTA.EnumerationPendingDomainAssignment
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-!
# One current assignment at a source done endpoint

The original accepted source supplies one concrete finite Type witness.
The packet supplies current safety, ordering and native normality.
The remaining endpoint origin and bucket invariants stay explicit.
This result does not include residuals, historical obligations or root acceptance.
-/
namespace MicroCFTA.SourceSynthesisCurrentDoneAssignment
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourcePruningEnumerationNodes (lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false
variable {Typing : Type} {width : Nat}

/-- Actual done slot invariants construct one assignment for current native domains and equations. -/
theorem done_current_assignment
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      InternedNestedConstruction.Outcome.done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (caller : SourceCurrentAllocatedPartialState.State width) (memos : EndpointMemoGateTrace.Memos)
    (before : EnumerationExpandableIndex.Cached Symbol Guard)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (done : SourcePruningEnumerationRestart.decision none order metadata before = some .done)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal caller.checked.native.machine.heap)
    (growth : Grows sourceHeap caller.checked.native.machine.heap)
    (onlyU : ∀ (slot handle : Nat) (scs : List EnumerationState.Suspended),
      before.core.values[slot]? = some (.unenumerated (some handle) scs) →
      ∀ value, lookupNode caller.checked.native.machine.heap handle = some value →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)
    (noneBuckets : ∀ (slot : Nat) (scs : List EnumerationState.Suspended),
      before.core.values[slot]? = some (.unenumerated none scs) → scs = []) :
    ∃ assignment : Nat → Term Symbol,
      Fragments.stateSatisfies before.core.representatives
        (EnumerationCorrectness.heap
          (handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          before.core.values) assignment ∧
      ∀ (slot : Nat) (node : Option Nat) (scs : List EnumerationState.Suspended),
        before.core.values[slot]? = some (.unenumerated node scs) →
        assignment slot = .node (literal "var1") []
 := by
  have normal := packet.context.ready.semantic.ready.semantic.1.normal
  have members := SourceSynthesisCurrentDonePendingTypes.done_pending_type_members
    formulas solver ambient lib query signed whole accepted rootValue sourceHeap built
    key entry body depth ordinary stored order metadata caller before packet.valid done
    normal irreducible growth onlyU
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  apply EnumerationPendingAssignment.stratified_pending_assignment before.core packet.safe
    level frontier ordered (.node (literal "var1") [])
    (handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
  intro slot node scs atSlot
  cases node with
  | none =>
      refine ⟨noneBuckets slot scs atSlot, ?_⟩
      intro handle impossible
      cases impossible
  | some handle =>
      obtain ⟨emptyBucket, admitted⟩ := members slot handle scs atSlot
      refine ⟨emptyBucket, ?_⟩
      intro other same
      have identity : handle = other := Option.some.inj same
      subst other
      exact admitted _ (.leaf "var1" (by decide))

end MicroCFTA.SourceSynthesisCurrentDoneAssignment

#check MicroCFTA.SourceSynthesisCurrentDoneAssignment.done_current_assignment
#print axioms MicroCFTA.SourceSynthesisCurrentDoneAssignment.done_current_assignment
