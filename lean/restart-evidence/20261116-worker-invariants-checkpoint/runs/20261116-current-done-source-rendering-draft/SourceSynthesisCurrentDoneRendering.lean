import MicroCFTA.SourceSynthesisCurrentDonePendingTypes
import MicroCFTA.SourcePruningEnumerationPendingRendering
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-!
# One current assignment from actual source rendering

The original accepted source supplies one concrete finite Type witness.
The packet supplies current safety, ordering and native normality.
The remaining endpoint origin and bucket invariants stay explicit.
Historical obligations and original-root acceptance remain separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentDoneRendering
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

/-- Actual done rendering and checked residuals construct one current source assignment. -/
theorem rendered_current_assignment
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
      before.core.values[slot]? = some (.unenumerated none scs) → scs = [])
    (fuel uv : Nat) (after : EnumerationState.State Symbol Guard) (term : Term Symbol)
    (pending : List (Guard × Term Symbol))
    (observed : EnumerationCorrectness.Success
      (SourcePruningEnumerationRendering.render caller.checked.native.machine.heap (literal "var1") fuel uv)
      before.core (term, pending) after)
    (checked : ∀ obligation ∈ pending,
      SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) :
    ∃ assignment : Nat → Term Symbol,
      EnumerationCorrectness.Satisfies
        (handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment before.core ∧
      term = assignment uv ∧ EnumerationCompressionFrame.Frame before.core after ∧
      EnumerationCorrectness.Satisfies
        (handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment after
 := by
  have normal := packet.context.ready.semantic.ready.semantic.1.normal
  have members := SourceSynthesisCurrentDonePendingTypes.done_pending_type_members
    formulas solver ambient lib query signed whole accepted rootValue sourceHeap built
    key entry body depth ordinary stored order metadata caller before packet.valid done
    normal irreducible growth onlyU
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  apply SourcePruningEnumerationPendingRendering.render_assignment
    caller.checked.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver) ambient
    (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
    (literal "var1") fuel uv before.core after term pending packet.safe level frontier ordered
    ?_ observed checked
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

end MicroCFTA.SourceSynthesisCurrentDoneRendering
