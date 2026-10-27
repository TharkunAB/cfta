import MicroCFTA.SourcePruningEnumerationCapturedEdgeDiagonalHistory
import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.EnumerationStratifiedTransport
import MicroCFTA.SourcePruningEnumerationSelectedEdgeNeutralSoundness
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Native acceptance of actual rendered captured fragments

The completed source receipt derives safety and fragment dependency order.
The actual renderer and its checked residuals construct the assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationValidity EnumerationSemantics EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual rendering and checked residuals imply native acceptance without an assumed final assignment. -/
theorem diagonal_render_sound_current
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after))
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified before.core level frontier)
    (discharged : SourcePruningEnumerationRendering.Discharged after.core)
    (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (renderFuel : Nat)
    (term : Language.Term Symbol) (pendingResiduals : List (Constraint × Language.Term Symbol))
    (renderedAfter : EnumerationState.State Symbol Constraint)
    (rendered : Success
      (SourcePruningEnumerationRendering.render afterCaller.checked.native.machine.heap marker renderFuel uv)
      after.core (term, pendingResiduals) renderedAfter)
    (checked : ∀ obligation ∈ pendingResiduals,
      SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) :
    ∃ assignment : Nat → Language.Term Symbol,
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) term ∧
      (∀ sc ∈ scs, Suspended.Holds assignment term sc) ∧
      Fragments.fill assignment fragment = term ∧
      EnumerationCompressionFrame.Frame after.core renderedAfter ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        assignment after.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        assignment renderedAfter := by
  obtain ⟨safe, history⟩ := diagonal_complete_safe_order formulas solver inventory caller before checkEmpty
    uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending allowed tries residual projected ranges observed
  obtain ⟨nextLevel, afterOrder⟩ := history level frontier ordered
  obtain ⟨assignment, satisfies, termSame, frame, renderedSatisfies⟩ :=
    SourcePruningEnumerationRendering.render_assignment afterCaller.checked.native.machine.heap
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      marker renderFuel uv after.core renderedAfter term pendingResiduals safe nextLevel (frontier + 1)
      afterOrder discharged rendered checked
  obtain ⟨original, edgeAccepted, parentAccepted, suspended, filled⟩ :=
    diagonal_complete_sound_current formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected paths
      counts flags pending allowed tries residual projected ranges canonical nonterminal freshArity retained
      observed ambient assignment satisfies
  refine ⟨assignment, original, ?_, ?_, ?_, filled.trans termSame.symm, frame, satisfies, renderedSatisfies⟩
  · simpa only [← termSame] using edgeAccepted
  · simpa only [← termSame] using parentAccepted
  · simpa only [← termSame] using suspended

end MicroCFTA.SourcePruningEnumerationCapturedEdge
