import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWords

namespace MicroCFTA.FiniteOrdinaryWordsChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedFiniteOrdinaryWordExecution
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "KNode" => SourceCurrentAllocatedFiniteOrdinaryKeys.Node
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
local notation "Ranges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An arbitrary yielded prefix needs no physical trace or completed request. -/
theorem all_actual_prefixes (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right)
    (fuel : Nat) (control : Control (Value Symbol Guard)) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode emptyDomain left right)) before control after) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) control :=
  SourceCurrentAllocatedFiniteOrdinaryWords.node bits before good left right
    leftAvailable rightAvailable leftKeys rightKeys fuel control after actual

/-- Full stored guards remain unrestricted at every requested row and child. -/
theorem arbitrary_full_guards (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (leftNode rightNode : Interned InternedBinderProtocol.NodeKey)
    (leftEdge rightEdge : Interned (EdgeKey Symbol Guard))
    (leftNodeFits : leftNode.identity < 2 ^ bits) (rightNodeFits : rightNode.identity < 2 ^ bits)
    (leftEdgeFits : leftEdge.identity < 2 ^ (bits + 2)) (rightEdgeFits : rightEdge.identity < 2 ^ (bits + 2))
    (leftAvailable : Available before.native.machine.heap (.node leftNode [⟨leftEdge, [.empty]⟩] 0 []))
    (rightAvailable : Available before.native.machine.heap (.node rightNode [⟨rightEdge, [.empty]⟩] 0 [])) :
    Ranges (.code (requestNode emptyDomain (.node leftNode [⟨leftEdge, [.empty]⟩] 0 [])
      (.node rightNode [⟨rightEdge, [.empty]⟩] 0 []))) before := by
  apply SourceCurrentAllocatedFiniteOrdinaryWords.node bits before good _ _ leftAvailable rightAvailable
  · exact .ordinary leftNodeFits (.cons leftEdgeFits (.cons .empty .nil) .nil)
  · exact .ordinary rightNodeFits (.cons rightEdgeFits (.cons .empty .nil) .nil)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- A warm evaluation selects the exact candidate before compiling its captured body. -/
theorem warm_owner_exact (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right)
    (owner : NodeRequest Symbol Guard) (chosen running : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (handle : Nat)
    (selected : lookupNode (bits + 2) ⟨emptyDomain, left, right⟩ before.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate owner, running)) :
    owner = ⟨emptyDomain, left, right⟩ := by
  exact Origins.node_started before.native.machine good.native.machine _ owner before.native chosen running handle
    (Origins.of_valid before.native good.native) ⟨SourceRecursiveIntersectionKernel.empty_domain _, leftAvailable, rightAvailable⟩
    (SourceCurrentAllocatedFiniteOrdinaryKeys.node_key_safe_empty leftKeys rightKeys) selected demanded

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- A finish stores a value only at the original evaluating owner. No result key bound is needed. -/
theorem finish_exact_owner {width : Nat} (source : Machine Symbol Guard)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (origins : Origins source before)
    (handle : Nat) (owner : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : before.nodes.cells handle = some ⟨owner, .evaluating⟩) :
    Origins source (SourceRecursiveIntersectionThunks.finishNode handle value before) ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value before).nodes.cells handle =
        some ⟨owner, .returned value⟩ := by
  refine ⟨Origins.finishNode source before origins handle value, ?_⟩
  simpa only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, running] using
    FlatMemoThunk.setStatus_cell handle (.returned value) before.nodes ⟨owner, .evaluating⟩ running

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Result payloads can have unbounded reference names without changing original key certificates. -/
theorem unbounded_result_reference {width : Nat} (source : Machine Symbol Guard)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (origins : Origins source before)
    (handle : Nat) (name : InternedBinderProtocol.Reference) :
    Origins source (SourceRecursiveIntersectionThunks.finishNode handle (.reference name) before) :=
  Origins.finishNode source before origins handle (.reference name)

/-- Actual checked edge allocation prefixes retain every future original-key check. -/
theorem edge_body_prefix (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (request : EdgeRequest Symbol Guard)
    (inputs : SourceCurrentAllocatedFiniteOrdinaryWordCode.EdgeInputs bits before.native.machine request)
    (fuel : Nat) (control : Control (EdgeValue Symbol Guard)) (after : Checked (bits + 2))
    (actual : Steps fuel (.edgeBody request .pure) before control after) :
    Origins before.native.machine after.native ∧
      SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) control := by
  have certificate : Certified bits before.native.machine (.edgeBody request (Code.pure)) := ⟨inputs, fun _ => trivial⟩
  have reached := SourceCurrentAllocatedFiniteOrdinaryWordExecution.reached bits before.native.machine good.native.machine
    fuel _ control before after (Origins.of_valid before.native good.native) certificate actual
  exact ⟨reached.1, reached.2.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- A changed current machine does not replace the fixed source used for warm original readback. -/
theorem source_is_initial {width : Nat} (source : Machine Symbol Guard)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (origins : Origins source before)
    (arbitraryMachine : Machine Symbol Guard) :
    Origins source (advance before arbitraryMachine) :=
  Origins.advance source before origins arbitraryMachine

/-- Word safety does not assert completion when a current request is blocked. -/
theorem busy_is_not_completion (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right)
    (reason : Blocked) (control : Control (Value Symbol Guard)) (after : Checked (bits + 2))
    (blocked : step (.code (requestNode emptyDomain left right)) before = .blocked reason control after) :
    Ranges (.code (requestNode emptyDomain left right)) before ∧
      ∀ fuel, SourceEqualityNativeDemand.execute (fuel + 1) (.code (requestNode emptyDomain left right)) before = .blocked reason control after := by
  refine ⟨SourceCurrentAllocatedFiniteOrdinaryWords.node bits before good left right
    leftAvailable rightAvailable leftKeys rightKeys, ?_⟩
  intro fuel
  simp only [SourceEqualityNativeDemand.execute, blocked]

end MicroCFTA.FiniteOrdinaryWordsChecks

#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.all_actual_prefixes
#check @MicroCFTA.FiniteOrdinaryWordsChecks.all_actual_prefixes
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.arbitrary_full_guards
#check @MicroCFTA.FiniteOrdinaryWordsChecks.arbitrary_full_guards
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.warm_owner_exact
#check @MicroCFTA.FiniteOrdinaryWordsChecks.warm_owner_exact
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.finish_exact_owner
#check @MicroCFTA.FiniteOrdinaryWordsChecks.finish_exact_owner
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.unbounded_result_reference
#check @MicroCFTA.FiniteOrdinaryWordsChecks.unbounded_result_reference
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.edge_body_prefix
#check @MicroCFTA.FiniteOrdinaryWordsChecks.edge_body_prefix
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.source_is_initial
#check @MicroCFTA.FiniteOrdinaryWordsChecks.source_is_initial
#print axioms MicroCFTA.FiniteOrdinaryWordsChecks.busy_is_not_completion
#check @MicroCFTA.FiniteOrdinaryWordsChecks.busy_is_not_completion
