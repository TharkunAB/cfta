import MicroCFTA.SourceCurrentHeadIssuedHistory
import MicroCFTA.SourceCurrentRequiredPublicationHistory

/-!
# Issued history through two actual Mu steps

The closed source is Mu x. Mu y. node7[x,y].
The first unfold returns a used Mu. The selected row occurs only after
that Mu also unfolds. The selected child retains its actual last-Mu call.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.HeadIssuedPathKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (History Written)
open SourceCurrentRecursiveHeadChainRows (Chain)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
local notation "Node" => Value Nat Bool
local notation "Row" => EdgeValue Nat Bool
local notation "Heap" => State Nat Bool

private def expression : Syntax Nat Bool :=
  .binder false (.binder false (.node [.mk 7 false [.var 1,.var 0]]))
private def built := build expression [] empty
private def value : Node := match built with | .done value _ => value | _ => .empty
private def before : Heap := built.state
private def first := unfold value before
private def retained : Node := match first with | .done value _ => value | _ => .empty
private def middle : Heap := first.state
private def second := unfold retained middle
private def terminal : Node := match second with | .done value _ => value | _ => .empty
private def terminalHeap : Heap := second.state
private def called := SourceEqualityRequiredWorker.head 8 value before
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after : Heap := match called with | .done _ after => after | _ => before
private def row : Row := (nodeEdges result)[0]?.getD (run (makeEdge 0 false []) before).1
private def child : Node := row.children[1]?.getD .empty
private def entry := match value with | .mu entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match value with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match value with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match value with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def lastEntry := match retained with | .mu entry _ _ _ => entry | _ => entry
private def lastBody : Node := match retained with | .mu _ body _ _ => body | _ => .empty
private def lastDepth : Node := match retained with | .mu _ _ depth _ => depth | _ => .empty
private def lastOrdinary : Node := match retained with | .mu _ _ _ ordinary => ordinary | _ => .empty

private theorem built_done : built = .done value before := by cbv
private theorem first_done : first = .done retained middle := by cbv
private theorem second_done : second = .done terminal terminalHeap := by cbv
private theorem called_done : called = .done result after := by cbv
private theorem shapes : value = .mu entry body depth ordinary ∧
    retained = .mu lastEntry lastBody lastDepth lastOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal lastDepth lastOrdinary = true ∧
    value.free = [] ∧ (nodeEdges result)[0]? = some row ∧
    row.children[1]? = some child ∧ child = retained ∧
    nodeEdges value = [] ∧ nodeEdges retained = [] := by cbv
private theorem no_literal :
    ¬ SourceCurrentLiteralRootParts.Row value row ∧
    ¬ SourceCurrentLiteralRootParts.Row retained row := by
  constructor
  · intro part
    rw [shapes.1] at part
    cases part
  · intro part
    rw [shapes.2.1] at part
    cases part
private theorem ready : Ready before := SourceEqualityRequiredCache.constructed expression value before built_done
private theorem available : Available before value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value before built_done
private theorem actual : SourceEqualityRequiredHead.Head value before result after :=
  SourceEqualityRequiredWorkerSound.head_graph 8 value before result after called_done
private theorem first_call : execute body (selfEnvironment entry body depth ordinary) before = .done retained middle := by
  change unfold (.mu entry body depth ordinary) before = .done retained middle
  rw [←shapes.1]
  exact first_done
private theorem last_call : execute lastBody (selfEnvironment lastEntry lastBody lastDepth lastOrdinary) middle =
    .done terminal terminalHeap := by
  change unfold (.mu lastEntry lastBody lastDepth lastOrdinary) middle = .done terminal terminalHeap
  rw [←shapes.2.1]
  exact second_done
private theorem two_mu : Chain before value terminalHeap terminal := by
  have start : Chain before value before (.mu entry body depth ordinary) :=
    shapes.1 ▸ Chain.start ready available shapes.2.2.2.2.1
  have first : Chain before value middle (.mu lastEntry lastBody lastDepth lastOrdinary) :=
    shapes.2.1 ▸ Chain.mu start first_call
  exact Chain.mu first last_call

private theorem costs : InternedFreshOrdinaryCostHeap.Heap before := by
  simpa only [before,built] using InternedFreshOrdinaryCosts.closed_heap expression
private noncomputable def initial_path : SourceCurrentNativeMuIssuedHistory.Path empty before :=
  SourceCurrentNativeMuIssuedHistory.closed_path expression

private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady before :=
  SourceEqualityRequiredSemanticCache.constructed expression value before built_done
private noncomputable def final_path : SourceCurrentNativeMuIssuedHistory.Path empty after :=
  .trans initial_path (Classical.choice (SourceCurrentHeadIssuedHistory.head actual semantic costs available))

private theorem checked_witness :
    built = .done value before ∧ Ready before ∧ Available before value ∧
    first = .done retained middle ∧ second = .done terminal terminalHeap ∧
    called = .done result after ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal lastDepth lastOrdinary = true ∧
    ¬ SourceCurrentLiteralRootParts.Row value row ∧ ¬ SourceCurrentLiteralRootParts.Row retained row ∧
    Chain before value terminalHeap terminal ∧ (nodeEdges result)[0]? = some row ∧
    row.children[1]? = some child ∧ child = retained ∧ Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty before) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty after) ∧
    ∃ (chosenEntry : Interned InternedBinderProtocol.NodeKey) (chosenBody chosenDepth chosenOrdinary : Node)
        (firstHeap secondHeap : Heap) (returned : Node) (lastHeap : Heap) (lastValue : Node),
      Chain before value firstHeap (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) ∧
      unfold (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) firstHeap = .done returned secondHeap ∧
      SourceCurrentRecursiveHeadMuChildContexts.Suffix secondHeap returned lastHeap lastValue ∧
      SourceEqualityRequiredCache.Keeps lastHeap after ∧ SourceCurrentLiteralRootParts.Row returned row ∧
      SourceCurrentNativeMuIssuedWriters.Written empty after chosenEntry.key (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) ∧
      SourceCurrentStoredMuUnfoldChildContexts.Child chosenBody firstHeap secondHeap row 1 child := by
  have lineage := SourceCurrentHeadIssuedHistory.head_child value before semantic costs available
    shapes.2.2.2.2.1 result after actual initial_path 0 row shapes.2.2.2.2.2.1 1 child shapes.2.2.2.2.2.2.1
  rcases lineage with literal | lineage
  · exact False.elim (no_literal.1 literal)
  · exact ⟨built_done,ready,available,first_done,second_done,called_done,
      shapes.2.2.1,shapes.2.2.2.1,no_literal.1,no_literal.2,two_mu,
      shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,⟨initial_path⟩,⟨final_path⟩,lineage⟩

/-- Two actual Mu steps retain the issued path and the selected Mu writer at the final reader. -/
theorem two_mu_issued :
    built = .done value before ∧ Ready before ∧ Available before value ∧
    first = .done retained middle ∧ second = .done terminal terminalHeap ∧
    called = .done result after ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal lastDepth lastOrdinary = true ∧
    ¬ SourceCurrentLiteralRootParts.Row value row ∧ ¬ SourceCurrentLiteralRootParts.Row retained row ∧
    Chain before value terminalHeap terminal ∧ (nodeEdges result)[0]? = some row ∧
    row.children[1]? = some child ∧ child = retained ∧ Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty before) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty after) ∧
    ∃ (chosenEntry : Interned InternedBinderProtocol.NodeKey) (chosenBody chosenDepth chosenOrdinary : Node)
        (firstHeap secondHeap : Heap) (returned : Node) (lastHeap : Heap) (lastValue : Node),
      Chain before value firstHeap (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) ∧
      unfold (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) firstHeap = .done returned secondHeap ∧
      SourceCurrentRecursiveHeadMuChildContexts.Suffix secondHeap returned lastHeap lastValue ∧
      SourceEqualityRequiredCache.Keeps lastHeap after ∧ SourceCurrentLiteralRootParts.Row returned row ∧
      SourceCurrentNativeMuIssuedWriters.Written empty after chosenEntry.key (.mu chosenEntry chosenBody chosenDepth chosenOrdinary) ∧
      SourceCurrentStoredMuUnfoldChildContexts.Child chosenBody firstHeap secondHeap row 1 child := checked_witness

end MicroCFTA.HeadIssuedPathKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.HeadIssuedPathKernels.two_mu_issued
#print MicroCFTA.HeadIssuedPathKernels.two_mu_issued
#print axioms MicroCFTA.HeadIssuedPathKernels.two_mu_issued
