import MicroCFTA.SourceCurrentFiniteObservationExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
namespace MicroCFTA.SupportedReaderDiagnostic
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference NodeKey NodeRef)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
 match outcome with | .done result _ => result | .pending .. => .empty
private def leaf (symbol:Nat):Syntax Nat Bool := .node [.mk symbol false []]
private def capture (symbol:Nat):Syntax Nat Bool := .node [.mk 5 false [leaf symbol]]
private def built := build (.node [.mk 9 false [capture 0,capture 1]]) [] empty
private def base := built.state
private def item (index:Nat) := (children (value built))[index]?.getD .empty
private def expression : Syntax Nat Bool := .binder true (.node [.mk 2 false [.var 0,.var 1]])
private def firstRawRun := build expression [.reference (.uninterned 0)] base
private def secondRawRun := build expression [.reference (.uninterned 1)] firstRawRun.state
private def firstRun := execute (value firstRawRun) (fun name=>if name=.uninterned 0 then some (item 0) else none) secondRawRun.state
private def secondRun := execute (value secondRawRun) (fun name=>if name=.uninterned 1 then some (item 1) else none) firstRun.state
private def firstResult := value firstRun
private def secondResult := value secondRun
private def ident : Value Nat Bool → Nat
 | .node entry .. | .mu entry .. | .union entry .. =>entry.identity
 | _=>999
private def foreignExpression : Syntax Nat Bool := .binder true (.union [.var 1,.node [.mk 2 false [.var 0,.var 2]]])
private def fillers : Nat → State Nat Bool → State Nat Bool
 | 0, before=>before
 | n+1,before=>fillers n (build (leaf (100+n)) [] before).state
private def foreignRun (count:Nat) := build foreignExpression [.reference (.uninterned 99),item 0] (fillers count base)
private def foreignMu (count:Nat) := value (foreignRun count)
private def next (count:Nat) := (unfold (foreignMu count) (foreignRun count).state).state
private def summarize (v:Value Nat Bool) : Nat×List (Nat×List NodeRef) :=
 (ident v,(InternedEdgeResidency.nodeEdges v).map (fun row => (row.entry.key.symbol,row.children.map Value.referenceOf)))
#eval (base.nodes.next,ident (item 0),ident (item 1),ident firstResult,ident secondResult)
#eval (List.range 12).map (fun count => (count,ident (foreignMu count)))
#eval summarize (value (unfold firstResult (next 6)))
#eval summarize (value (unfold secondResult (next 6)))
#eval (children (value (unfold firstResult (next 6)))).map Value.free
#eval (children (value (unfold secondResult (next 6)))).map Value.free
#eval (value (unfold (foreignMu 6) (next 6))).free
end MicroCFTA.SupportedReaderDiagnostic
