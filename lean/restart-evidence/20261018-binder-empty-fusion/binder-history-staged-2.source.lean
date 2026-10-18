import MicroCFTA.SourceCurrentFilteredSourceFusion
namespace MicroCFTA.BinderHistoryStaged
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private def row : Syntax Nat Bool := .node [.mk 7 false [.var 0,.var 1]]
private def author : Syntax Nat Bool := .binder true row
private def source : Syntax Nat Bool := .binder false author
private def requesterBody : Syntax Nat Bool := .union [row,.empty]
private def requester : Syntax Nat Bool := .binder true requesterBody
private def report [Repr Item] (name : String) (item : Item) : IO Unit := do
  IO.println (name ++ ": " ++ reprStr item)
  (← IO.getStdout).flush

#eval do
  let built := build source [] empty
  let heap := built.state
  report "outer" (done built,heap.nodes.next,heap.edges.next)
  match val built with
  | .mu outer body outerDepth ordinary =>
      let q := Reference.interned outer.identity
      let r := Reference.uninterned (ordinaryLevel outerDepth)
      report "outer-names" (outer.identity,ordinaryLevel outerDepth)
      match body,ordinary with
      | .mu first firstBody firstDepth firstOrdinary, .mu second secondBody secondDepth secondOrdinary =>
          report "older-used" (first.identity,second.identity,
            firstBody.free.contains (.interned first.identity),secondBody.free.contains (.interned second.identity))
          let firstProbe := callback requesterBody [.reference q] .depth heap
          let firstOrdinaryProbe := callback requesterBody [.reference q]
            (.uninterned (ordinaryLevel (val firstProbe))) firstProbe.state
          report "first-probes" (done firstProbe,done firstOrdinaryProbe,
            (val firstProbe).referenceOf == firstDepth.referenceOf,
            (val firstOrdinaryProbe).referenceOf == firstOrdinary.referenceOf,
            firstOrdinaryProbe.state.nodes.next == heap.nodes.next)
          let secondProbe := callback requesterBody [.reference r] .depth heap
          let secondOrdinaryProbe := callback requesterBody [.reference r]
            (.uninterned (ordinaryLevel (val secondProbe))) secondProbe.state
          report "second-probes" (done secondProbe,done secondOrdinaryProbe,
            (val secondProbe).referenceOf == secondDepth.referenceOf,
            (val secondOrdinaryProbe).referenceOf == secondOrdinary.referenceOf,
            secondOrdinaryProbe.state.nodes.next == heap.nodes.next)
          let firstRequest := build requester [.reference q] heap
          let secondRequest := build requester [.reference r] firstRequest.state
          report "current-requests" (done firstRequest,done secondRequest,
            (val firstRequest).referenceOf == body.referenceOf,
            (val secondRequest).referenceOf == ordinary.referenceOf,
            secondRequest.state.nodes.next == heap.nodes.next)
          let firstFiltered := run (withoutSelfReference .depth (val firstRequest)) secondRequest.state
          let firstResult := execute firstFiltered.1 (fun name => if name = q then some .empty else none) firstFiltered.2
          report "first-empty" (done firstResult,(val firstResult).referenceOf == .empty,
            firstResult.state.nodes.next,firstResult.state.edges.next)
          let secondFiltered := run (withoutSelfReference .depth (val secondRequest)) firstResult.state
          let secondResult := execute secondFiltered.1 (fun name => if name = r then some .empty else none) secondFiltered.2
          report "second-empty" (done secondResult,(val secondResult).referenceOf == .empty,
            secondResult.state.nodes.next,secondResult.state.edges.next)
      | _,_ => report "wrong-inner-shape" false
  | _ => report "wrong-outer-shape" false

end MicroCFTA.BinderHistoryStaged
