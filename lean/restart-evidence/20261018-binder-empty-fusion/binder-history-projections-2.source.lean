import MicroCFTA.SourceCurrentFilteredSourceFusion
namespace MicroCFTA.BinderHistoryProjections
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private def row : Syntax Nat Bool := .node [.mk 7 false [.var 0,.var 1]]
private def author : Syntax Nat Bool := .binder true row
private def source : Syntax Nat Bool := .binder false author
private def requesterBody : Syntax Nat Bool := .union [row,.empty]
private def requester : Syntax Nat Bool := .binder true requesterBody
private def built := build source [] empty
private def checks : Bool :=
  let heap := built.state
  done built &&
  match val built with
  | .mu outer body outerDepth ordinary =>
      let q := Reference.interned outer.identity
      let r := Reference.uninterned (ordinaryLevel outerDepth)
      match body,ordinary with
      | .mu first firstBody firstDepth firstOrdinary, .mu second secondBody secondDepth secondOrdinary =>
          let firstProbe := callback requesterBody [.reference q] .depth heap
          let firstOrdinaryProbe := callback requesterBody [.reference q]
            (.uninterned (ordinaryLevel (val firstProbe))) firstProbe.state
          let secondProbe := callback requesterBody [.reference r] .depth heap
          let secondOrdinaryProbe := callback requesterBody [.reference r]
            (.uninterned (ordinaryLevel (val secondProbe))) secondProbe.state
          let firstRequest := build requester [.reference q] heap
          let secondRequest := build requester [.reference r] firstRequest.state
          let firstFiltered := run (withoutSelfReference .depth (val firstRequest)) secondRequest.state
          let firstResult := execute firstFiltered.1 (fun name => if name = q then some .empty else none) firstFiltered.2
          let secondFiltered := run (withoutSelfReference .depth (val secondRequest)) firstResult.state
          let secondResult := execute secondFiltered.1 (fun name => if name = r then some .empty else none) secondFiltered.2
          firstBody.free.contains (.interned first.identity) &&
          secondBody.free.contains (.interned second.identity) &&
          done firstProbe && done firstOrdinaryProbe &&
          ((val firstProbe).referenceOf == firstDepth.referenceOf) &&
          ((val firstOrdinaryProbe).referenceOf == firstOrdinary.referenceOf) &&
          done secondProbe && done secondOrdinaryProbe &&
          ((val secondProbe).referenceOf == secondDepth.referenceOf) &&
          ((val secondOrdinaryProbe).referenceOf == secondOrdinary.referenceOf) &&
          done firstRequest && done secondRequest &&
          ((val firstRequest).referenceOf == body.referenceOf) &&
          ((val secondRequest).referenceOf == ordinary.referenceOf) &&
          done firstResult && ((val firstResult).referenceOf == InternedBinderProtocol.NodeRef.empty) &&
          done secondResult && ((val secondResult).referenceOf == InternedBinderProtocol.NodeRef.empty)
      | _,_ => false
  | _ => false
private theorem unpack (outcome : Outcome Nat Bool (Value Nat Bool)) (success : done outcome = true) :
    outcome = .done (val outcome) outcome.state := by
  cases outcome <;> simp_all [done,val,Outcome.state]
private theorem computed : checks = true := by cbv
private theorem checked_witness :
    build source [] empty = .done (val built) built.state ∧
    SourceEqualityRequiredCache.Ready built.state ∧ checks = true := by
  have success : done built = true := (Bool.and_eq_true_iff.mp computed).1
  have actual := unpack built success
  exact ⟨actual,SourceEqualityRequiredCache.constructed source (val built) built.state actual,computed⟩
theorem focused_key_and_empty_checks :
    build source [] empty = .done (val built) built.state ∧
    SourceEqualityRequiredCache.Ready built.state ∧ checks = true := checked_witness
end MicroCFTA.BinderHistoryProjections
