import MicroCFTA.SourceCurrentPublicationFilterSource
import MicroCFTA.InternedFreshOrdinaryContext

set_option linter.all true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace MicroCFTA.UsedMuRootEraseBoundary
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open SourceCurrentPublicationFilterSource (rootErase)
open SourceCurrentLiteralRootParts (Literal SameParts)
open SourceCurrentNativeCallbackErasure (eraseSelf)
private def expression : Syntax Nat Bool :=
  .binder true (.union [.var 1,.node [.mk 0 false [.var 1]]])
private def own : InternedBinderProtocol.Reference := .uninterned 0
private def inputs : List (Value Nat Bool) := [.reference own]
private def started := build expression inputs empty
private def raw : Value Nat Bool := match started with | .done value _ => value | .pending .. => .empty
private def common := started.state
private def filtered := eraseSelf own (run (withoutSelfReference own raw) common).1
private theorem start : started = .done raw common := by cbv
private theorem context : InternedFreshOrdinaryContext.Context common inputs := by
  have initial := InternedFreshOrdinaryContext.empty_context (Symbol := Nat) (Guard := Bool)
  have withOwn := initial.local own (ordinary_available empty 0)
  exact withOwn.build expression
private theorem raw_atom : Literal raw (.reference own) := by
  cbv
  exact .union (List.mem_cons_self) (.reference _)
private theorem missing_atom : ¬ Literal filtered (.reference own) := by
  cbv
  intro impossible
  cases impossible
/-- A nested unused binder exposes a bare outer name that root erasure does not remove from source. -/
theorem nested_binder_boundary :
    started = .done raw common ∧
    InternedFreshOrdinaryContext.Context common inputs ∧
    own ∉ InternedFreeNameSemantics.evaluate (.binder true expression) [] [] ∧
    rootErase expression = expression ∧
    build expression inputs common = .done raw common ∧
    build (rootErase expression) inputs common = .done raw common ∧
    raw ≠ .reference own ∧ own ∈ filtered.free ∧
    Literal raw (.reference own) ∧ ¬ Literal filtered (.reference own) ∧
    ¬ SameParts filtered raw := by
  refine ⟨start,context,?_,?_,?_,?_,?_,?_,raw_atom,missing_atom,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · intro same
    have shape := congrArg Value.referenceOf same
    cbv at shape
    cases shape
  · cbv
    exact List.mem_cons_self
  · intro parts
    exact missing_atom ((parts.1 (.reference own)).mpr raw_atom)
end MicroCFTA.UsedMuRootEraseBoundary
