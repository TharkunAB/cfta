import MicroCFTA.SourceRecursiveIntersectionNativeTraceSplit

/-!
# Nested native completion derivations

Each derivation records actual physical effects, memo lookup and demand,
completed compiled bodies, and their original completion frames. It contains
no kernel execution, purity, language, or completion-provenance premise.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A finite completed native evaluation retains each actual nested body and shared state. -/
inductive Evaluation (width : Nat) (Symbol Guard : Type) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) : {A : Type} → Code Symbol Guard A →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → A → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | pure (value : A) (state) : Evaluation width Symbol Guard emptyGuard conjoin (.pure value) state value state
  | work {job : Work Symbol Guard X} {next : X → Code Symbol Guard A} {state final} {result : A}
      (tail : Evaluation width Symbol Guard emptyGuard conjoin
        (next (InternedConstructorTemplates.run job state.machine.heap).1)
        (advance state {state.machine with heap := (InternedConstructorTemplates.run job state.machine.heap).2}) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.work job next) state result final
  | enter {domain : Interned DomainKey} {left right : Value Symbol Guard} {first second : Nat}
      {next : Interned DomainKey → Code Symbol Guard A} {state final} {result : A}
      (tail : Evaluation width Symbol Guard emptyGuard conjoin
        (next (SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second).1)
        (advance state {state.machine with domains := (SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second).2}) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.enter domain left right first second next) state result final
  | read {name : Nat} {next : Option (Value Symbol Guard) → Code Symbol Guard A} {state final} {result : A}
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next (SourcePreparedSharedRows.read state.machine.heap name)) state result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.read name next) state result final
  | optionalBinder {key : Nat × Nat} {body value : Value Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state final} {after : InternedConstructorTemplates.State Symbol Guard} {result : A}
      (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap = .done value after)
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (advance state {state.machine with heap := after}) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.optionalBinder key body next) state result final
  | nodeDirect {request actual : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected middle final} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.direct actual, selected))
      (body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode actual) selected value middle)
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) middle result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.node request next) state result final
  | nodeReady {request : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected current final} {handle : Nat} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.memoized handle, selected))
      (demand : demandNode handle selected = (.ready value, current))
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) current result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.node request next) state result final
  | nodeStarted {request actual : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected current middle final} {handle : Nat} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.memoized handle, selected))
      (demand : demandNode handle selected = (.evaluate actual, current))
      (body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode actual) current value middle)
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishNode handle value middle) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.node request next) state result final
  | edgeReady {request : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
      {state selected current final} {handle : Nat} {value : EdgeValue Symbol Guard} {result : A}
      (lookup : lookupEdge width request state = (handle, selected))
      (demand : demandEdge handle selected = (.ready value, current))
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) current result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.edge request next) state result final
  | edgeStarted {request actual : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
      {state selected current middle final} {handle : Nat} {value : EdgeValue Symbol Guard} {result : A}
      (lookup : lookupEdge width request state = (handle, selected))
      (demand : demandEdge handle selected = (.evaluate actual, current))
      (body : Evaluation width Symbol Guard emptyGuard conjoin (compileEdge emptyGuard conjoin actual) current value middle)
      (tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishEdge handle value middle) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.edge request next) state result final
  | finishNode {handle : Nat} {value : Value Symbol Guard} {next : Code Symbol Guard A} {state final} {result : A}
      (tail : Evaluation width Symbol Guard emptyGuard conjoin next (SourceRecursiveIntersectionThunks.finishNode handle value state) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.finishNode handle value next) state result final
  | finishEdge {handle : Nat} {value : EdgeValue Symbol Guard} {next : Code Symbol Guard A} {state final} {result : A}
      (tail : Evaluation width Symbol Guard emptyGuard conjoin next (SourceRecursiveIntersectionThunks.finishEdge handle value state) result final) :
      Evaluation width Symbol Guard emptyGuard conjoin (.finishEdge handle value next) state result final

end MicroCFTA.SourceRecursiveIntersectionNative
