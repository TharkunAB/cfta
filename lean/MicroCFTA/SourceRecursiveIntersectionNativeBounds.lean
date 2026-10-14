import MicroCFTA.SourceRecursiveIntersectionNativeMeaning

/-!
# Explicit word bounds on actual native requests

The resource premise records checked source keys at each memoized request in
the actual nested evaluation. Direct placeholder calls need no memo key.
No purity, successful execution, or completed value provenance is added.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual native memo requests retain the existing explicit machine-word range premises. -/
inductive Bounds {width : Nat} {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} : {A : Type} → {code : Code Symbol Guard A} →
      {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} → {value : A} →
      Evaluation width Symbol Guard emptyGuard conjoin code state value after → Prop where
  | pure (value : A) (state) : Bounds (Evaluation.pure value state)
  | work {job : Work Symbol Guard X} {next : X → Code Symbol Guard A} {state final} {result : A}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin
        (next (InternedConstructorTemplates.run job state.machine.heap).1)
        (advance state {state.machine with heap := (InternedConstructorTemplates.run job state.machine.heap).2}) result final}
      (bounded : Bounds tail) : Bounds (Evaluation.work (job := job) (next := next) (state := state) tail)
  | enter {domain : Interned DomainKey} {left right : Value Symbol Guard} {first second : Nat}
      {next : Interned DomainKey → Code Symbol Guard A} {state final} {result : A}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin
        (next (SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second).1)
        (advance state {state.machine with domains := (SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second).2}) result final}
      (bounded : Bounds tail) : Bounds (Evaluation.enter (domain := domain) (left := left) (right := right)
        (first := first) (second := second) (next := next) (state := state) tail)
  | read {name : Nat} {next : Option (Value Symbol Guard) → Code Symbol Guard A} {state final} {result : A}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next (SourcePreparedSharedRows.read state.machine.heap name)) state result final}
      (bounded : Bounds tail) : Bounds (Evaluation.read (name := name) (next := next) (state := state) tail)
  | optionalBinder {key : Nat × Nat} {body value : Value Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state final} {after : InternedConstructorTemplates.State Symbol Guard} {result : A}
      (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap = .done value after)
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (advance state {state.machine with heap := after}) result final}
      (bounded : Bounds tail) : Bounds (Evaluation.optionalBinder (next := next) done tail)
  | nodeDirect {request actual : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected middle final} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.direct actual, selected))
      {body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode actual) selected value middle}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) middle result final}
      (bodyBound : Bounds body) (tailBound : Bounds tail) : Bounds (Evaluation.nodeDirect (next := next) lookup body tail)
  | nodeReady {request : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected current final} {handle : Nat} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.memoized handle, selected))
      (demand : demandNode handle selected = (.ready value, current))
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) current result final}
      (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) (tailBound : Bounds tail) :
      Bounds (Evaluation.nodeReady (next := next) lookup demand tail)
  | nodeStarted {request actual : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
      {state selected current middle final} {handle : Nat} {value : Value Symbol Guard} {result : A}
      (lookup : lookupNode width request state = (.memoized handle, selected))
      (demand : demandNode handle selected = (.evaluate actual, current))
      {body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode actual) current value middle}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishNode handle value middle) result final}
      (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) (bodyBound : Bounds body) (tailBound : Bounds tail) :
      Bounds (Evaluation.nodeStarted (next := next) lookup demand body tail)
  | edgeReady {request : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
      {state selected current final} {handle : Nat} {value : EdgeValue Symbol Guard} {result : A}
      (lookup : lookupEdge width request state = (handle, selected))
      (demand : demandEdge handle selected = (.ready value, current))
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) current result final}
      (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) (tailBound : Bounds tail) :
      Bounds (Evaluation.edgeReady (next := next) lookup demand tail)
  | edgeStarted {request actual : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
      {state selected current middle final} {handle : Nat} {value : EdgeValue Symbol Guard} {result : A}
      (lookup : lookupEdge width request state = (handle, selected))
      (demand : demandEdge handle selected = (.evaluate actual, current))
      {body : Evaluation width Symbol Guard emptyGuard conjoin (compileEdge emptyGuard conjoin actual) current value middle}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishEdge handle value middle) result final}
      (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) (bodyBound : Bounds body) (tailBound : Bounds tail) :
      Bounds (Evaluation.edgeStarted (next := next) lookup demand body tail)
  | finishNode {handle : Nat} {value : Value Symbol Guard} {next : Code Symbol Guard A} {state final} {result : A}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin next (SourceRecursiveIntersectionThunks.finishNode handle value state) result final}
      (bounded : Bounds tail) : Bounds (Evaluation.finishNode (handle := handle) (value := value) (state := state) tail)
  | finishEdge {handle : Nat} {value : EdgeValue Symbol Guard} {next : Code Symbol Guard A} {state final} {result : A}
      {tail : Evaluation width Symbol Guard emptyGuard conjoin next (SourceRecursiveIntersectionThunks.finishEdge handle value state) result final}
      (bounded : Bounds tail) : Bounds (Evaluation.finishEdge (handle := handle) (value := value) (state := state) tail)

end MicroCFTA.SourceRecursiveIntersectionNative
