import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth

/-!
# Actual ordered children of a retained native row writer

The selected owner retains its original input rows. Each returned child
has an actual earlier node call at the same index in both input rows.
The call states grow into the current reader heap. A warm row demand uses
the same captured owner and the same complete request.
-/
namespace MicroCFTA.SourceCurrentNativeWriterChildOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (Written History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private theorem body_choice (request : EdgeRequest Symbol Guard) (before current : Checked width)
    (resume : Control (EdgeValue Symbol Guard))
    (one : body request .pure before = .yielded resume current) :
    resume = .code (SourceEqualityNativeCheckedCode.sentinel request.left) ∨
      ∃ first second combined,
        request.left.children.length = request.right.children.length ∧
        SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
        SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
        resume = .code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) ∧
        current = {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length before.operations).2} := by
  by_cases arity : request.left.children.length = request.right.children.length
  · simp only [SourceEqualityNativeDemand.body,ite_eq_right (not_not_intro arity)] at one
    cases left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [left] at one; cases one
    | ok first =>
      cases first with
      | none => simp only [left] at one; cases one
      | some first =>
        simp only [left] at one
        cases right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
        | error message => simp only [right] at one; cases one
        | ok second =>
          cases second with
          | none => simp only [right] at one; cases one
          | some second =>
            simp only [right] at one
            cases checked : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                request.left.children.length request.right.children.length before.operations).1 with
            | error message => simp only [checked] at one; cases one
            | ok branch =>
              cases branch with
              | mismatch | rejected =>
                  simp only [checked,sentinel,code_bind_pure] at one
                  exact .inl (Outcome.yielded.inj one).1.symm
              | ready combined =>
                  simp only [checked,code_bind_pure] at one
                  exact .inr ⟨first,second,combined,arity,rfl,rfl,checked,
                    (Outcome.yielded.inj one).1.symm,(Outcome.yielded.inj one).2.symm⟩
  · simp only [SourceEqualityNativeDemand.body,ite_eq_left arity,sentinel,code_bind_pure] at one
    exact .inl (Outcome.yielded.inj one).1.symm

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A live selected row retains its exact owner and actual ordered child calls at growing heaps. -/
theorem live {handle : Nat} {request : EdgeRequest Symbol Guard} {result : EdgeValue Symbol Guard}
    {reader : Heap} (written : Written (width := width) handle request result reader)
    (survives : Value.empty ∉ result.children) :
    ∃ (before first last : Checked width) (count : Nat),
      Good before ∧ EdgeReady before.native.machine request ∧
      before.native.edges.cells handle = some ⟨request,.evaluating⟩ ∧
      Grows before.native.machine.heap reader ∧
      Good first ∧ Good last ∧ Grows first.native.machine.heap reader ∧ Grows last.native.machine.heap reader ∧
      Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children) first result.children last count ∧
      result.entry.key.symbol = request.left.entry.key.symbol ∧
      result.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
        request.left.entry.key.constraint request.right.entry.key.constraint := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,_,_,growth,finalGrowth⟩ := written
  cases actual with
  | cons _ _ resume current _ _ rest inputs one tail =>
    have fields : Fields (.edgeBody request .pure) before := ⟨ready,fun _ => trivial⟩
    have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before good inputs fields
    have currentGood : Good current := by simpa only [one,Outcome.state] using checked.1
    change body request .pure before = .yielded resume current at one
    rcases body_choice request before current resume one with sentinelCase | accepted
    · subst resume
      obtain ⟨_,equal,_,_⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
        (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) rest current after result tail
      have available : Values current.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
        intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact empty_available _
      have childFields := (MergedPhysicalGroupEdges.makeEdge_fields current.native.machine.heap
        currentGood.heap.semantic.1.normal.facts request.left.entry.key.symbol
        SourceEqualityConstraintConstructors.top [.empty] available).2.2
      apply False.elim
      apply survives
      rw [equal,childFields]
      exact List.mem_cons_self
    · obtain ⟨left,right,combined,arity,leftLoad,rightLoad,accepted,rfl,currentEq⟩ := accepted
      obtain ⟨inner,outer,values,middle,_,walked,made⟩ := bind_inverse rest
        (.code (SourceRecursiveIntersectionCode.walk
          (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children)))
        (fun values => .work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure) current after result tail
      have walkFields := SourceCurrentAllocatedNativeCodeFields.fields_walk current.operations
        (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children) (by intro pair member value; trivial)
      have middleFacts := effects walked currentGood walkFields
      obtain ⟨_,equal,_,workInputs⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback _ outer middle after result made
      have available : Values middle.native.machine.heap values := by
        cases workInputs with
        | edge _ _ _ available => exact available
      have resultFields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap
        middleFacts.1.heap.semantic.1.normal.facts request.left.entry.key.symbol
        (SourceEqualityConjoinAllocation.readback combined) values available
      have madeFields : Fields (.code (.work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle :=
        (effects (walked.bind (fun values => .work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) currentGood (by
          simpa only [step,one,SourceCurrentAllocatedNativeFieldClosure.OutcomeFields]
            using checked.2.2.2.2.2)).2.2.2.2
      have later := effects made middleFacts.1 madeFields
      have middleGrowth := grows_trans later.2.2.1.growth finalGrowth
      have currentGrowth : Grows current.native.machine.heap reader := by rw [currentEq]; exact growth
      have symbol : result.entry.key.symbol = request.left.entry.key.symbol := equal ▸ resultFields.1
      have guard : result.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
          request.left.entry.key.constraint request.right.entry.key.constraint := by
        have literal := SourceEqualityNativeDemandAcceptedLanguage.ready_readback request before left right combined
          good.operations (good.fields _ _ ready.2.1).1 (good.fields _ _ ready.2.2).1 arity leftLoad rightLoad accepted
        exact (equal ▸ resultFields.2.1).trans literal
      have children : result.children = values := equal ▸ resultFields.2.2
      exact ⟨before,current,middle,inner,good,ready,owner,growth,currentGood,middleFacts.1,
        currentGrowth,middleGrowth,children ▸ SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback _ _ inner _ _ _ walked,
        symbol,guard⟩

/-- Each selected output child comes from the same input index and actual earlier node call. -/
theorem child {handle : Nat} {request : EdgeRequest Symbol Guard} {result : EdgeValue Symbol Guard}
    {reader : Heap} (written : Written (width := width) handle request result reader)
    (survives : Value.empty ∉ result.children) (index : Nat) (value : Value Symbol Guard)
    (selected : result.children[index]? = some value) :
    ∃ (left right : Value Symbol Guard) (before after : Checked width) (fuel : Nat),
      request.left.children[index]? = some left ∧ request.right.children[index]? = some right ∧
      Good before ∧ Good after ∧ Grows before.native.machine.heap reader ∧ Grows after.native.machine.heap reader ∧
      Trace fuel (.code (requestNode request.domain left right)) before (.code (.pure value)) after := by
  obtain ⟨_,first,last,_,_,_,_,_,good,_,_,growth,walked,_⟩ := live written survives
  obtain ⟨pair,current,next,prefixFuel,childFuel,suffixFuel,input,_,initialCalls,called,suffix⟩ :=
    SourceCurrentNativeRowOrigins.indexed walked index value selected
  have firstFields := SourceCurrentAllocatedNativeCodeFields.fields_walk first.operations
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    ((request.left.children.zip request.right.children).take index) (by intro pair member value; trivial)
  have currentFacts := effects initialCalls.trace good firstFields
  have nextFacts := effects called currentFacts.1 (by intro value; trivial)
  have lastFields := SourceCurrentAllocatedNativeCodeFields.fields_walk next.operations
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    ((request.left.children.zip request.right.children).drop (index + 1)) (by intro pair member value; trivial)
  have suffixFacts := effects suffix.trace nextFacts.1 lastFields
  have nextGrowth := grows_trans suffixFacts.2.2.1.growth growth
  have currentGrowth := grows_trans nextFacts.2.2.1.growth nextGrowth
  have paired := List.getElem?_zip_eq_some.mp input
  exact ⟨pair.1,pair.2,current,next,childFuel,paired.1,paired.2,currentFacts.1,nextFacts.1,
    currentGrowth,nextGrowth,called⟩

/-- An actual warm demand supplies child provenance from its captured historical writer. -/
theorem warm_child {state : Checked width} (history : History state) (good : Good state)
    (request : EdgeRequest Symbol Guard) (chosen running : Native width Symbol Guard) (handle : Nat)
    (result : EdgeValue Symbol Guard) (ready : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (lookup : lookupEdge width request state.native = (handle,chosen))
    (demand : demandEdge handle chosen = (.ready result,running))
    (survives : Value.empty ∉ result.children) (index : Nat) (value : Value Symbol Guard)
    (selected : result.children[index]? = some value) :
    ∃ (left right : Value Symbol Guard) (before after : Checked width) (fuel : Nat),
      request.left.children[index]? = some left ∧ request.right.children[index]? = some right ∧
      Good before ∧ Good after ∧ Grows before.native.machine.heap state.native.machine.heap ∧
      Grows after.native.machine.heap state.native.machine.heap ∧
      Trace fuel (.code (requestNode request.domain left right)) before (.code (.pure value)) after :=
  child (history.warm good request chosen running handle result ready safe lookup demand) survives index value selected

end MicroCFTA.SourceCurrentNativeWriterChildOrigins
