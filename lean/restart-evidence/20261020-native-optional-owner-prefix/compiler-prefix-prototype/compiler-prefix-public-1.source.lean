import MicroCFTA.SourceCurrentNativeWalkOptionalPrefix

/-!
# Actual optional sites in compiled node prefixes

The actual prefix selects the Mu compiler or a nested node or edge call.
Each nested call retains its checked prefix, unbound optional trace and
full appended continuation. No owner or future return is a premise.
-/
namespace MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A X : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def NodeCut (fuel : Nat) (control : Control Node) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node) : Prop :=
  ∃ (prefixFuel childFuel : Nat) (child : NodeRequest Symbol Guard) (callNext : Node → Code Symbol Guard Node)
      (entry : Checked width) (innerNext : Node → Code Symbol Guard Node),
    prefixFuel + childFuel = fuel ∧
    Trace prefixFuel control before
      ((.code (requestNode child.domain child.left child.right) : Control Node).bind callNext) entry ∧
    Trace childFuel (.code (requestNode child.domain child.left child.right)) entry
      (.code (.optionalBinder pair body innerNext)) after ∧
    siteNext = fun value => (innerNext value).bind callNext

private def EdgeCut (fuel : Nat) (control : Control Node) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node) : Prop :=
  ∃ (prefixFuel childFuel : Nat) (child : EdgeRequest Symbol Guard) (callNext : Edge → Code Symbol Guard Node)
      (entry : Checked width) (innerNext : Node → Code Symbol Guard Edge),
    prefixFuel + childFuel = fuel ∧
    Trace prefixFuel control before
      ((.code (requestEdge child.domain child.left child.right) : Control Edge).bind callNext) entry ∧
    Trace childFuel (.code (requestEdge child.domain child.left child.right)) entry
      (.code (.optionalBinder pair body innerNext)) after ∧
    siteNext = fun value => (innerNext value).bind callNext

private theorem pure_no_optional (value : A) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard A)
    (actual : Trace fuel (.code (.pure value)) before (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

private theorem fail_no_optional (failure : Failure) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard A)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

private theorem work_no_optional (job : Work Symbol Guard A) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard A)
    (actual : Trace fuel (.code (.work job .pure)) before (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons _ _ next current _ _ count inputs one tail =>
    let built := InternedConstructorTemplates.run job before.native.machine.heap
    have observed : step (.code (.work job .pure)) before = .yielded (.code (.pure built.1))
        {before with native := advance before.native {before.native.machine with heap := built.2}} := rfl
    obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (observed.symm.trans one)
    exact pure_no_optional built.1 count _ after pair body siteNext tail

private theorem single_node (child : NodeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (requestNode child.domain child.left child.right)) before
      (.code (.optionalBinder pair body siteNext)) after) :
    NodeCut fuel (.code (requestNode child.domain child.left child.right)) before after pair body siteNext := by
  refine ⟨0,fuel,child,.pure,before,siteNext,Nat.zero_add fuel,?_,actual,?_⟩
  · simpa only [Control.bind,code_bind_pure] using
      (Trace.refl (.code (requestNode child.domain child.left child.right)) before)
  · funext value
    exact (code_bind_pure (siteNext value)).symm

private theorem node_walk (call : X → NodeRequest Symbol Guard) (inputs : List X)
    (job : List Node → Work Symbol Guard Node) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code ((walk (fun input => requestNode (call input).domain
      (call input).left (call input).right) inputs).bind (fun values => .work (job values) .pure))) before
      (.code (.optionalBinder pair body siteNext)) after) :
    NodeCut fuel (.code ((walk (fun input => requestNode (call input).domain
      (call input).left (call input).right) inputs).bind (fun values => .work (job values) .pure)))
      before after pair body siteNext := by
  rcases SourceCurrentNativeWalkOptionalPrefix.cut
      (fun input => requestNode (call input).domain (call input).left (call input).right) inputs
      (fun values => .work (job values) .pure) fuel before after pair body siteNext actual with
      ⟨walkFuel,outerFuel,values,middle,total,earlier,later⟩ |
      ⟨index,input,values,entry,prefixFuel,childFuel,innerNext,selected,earlier,total,priorTrace,child,same⟩
  · exact False.elim (work_no_optional (job values) outerFuel middle after pair body siteNext later)
  · exact ⟨prefixFuel,childFuel,call input,_,entry,innerNext,total,priorTrace,child,same⟩

private theorem edge_walk (call : X → EdgeRequest Symbol Guard) (inputs : List X)
    (job : List Edge → Work Symbol Guard Node) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code ((walk (fun input => requestEdge (call input).domain
      (call input).left (call input).right) inputs).bind (fun values => .work (job values) .pure))) before
      (.code (.optionalBinder pair body siteNext)) after) :
    EdgeCut fuel (.code ((walk (fun input => requestEdge (call input).domain
      (call input).left (call input).right) inputs).bind (fun values => .work (job values) .pure)))
      before after pair body siteNext := by
  rcases SourceCurrentNativeWalkOptionalPrefix.cut
      (fun input => requestEdge (call input).domain (call input).left (call input).right) inputs
      (fun values => .work (job values) .pure) fuel before after pair body siteNext actual with
      ⟨walkFuel,outerFuel,values,middle,total,earlier,later⟩ |
      ⟨index,input,values,entry,prefixFuel,childFuel,innerNext,selected,earlier,total,priorTrace,child,same⟩
  · exact False.elim (work_no_optional (job values) outerFuel middle after pair body siteNext later)
  · exact ⟨prefixFuel,childFuel,call input,_,entry,innerNext,total,priorTrace,child,same⟩

private theorem reference_cut (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Node) (left : Bool) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (compileReference domain name other left)) before
      (.code (.optionalBinder pair body siteNext)) after) :
    NodeCut fuel (.code (compileReference domain name other left)) before after pair body siteNext := by
  by_cases scope : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · let readNext := fun found : Option Node => match found with
      | some bound => if left then requestNode domain bound other else requestNode domain other bound
      | none => .fail (.missingPayload name)
    have exposed : compileReference domain name other left = .read name readNext := by
      simp only [compileReference,scope,ite_true,readNext]
      apply congrArg (Code.read name)
      funext found
      cases found <;> cases left <;> rfl
    rw [exposed] at actual ⊢
    cases actual with
    | cons _ _ next current _ _ count inputs one tail =>
      cases found : SourcePreparedSharedRows.read before.native.machine.heap name with
      | none =>
        have observed : step (.code (.read name readNext)) before =
            .yielded (.code (.fail (.missingPayload name))) before := by
          simp only [step,SourceRecursiveIntersectionNative.step,lift,found,readNext]
        obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (observed.symm.trans one)
        exact False.elim (fail_no_optional (.missingPayload name) count before after pair body siteNext tail)
      | some bound =>
        let child : NodeRequest Symbol Guard := if left then ⟨domain,bound,other⟩ else ⟨domain,other,bound⟩
        have observed : step (.code (.read name readNext)) before =
            .yielded (.code (requestNode child.domain child.left child.right)) before := by
          cases left <;> simp only [child,step,readNext,
            SourceRecursiveIntersectionNative.step,lift,found,Bool.false_eq_true,ite_true,ite_false]
        obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (observed.symm.trans one)
        refine ⟨1,count,child,.pure,before,siteNext,by omega,?_,tail,?_⟩
        · simpa only [Control.bind,code_bind_pure] using
            (Trace.cons _ _ _ _ _ _ 0 inputs observed (Trace.refl _ _))
        · funext value
          exact (code_bind_pure (siteNext value)).symm
  · have failed : Trace fuel (.code (.fail (.missingBinder name))) before
        (.code (.optionalBinder pair body siteNext)) after := by
      simpa only [compileReference,scope,ite_false] using actual
    exact False.elim (fail_no_optional (.missingBinder name) fuel before after pair body siteNext failed)

/-- A compiled node optional prefix retains its actual Mu branch or nested node or edge call. -/
theorem node (request : NodeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.optionalBinder pair body siteNext)) after) :
    (((decision request.domain.key request.left request.right = .bothMu ∨
        decision request.domain.key request.left request.right = .leftMu ∨
        decision request.domain.key request.left request.right = .rightMu) ∧
      Trace fuel (.code (compileMu request.domain request.left request.right)) before
        (.code (.optionalBinder pair body siteNext)) after) ∨
    (∃ (prefixFuel childFuel : Nat) (child : NodeRequest Symbol Guard) (callNext : Node → Code Symbol Guard Node)
        (entry : Checked width) (innerNext : Node → Code Symbol Guard Node),
      prefixFuel + childFuel = fuel ∧
      Trace prefixFuel (.code (compileNode request)) before
        ((.code (requestNode child.domain child.left child.right) : Control Node).bind callNext) entry ∧
      Trace childFuel (.code (requestNode child.domain child.left child.right)) entry
        (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind callNext) ∨
    (∃ (prefixFuel childFuel : Nat) (child : EdgeRequest Symbol Guard) (callNext : Edge → Code Symbol Guard Node)
        (entry : Checked width) (innerNext : Node → Code Symbol Guard Edge),
      prefixFuel + childFuel = fuel ∧
      Trace prefixFuel (.code (compileNode request)) before
        ((.code (requestEdge child.domain child.left child.right) : Control Edge).bind callNext) entry ∧
      Trace childFuel (.code (requestEdge child.domain child.left child.right)) entry
        (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind callNext)) := by
  change (_ ∧ _) ∨ NodeCut fuel (.code (compileNode request)) before after pair body siteNext ∨
    EdgeCut fuel (.code (compileNode request)) before after pair body siteNext
  cases selected : decision request.domain.key request.left request.right with
  | empty =>
    exact False.elim (pure_no_optional .empty fuel before after pair body siteNext
      (by simpa only [compileNode,selected] using actual))
  | reset =>
    exact .inr (.inl (by simpa only [compileNode,selected] using
      (single_node ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ fuel before after pair body siteNext
        (by simpa only [compileNode,selected] using actual))))
  | self =>
    exact False.elim (pure_no_optional request.left fuel before after pair body siteNext
      (by simpa only [compileNode,selected] using actual))
  | swap =>
    exact .inr (.inl (by simpa only [compileNode,selected] using
      (single_node ⟨request.domain,request.right,request.left⟩ fuel before after pair body siteNext
        (by simpa only [compileNode,selected] using actual))))
  | repeated key =>
    exact False.elim (pure_no_optional (repeatedValue key) fuel before after pair body siteNext
      (by simpa only [compileNode,selected] using actual))
  | bothMu => exact .inl ⟨.inl rfl,by simpa only [compileNode,selected] using actual⟩
  | leftMu => exact .inl ⟨.inr (.inl rfl),by simpa only [compileNode,selected] using actual⟩
  | rightMu => exact .inl ⟨.inr (.inr rfl),by simpa only [compileNode,selected] using actual⟩
  | leftUnion =>
    cases shape : request.left with
    | union entry members depth free =>
      simp only [shape] at selected
      exact .inr (.inl (by simpa only [compileNode,selected,shape] using
        (node_walk (fun member => ⟨request.domain,member,request.right⟩) members makeUnion fuel before after pair body siteNext
          (by simpa only [compileNode,selected,shape] using actual))))
    | _ =>
      simp only [shape] at selected
      exact False.elim (fail_no_optional _ fuel before after pair body siteNext
        (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
  | rightUnion =>
    cases shape : request.right with
    | union entry members depth free =>
      simp only [shape] at selected
      exact .inr (.inl (by simpa only [compileNode,selected,shape] using
        (node_walk (fun member => ⟨request.domain,request.left,member⟩) members makeUnion fuel before after pair body siteNext
          (by simpa only [compileNode,selected,shape] using actual))))
    | _ =>
      simp only [shape] at selected
      exact False.elim (fail_no_optional _ fuel before after pair body siteNext
        (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
  | leftReference =>
    cases shape : request.left with
    | reference name =>
      simp only [shape] at selected
      cases name with
      | interned name =>
        exact .inr (.inl (by simpa only [compileNode,selected,shape] using
          (reference_cut request.domain name request.right true fuel before after pair body siteNext
            (by simpa only [compileNode,selected,shape] using actual))))
      | _ => exact False.elim (fail_no_optional _ fuel before after pair body siteNext
          (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
    | _ =>
      simp only [shape] at selected
      exact False.elim (fail_no_optional _ fuel before after pair body siteNext
        (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
  | rightReference =>
    cases shape : request.right with
    | reference name =>
      simp only [shape] at selected
      cases name with
      | interned name =>
        exact .inr (.inl (by simpa only [compileNode,selected,shape] using
          (reference_cut request.domain name request.left false fuel before after pair body siteNext
            (by simpa only [compileNode,selected,shape] using actual))))
      | _ => exact False.elim (fail_no_optional _ fuel before after pair body siteNext
          (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
    | _ =>
      simp only [shape] at selected
      exact False.elim (fail_no_optional _ fuel before after pair body siteNext
        (by simpa only [compileNode,selected,shape,SourceRecursiveIntersectionCode.unsupported] using actual))
  | ordinary =>
    cases first : request.left with
    | node firstEntry firstRows firstDepth firstFree =>
      simp only [first] at selected
      cases second : request.right with
      | node secondEntry secondRows secondDepth secondFree =>
        simp only [second] at selected
        exact .inr (.inr (by simpa only [compileNode,selected,first,second,compileRows] using
          (edge_walk (fun rows => ⟨request.domain,rows.1,rows.2⟩) (pairs firstRows secondRows) makeNode
            fuel before after pair body siteNext
            (by simpa only [compileNode,selected,first,second,compileRows] using actual))))
      | _ =>
        simp only [second] at selected
        exact False.elim (fail_no_optional _ fuel before after pair body siteNext
          (by simpa only [compileNode,selected,first,second,SourceRecursiveIntersectionCode.unsupported] using actual))
    | _ =>
      simp only [first] at selected
      exact False.elim (fail_no_optional _ fuel before after pair body siteNext
        (by simpa only [compileNode,selected,first,SourceRecursiveIntersectionCode.unsupported] using actual))
  | unsupported => exact False.elim (fail_no_optional _ fuel before after pair body siteNext
      (by simpa only [compileNode,selected,SourceRecursiveIntersectionCode.unsupported] using actual))

end MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix.node
#print MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix.node
#print axioms MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix.node
