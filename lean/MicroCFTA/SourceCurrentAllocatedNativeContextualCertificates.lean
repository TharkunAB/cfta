import MicroCFTA.SourceCurrentAllocatedNativeContextualCode
import MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning
import MicroCFTA.SourceCurrentAllocatedNativeNodeBranches

/-!
# Static contextual certificates for ordinary source branches

Ordered request walks collect only child-local contextual laws and returned
physical records. Actual constructor equations derive the parent law. These
certificates do not assume a parent result law or a completed parent trace.
Mu entry and original binding resolution remain separate transformers.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
open Language BinderLanguage Cache InternedBinderProtocol InternedConstructorTemplates
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeContextualCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)]

section Walks
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Every ordered node request contributes its own law and available result. -/
theorem node_walk_certified (request : A → NodeRequest Symbol Guard) (inputs : List A)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified view model ranked holds (SourceRecursiveIntersectionCode.walk (fun input => .node (request input) .pure) inputs)
      state (fun after values => Values after.heap values ∧
        All₂ (fun input value => NodeLaw view model ranked holds (request input) value) inputs values) := by
  induction inputs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), .nil⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, Code.bind, Certified]
      intro value middle middleValid growth middleSemantic available law
      apply certified_bind view model ranked holds _ _ middle middleValid middleSemantic _ _
        (ih middle middleValid middleSemantic)
      intro values after afterValid later afterSemantic tail
      exact ⟨by intro child member; cases member with
        | head => exact later.available value available
        | tail _ member => exact tail.1 child member, .cons law tail.2⟩

/-- Every matching ordered edge request contributes its own law and resident row. -/
theorem edge_walk_certified (request : A → EdgeRequest Symbol Guard) (inputs : List A)
    (matching : ∀ input ∈ inputs, (request input).left.entry.key.symbol = (request input).right.entry.key.symbol)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified view model ranked holds (SourceRecursiveIntersectionCode.walk (fun input => .edge (request input) .pure) inputs)
      state (fun after values => Edges after.heap values ∧
        All₂ (fun input value => EdgeLaw view model ranked holds (request input) value) inputs values) := by
  induction inputs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), .nil⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, Code.bind, Certified]
      refine ⟨matching first List.mem_cons_self, ?_⟩
      intro value middle middleValid growth middleSemantic resident law
      apply certified_bind view model ranked holds _ _ middle middleValid middleSemantic _ _
        (ih (fun input inside => matching input (List.mem_cons_of_mem _ inside)) middle middleValid middleSemantic)
      intro values after afterValid later afterSemantic tail
      exact ⟨by intro child member; cases member with
        | head => exact edge_grows _ _ later.heap value resident
        | tail _ member => exact tail.1 child member, .cons law tail.2⟩
end Walks

/-- The actual ordinary row join and node constructor derive a static parent certificate. -/
theorem compileRows_certified [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (leftAvailable : Available source (.node first left leftDepth leftFree))
    (rightAvailable : Available source (.node second right rightDepth rightFree))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (view source holds) model ranked holds (compileRows domain left right) state
      (fun _ value => NodeLaw (view source holds) model ranked holds
        ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩ value) := by
  unfold compileRows
  apply certified_bind (view source holds) model ranked holds _ _ state valid semantic _ _
    (edge_walk_certified (view source holds) model ranked holds
      (fun pair => ⟨domain, pair.1, pair.2⟩) (pairs left right)
      (fun pair member => SourceCurrentAllocatedNativeEdgeMeaning.joined_symbols left right pair member)
      state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done (makeNode values) middle value after done).1]
  exact SourceCurrentAllocatedNativeNodeRowsMeaning.rows_law source sourceFacts holds model ranked domain
    first left leftDepth leftFree second right rightDepth rightFree leftAvailable rightAvailable
    middle.heap middleValid.1 values children.1 children.2

/-- The source left-union walk derives its parent law in the actual constructor state. -/
theorem left_union_certified
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (right : Value Symbol Guard)
    (available : Available source (.union entry members depth free))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (view source holds) model ranked holds
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member right) members).bind
        (fun values => .work (makeUnion values) .pure)) state
      (fun _ value => NodeLaw (view source holds) model ranked holds ⟨domain, .union entry members depth free, right⟩ value) := by
  apply certified_bind (view source holds) model ranked holds _ _ state valid semantic _ _
    (node_walk_certified (view source holds) model ranked holds (fun member => ⟨domain, member, right⟩)
      members state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done (makeUnion values) middle value after done).1]
  exact SourceCurrentAllocatedNativeNodeBranches.left_union_law source sourceFacts holds model ranked domain entry
    members depth free right available middle.heap middleValid.1 values children.1 children.2

/-- The source right-union walk retains the corresponding ordered original member laws. -/
theorem right_union_certified
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (left : Value Symbol Guard)
    (available : Available source (.union entry members depth free))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (view source holds) model ranked holds
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain left member) members).bind
        (fun values => .work (makeUnion values) .pure)) state
      (fun _ value => NodeLaw (view source holds) model ranked holds ⟨domain, left, .union entry members depth free⟩ value) := by
  apply certified_bind (view source holds) model ranked holds _ _ state valid semantic _ _
    (node_walk_certified (view source holds) model ranked holds (fun member => ⟨domain, left, member⟩)
      members state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done (makeUnion values) middle value after done).1]
  exact SourceCurrentAllocatedNativeNodeBranches.right_union_law source sourceFacts holds model ranked domain entry
    members depth free left available middle.heap middleValid.1 values children.1 children.2

/-- Accepted checked child code needs only actual conjunction truth and each child law. -/
theorem children_certified
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (guards : ∀ term, holds (SourceEqualityConjoinAllocation.readback combined) term =
      (holds request.left.entry.key.constraint term && holds request.right.entry.key.constraint term))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified view model ranked holds (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)
      state (fun _ value => EdgeLaw view model ranked holds request value) := by
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind view model ranked holds _ _ state valid semantic _ _
    (node_walk_certified view model ranked holds (fun pair => ⟨request.domain, pair.1, pair.2⟩)
      (request.left.children.zip request.right.children) state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done _ middle value after done).1]
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.heap middleValid.1 request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values children.1
  apply SourceCurrentAllocatedNativeEdgeMeaning.edge_law view model ranked holds request _ arity symbols fields.1
    (fun term => by rw [fields.2.1]; exact guards term)
  rw [fields.2.2]
  exact children.2

/-- A rejected checked branch constructs a literal empty child without recursive calls. -/
theorem sentinel_certified
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard)
    (disjoint : ∀ first second term, ¬ (RowAt holds ranked.languages first request.left term ∧
      RowAt holds ranked.languages second request.right term))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified view model ranked holds (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ value => EdgeLaw view model ranked holds request value) := by
  intro value after done afterValid growth afterSemantic
  rw [(work_done _ state value after done).1]
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state.heap valid.1 request.left.entry.key.symbol
    SourceEqualityConstraintConstructors.top [.empty] (by intro value member; cases member with | head => exact empty_available _ | tail _ member => cases member)
  exact SourceCurrentAllocatedNativeEdgeMeaning.sentinel_edge_law view model ranked holds request _ fields.2.2 disjoint

section Direct
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Literal empty rejection has a direct certificate at every current machine. -/
theorem empty_certified (request : NodeRequest Symbol Guard) (literal : request.left = .empty ∨ request.right = .empty)
    (state : Machine Symbol Guard) :
    Certified view model ranked holds (.pure (.empty : Value Symbol Guard)) state
      (fun _ value => NodeLaw view model ranked holds request value) :=
  SourceCurrentAllocatedNativeNodeBranches.empty_law view model ranked holds request literal

/-- A reset request uses only its exact child's law in the empty domain. -/
theorem reset_certified (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) :
    Certified view model ranked holds (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right) state
      (fun _ value => NodeLaw view model ranked holds request value) := by
  intro value after afterValid growth afterSemantic available law
  exact SourceCurrentAllocatedNativeNodeBranches.reset_law view model ranked holds request value law

/-- A source swap transports only the exact reversed child request law. -/
theorem swap_certified (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) :
    Certified view model ranked holds (requestNode request.domain request.right request.left) state
      (fun _ value => NodeLaw view model ranked holds request value) := by
  intro value after afterValid growth afterSemantic available law
  exact SourceCurrentAllocatedNativeNodeBranches.swap_law view model ranked holds request value law

/-- Repeated-pair cutoff uses the actual sorted pair already present in the domain. -/
theorem repeated_certified (request : NodeRequest Symbol Guard) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (leftNonempty : inputOf request.left ≠ .empty) (rightNonempty : inputOf request.right ≠ .empty)
    (seen : SourceRecursiveIntersectionControl.pair first second ∈ request.domain.key.seen)
    (state : Machine Symbol Guard) :
    Certified view model ranked holds (.pure (SourceRecursiveIntersectionControl.repeatedValue
      (SourceRecursiveIntersectionControl.pair first second))) state
      (fun _ value => NodeLaw view model ranked holds request value) :=
  SourceCurrentAllocatedNativeNodeBranches.repeated_law view model ranked holds request first second
    leftIdentity rightIdentity leftNonempty rightNonempty seen
end Direct

/-- Closed physical self reuse follows from the fixed original input readback. -/
theorem self_certified
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (leftAvailable : Available source request.left)
    (rightAvailable : Available source request.right)
    (self : SourceRecursiveIntersectionControl.closedSelf request.left request.right = true)
    (state : Machine Symbol Guard) :
    Certified (view source holds) model ranked holds (.pure request.left) state
      (fun _ value => NodeLaw (view source holds) model ranked holds request value) :=
  SourceCurrentAllocatedNativeNodeBranches.self_law source sourceFacts holds model ranked request
    leftAvailable rightAvailable self

/-- Literal source conjunction discharges accepted code's guard truth equation. -/
theorem children_source_certified
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (literal : SourceEqualityConjoinAllocation.readback combined = SourceEqualityConstraintConstructors.conjoin
      GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified view model ranked (SourceEqualityPCSGuard.holds formulas solver)
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun _ value => EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  apply children_certified view model ranked _ request combined arity symbols _ state valid semantic
  intro term
  rw [literal]
  exact SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver _ _ term

/-- Different original arities derive the sentinel certificate without a child law. -/
theorem mismatch_certified
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (mismatch : request.left.children.length ≠ request.right.children.length)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified view model ranked holds (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ value => EdgeLaw view model ranked holds request value) :=
  sentinel_certified view model ranked holds request
    (SourceCurrentAllocatedNativeEdgeMeaning.rowAt_mismatch holds ranked.languages request.left request.right mismatch) state valid

/-- Actual source constructor rejection derives the sentinel certificate. -/
theorem rejected_certified
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (rejected : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le request.left.entry.key.constraint
      request.right.entry.key.constraint request.left.children.length request.right.children.length = .rejected)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified view model ranked (SourceEqualityPCSGuard.holds formulas solver)
      (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ value => EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request value) :=
  sentinel_certified view model ranked _ request
    (SourceCurrentAllocatedNativeEdgeMeaning.rowAt_rejected formulas solver ranked.languages request leftCached rightCached rejected) state valid

/-- The actual yielded checked prefix derives its own static semantic certificate. -/
theorem prefix_certified [DecidableEq Symbol]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (before : SourceEqualityNativeDemand.State width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard)) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (one : SourceEqualityNativeDemand.step (.edgeBody request .pure) before =
      .yielded (.code code) {before with operations := operations}) :
    Certified view model ranked (SourceEqualityPCSGuard.holds formulas solver) code before.native.machine
      (fun _ value => EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  change SourceEqualityNativeDemand.body request .pure before = _ at one
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at one
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at one; cases one
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at one; cases one
        | some first =>
            simp only [firstLoaded] at one
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at one; cases one
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at one; cases one
                | some second =>
                    simp only [secondLoaded] at one
                    have firstCached := (good.fields _ _ ready.2.1).1
                    have secondCached := (good.fields _ _ ready.2.2).1
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      firstCached first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      secondCached second secondLoaded).1
                    obtain ⟨branch, done, readback, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length
                      before.operations good.operations firstReady secondReady
                    cases branch with
                    | mismatch =>
                        simp only [SourceEqualityIntersectionEdgeAllocation.Branch.map,
                          SourceEqualityIntersectionEdgeAllocation.source, ite_eq_right matched] at readback
                        split at readback <;> cases readback
                    | rejected =>
                        simp only [done, SourceEqualityNativeDemand.sentinel] at one
                        have same := SourceEqualityNativeDemand.Control.code.inj
                          (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
                        rw [← same, SourceEqualityNativeDemand.code_bind_pure]
                        exact rejected_certified view model ranked formulas solver request firstCached secondCached
                          (SourceCurrentAllocatedNativeEdgeMeaning.rejected_source request before good.operations
                            firstCached secondCached first second firstLoaded secondLoaded done) before.native.machine good.native.machine
                    | ready combined =>
                        simp only [done] at one
                        have same := SourceEqualityNativeDemand.Control.code.inj
                          (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
                        rw [← same, SourceEqualityNativeDemand.code_bind_pure]
                        exact children_source_certified view model ranked formulas solver request combined arity symbols
                          (SourceEqualityNativeDemandAcceptedLanguage.ready_readback request before first second combined
                            good.operations firstCached secondCached arity firstLoaded secondLoaded done)
                          before.native.machine good.native.machine semantic
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel] at one
    have same := SourceEqualityNativeDemand.Control.code.inj
      (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
    rw [← same, SourceEqualityNativeDemand.code_bind_pure]
    exact mismatch_certified view model ranked (SourceEqualityPCSGuard.holds formulas solver) request arity
      before.native.machine good.native.machine

end MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
