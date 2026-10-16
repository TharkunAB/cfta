import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputEdge

/-!
# Hereditary guard certificates for actual native source bodies

Each recursive request combines two original bounded guards once.
The accepted edge root uses the actual loaded conjunction readback.
Children use the same common step at every depth. Rejected code uses Top.
These local certificates do not assert native completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardBody
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryGuardCode SourceCurrentAllocatedFiniteOrdinaryGuardStored
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "RowsProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "guardStep" => SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem edge_walk
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (known : ∀ pair ∈ pairs, EdgeInputs ⟨domain, pair.1, pair.2⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceRecursiveIntersectionCode.walk (fun pair => requestEdge domain pair.1 pair.2) pairs) state
      (fun after values => InternedNestedProvenance.Edges after.heap values ∧
        Language.All₂ (fun pair value => EdgeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values) := by
  induction pairs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), .nil⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, requestEdge, Code.bind, Certified]
      refine ⟨known first List.mem_cons_self, ?_⟩
      intro value middle middleValid growth middleSemantic resident law
      apply certified_bind _ _ middle middleValid middleSemantic _ _
        (ih (fun pair member => known pair (List.mem_cons_of_mem _ member)) middle middleValid middleSemantic)
      intro values after _ later _ tail
      exact ⟨by intro edge member; cases member with
        | head => exact edge_grows _ _ later.heap value resident
        | tail _ member => exact tail.1 edge member, .cons law tail.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem paired_rows
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (limits : Limits) (left right : List (EdgeValue Symbol Guard))
    (leftShape : RowsProfile limits left) (rightShape : RowsProfile limits right)
    (pairs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (inside : ∀ pair ∈ pairs, pair.1 ∈ left ∧ pair.2 ∈ right)
    (values : List (EdgeValue Symbol Guard))
    (laws : Language.All₂ (fun pair value => EdgeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values) :
    RowsProfile (guardStep limits) values := by
  induction laws with
  | nil => trivial
  | @cons pair value pairs values law tail ih =>
      have members := inside pair List.mem_cons_self
      exact ⟨law seen limits
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows.member left leftShape _ members.1)
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows.member right rightShape _ members.2),
        ih (fun pair member => inside pair (List.mem_cons_of_mem _ member))⟩

/-- The literal join and node constructor retain every descendant guard bound. -/
theorem rows_certified
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard))
    (leftDepth : Nat) (leftFree : List InternedBinderProtocol.Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard))
    (rightDepth : Nat) (rightFree : List InternedBinderProtocol.Reference)
    (leftDomain : DRows left) (rightDomain : DRows right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (compileRows domain left right) state
      (fun _ value => NodeCertificate
        ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩ value) := by
  unfold compileRows
  apply certified_bind _ _ state valid semantic _ _
    (edge_walk domain (pairs left right) (fun pair member => by
      have inside := (pairs_member left right pair).mp member
      exact ⟨seen, leftDomain.member pair.1 inside.1, rightDomain.member pair.2 inside.2.1⟩)
      state valid semantic)
  intro values middle middleValid _ _ paired
  intro value after done _inputs _afterValid _later _afterSemantic
  rw [(work_done _ middle value after done).1]
  intro _ limits leftShape rightShape
  apply SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeNode values middle.heap
    middleValid.1.coherent middleValid.1.linked paired.1
  exact paired_rows domain seen limits left right leftShape rightShape (pairs left right)
    (fun pair member => by
      have inside := (pairs_member left right pair).mp member
      exact ⟨inside.1, inside.2.1⟩) values paired.2

/-- The actual dispatcher derives conditional guard certificates for every supported branch. -/
theorem node_certified
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (leftAvailable : Available state.heap request.left) (rightAvailable : Available state.heap request.right)
    (inputs : NodeInputs request) :
    Certified (compileNode request) state (fun _ value => NodeCertificate request value) := by
  rcases request with ⟨domain, left, right⟩
  rcases inputs with ⟨seen, leftDomain, rightDomain⟩
  change domain.key.seen = [] at seen
  by_cases emptyCase : SourceRecursiveIntersectionControl.hasEmpty left right = true
  · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, ite_true]
    exact fun _ _ _ _ => trivial
  · by_cases resetCase : SourceRecursiveIntersectionControl.reset domain.key left right = true
    · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, Bool.false_eq_true, ite_false, ite_true]
      refine ⟨⟨rfl, leftDomain, rightDomain⟩, ?_⟩
      intro value after _ _ _ _ law _ limits leftShape rightShape
      exact law rfl limits leftShape rightShape
    · by_cases selfCase : SourceRecursiveIntersectionControl.closedSelf left right = true
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, Bool.false_eq_true, ite_false, ite_true]
        have same := SourceRecursiveIntersectionControl.self_record state.heap valid.1 left right
          leftAvailable rightAvailable selfCase
        intro _ limits _ rightShape
        rw [same]
        exact SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono right rightShape
          (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step_ge limits)
      · by_cases swapCase : SourceRecursiveIntersectionControl.greater left right = true
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false, ite_true]
          refine ⟨⟨seen, rightDomain, leftDomain⟩, ?_⟩
          intro value after _ _ _ _ law seenEmpty limits leftShape rightShape
          exact law seenEmpty limits rightShape leftShape
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false]
          cases leftDomain with
          | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
          | @ordinary left first leftDepth leftFree leftRows =>
            cases rightDomain with
            | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
            | @ordinary right second rightDepth rightFree rightRows =>
              simpa only [SourceRecursiveIntersectionControl.identity, seen, List.not_mem_nil,
                Bool.false_eq_true, ite_false, SourceRecursiveIntersectionControl.payload] using
                rows_certified domain seen first left leftDepth leftFree second right rightDepth rightFree
                  leftRows rightRows state valid semantic

local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "NodeProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "EdgeProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "ChildrenProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem child_list
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (limits : Limits) {pairs : List (Node × Node)} {values : List Node}
    (actual : Language.All₂ (fun pair value => NodeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values)
    (profiles : ∀ pair ∈ pairs, NodeProfile limits pair.1 ∧ NodeProfile limits pair.2) :
    ChildrenProfile (guardStep limits) values := by
  induction actual with
  | nil => trivial
  | @cons pair value pairs values first rest ih =>
      have inputs := profiles pair List.mem_cons_self
      exact ⟨first seen limits inputs.1 inputs.2,
        ih (fun pair member => profiles pair (List.mem_cons_of_mem _ member))⟩

omit [DecidableEq Symbol] in
private theorem walk_receipt (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List (Node × Node)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (inputs : ∀ pair ∈ pairs, NodeInputs ⟨domain, pair.1, pair.2⟩) :
    Certified (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) state
      (fun after values => Language.All₂ (fun pair value => NodeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values ∧
        ∀ value ∈ values, Available after.heap value) := by
  induction pairs generalizing state with
  | nil => exact ⟨.nil, fun _ absent => nomatch absent⟩
  | cons pair pairs ih =>
      change NodeInputs ⟨domain, pair.1, pair.2⟩ ∧ _
      refine ⟨inputs pair List.mem_cons_self, ?_⟩
      intro result middle middleValid _ middleSemantic available certificate
      apply certified_bind (walk (fun pair : Node × Node => requestNode domain pair.1 pair.2) pairs) _
        middle middleValid middleSemantic _ _
        (ih middle middleValid middleSemantic (fun pair member => inputs pair (List.mem_cons_of_mem _ member)))
      intro results after _ growth _ tail
      refine ⟨.cons certificate tail.1, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact growth.available result available
      · exact tail.2 value later

omit [DecidableEq Symbol] in
private theorem edge_work (request : EdgeRequest Symbol Guard) (symbol : Symbol) (guard : Guard)
    (values : List Node) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value)
    (shaped : ∀ limits, EdgeProfile limits request.left → EdgeProfile limits request.right →
      SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds (guardStep limits) guard ∧
      ChildrenProfile (guardStep limits) values) :
    Certified (.work (makeEdge symbol guard values) .pure) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  intro result after done _ _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state result after done
  refine ⟨?_, (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl⟩
  intro _ limits leftShape rightShape
  have output := shaped limits leftShape rightShape
  exact SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeEdge symbol guard values state.heap
    valid.1.coherent valid.1.cached available output.1 output.2

omit [DecidableEq Symbol] in
private theorem children_receipt (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (literal : SourceEqualityConjoinAllocation.readback combined = SourceEqualityConstraintConstructors.conjoin
      GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  have calls : ∀ pair ∈ request.left.children.zip request.right.children,
      NodeInputs ⟨request.domain, pair.1, pair.2⟩ := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨inputs.1, inputs.2.1.member pair.1 inside.1, inputs.2.2.member pair.2 inside.2⟩
  have children := walk_receipt request.domain (request.left.children.zip request.right.children)
    state valid semantic calls
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind _ _ state valid semantic _ _ children
  intro values after afterValid _ _ actual
  apply edge_work request request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
    values after afterValid actual.2
  intro limits leftShape rightShape
  constructor
  · rw [literal]
    exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.conjoin_step GuardStructuralOrder.le _ _ limits
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard _ leftShape)
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard _ rightShape)
  · apply child_list request.domain inputs.1 limits actual.1
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member _
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children _ leftShape) _ inside.1,
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member _
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children _ rightShape) _ inside.2⟩

omit [DecidableEq Symbol] in
private theorem sentinel_receipt (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun after result => EdgeCertificate request result ∧ EdgeResident after.heap result) := by
  apply edge_work request request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] state valid
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact empty_available _
  · intro limits _ _
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardLimits.top_bounds _, trivial, trivial⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Every actual checked body yield emits code at its returned operation state. -/
theorem body_yielded_code {width : Nat} {Output : Type}
    (request : EdgeRequest Symbol Guard) (next : Edge → Code Symbol Guard Output)
    (before after : Checked width) (rest : SourceEqualityNativeDemand.Control Output)
    (yielded : SourceEqualityNativeDemand.body request next before = .yielded rest after) :
    ∃ code, rest = .code code :=
  SourceCurrentAllocatedFiniteOrdinaryOutputEdge.body_yielded_code request next before after rest yielded

omit [DecidableEq Symbol] in
/-- The actual checked prefix derives its literal root conjunction before certifying child code. -/
theorem body_certified {width : Nat} {Output : Type}
    (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (before after : Checked width) (next : Edge → Code Symbol Guard Output) (rest : Code Symbol Guard Output)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request next before = .yielded (.code rest) after)
    (post : Machine Symbol Guard → Output → Prop)
    (continuation : ∀ result final, SourceRecursiveIntersectionKernel.Valid final →
      Extension before.native.machine final → SemanticReady final.heap → EdgeResident final.heap result →
      EdgeCertificate request result → Certified (next result) final post) :
    Certified rest after.native.machine post := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request next before
  rw [same]
  have bindCode : ∀ code, Certified code before.native.machine
      (fun final result => EdgeCertificate request result ∧ EdgeResident final.heap result) →
      Certified (code.bind next) before.native.machine post := by
    intro code certificate
    exact certified_bind code next before.native.machine good.native.machine semantic _ post certificate
      (fun result final valid growth current receipt => continuation result final valid growth current receipt.2 receipt.1)
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    have firstCached := (good.fields _ _ ready.2.1).1
                    have secondCached := (good.fields _ _ ready.2.2).1
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      firstCached first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      secondCached second secondLoaded).1
                    obtain ⟨branch, done, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length
                      before.operations good.operations firstReady secondReady
                    cases branch with
                    | mismatch | rejected =>
                        simp only [done, SourceEqualityNativeDemand.sentinel] at yielded
                        have codeSame := SourceEqualityNativeDemand.Control.code.inj
                          (SourceEqualityNativeDemand.Outcome.yielded.inj yielded).1
                        rw [← codeSame]
                        exact bindCode _ (sentinel_receipt request _ good.native.machine)
                    | ready combined =>
                        simp only [done] at yielded
                        have codeSame := SourceEqualityNativeDemand.Control.code.inj
                          (SourceEqualityNativeDemand.Outcome.yielded.inj yielded).1
                        rw [← codeSame]
                        exact bindCode _ (children_receipt request inputs combined
                          (SourceEqualityNativeDemandAcceptedLanguage.ready_readback request before first second combined
                            good.operations firstCached secondCached arity firstLoaded secondLoaded done)
                          _ good.native.machine semantic)
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel] at yielded
    have codeSame := SourceEqualityNativeDemand.Control.code.inj
      (SourceEqualityNativeDemand.Outcome.yielded.inj yielded).1
    rw [← codeSame]
    exact bindCode _ (sentinel_receipt request _ good.native.machine)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardBody
