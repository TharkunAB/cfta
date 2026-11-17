/- OPEN HEADER ONLY. No proof or theorem credit.
This is a source request-admission target at a literal checked node cut.
It does not assume a child result law or a future source invariant.
-/
import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
import MicroCFTA.SourceCurrentNativeConsistentOptionalOwner
import MicroCFTA.SourceEqualityNativeDemandBodyYield
import MicroCFTA.SourceSynthesisCurrentUniverseBodyMatchedPairs

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Actual source call admission]
Query results do not become operands of later compiled queries.
The compiler uses original operands, actual source reads and entered domains.
The carrier checks those calls and their literal continuations only.
Enter and read obligations use actual rooted prefixes within the fixed trace.
The carrier does not assume a result law or an optional body invariant.
-/
private def NodeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : NodeRequest Symbol Guard) : Prop :=
  Qualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request ∨
    ∃ (fullPattern : Value Symbol Guard) (patternId : Nat)
      (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntry (width := width) rootRequest machine operations wholeCount
        entry body depth ordinary fullPattern patternId originalDomain ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let e := SourceRecursiveIntersectionControl.pair bodyId entry.identity
      let d := SourceRecursiveIntersectionControl.pair entry.identity entry.identity
      let bodyFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] e
      let diagonalFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] d
      let bodyTerminal := SourceRecursiveIntersectionDomain.extend bodyFirst [entry.identity] d
      let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity] e
      (request.domain.key = bodyFirst ∧
        ((request.left = body ∧ request.right = body) ∨
         (request.left = referenceValue ∧ request.right = referenceValue) ∨
         (request.left = universeValue ∧ request.right = referenceValue))) ∨
      (request.domain.key = bodyTerminal ∧ request.left = body ∧ request.right = referenceValue) ∨
      (request.domain.key = diagonalFirst ∧
        ((request.left = body ∧ request.right = referenceValue) ∨
         (request.left = body ∧ request.right = universeValue))) ∨
      (request.domain.key = diagonalTerminal ∧
        ((request.left = body ∧ request.right = body) ∨
         (request.left = referenceValue ∧ request.right = referenceValue) ∨
         (request.left = universeValue ∧ request.right = referenceValue)))

private def EdgeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : EdgeRequest Symbol Guard) : Prop :=
  request.left.children.length = request.right.children.length →
    ∀ children ∈ request.left.children.zip request.right.children,
      NodeAdmission (width := width) rootRequest machine operations wholeCount
        entry body depth ordinary bodyId ⟨request.domain, children.1, children.2⟩

private def CodeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {A : Type}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat) :
    Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work _ next | .optionalBinder _ _ next =>
      ∀ value, CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId (next value)
  | .node request next =>
      NodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId (next value)
  | .edge request next =>
      EdgeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId (next value)
  | .enter domain left right first second next =>
      ∀ (used : Nat) (before : Checked width)
        (actualNext : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard)),
        used + 1 ≤ wholeCount →
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width)
          (.code (.enter domain left right first second actualNext)) before →
        let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
          domain.key left right first second
        let after : Checked width :=
          {before with native := advance before.native {before.native.machine with domains := entered.2}}
        Trace 1 (.code (.enter domain left right first second actualNext)) before
          (.code (actualNext entered.1)) after →
        CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId (next entered.1)
  | .read name next =>
      ∀ (used : Nat) (before : Checked width)
        (actualNext : Option (Value Symbol Guard) → Code Symbol Guard (Value Symbol Guard)),
        used + 1 ≤ wholeCount →
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width)
          (.code (.read name actualNext)) before →
        CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId
          (next (SourcePreparedSharedRows.read before.native.machine.heap name))
  | .finishNode _ _ next | .finishEdge _ _ next =>
      CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId next

private def ControlAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat) :
    Control (Value Symbol Guard) → Prop
  | .code code => CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId code
  | .edgeBody request next =>
      EdgeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId (next value)

section CarrierProofs
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
  (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)

private theorem code_admission_bind {A B : Type}
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (original : CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId code)
    (continuation : ∀ value, CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId (next value)) :
    CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih | optionalBinder key value resume ih =>
      intro result
      exact ih result (original result)
  | node request resume ih | edge request resume ih =>
      refine ⟨original.1, ?_⟩
      intro result
      exact ih result (original.2 result)
  | enter domain left right first second resume ih =>
      intro used before actualNext within actual
      dsimp only
      intro one
      exact ih _ (original used before actualNext within actual one)
  | read name resume ih =>
      intro used before actualNext within actual
      exact ih _ (original used before actualNext within actual)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih original

private theorem code_admission_walk {A B : Type}
    (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId (call value)) :
    CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
      · exact calls first List.mem_cons_self
      · intro value
        apply code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
        · exact ih (fun member included => calls member (List.mem_cons_of_mem first included))
        · intro values
          trivial

private theorem checked_children_admission
    (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (admitted : EdgeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId request)
    (arity : request.left.children.length = request.right.children.length) :
    CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  unfold SourceEqualityNativeCheckedCode.children
  apply code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
  · apply code_admission_walk rootRequest machine operations wholeCount entry body depth ordinary bodyId
    intro children included
    exact ⟨admitted arity children included, fun _ => trivial⟩
  · intro values row
    trivial

private theorem checked_sentinel_admission (row : EdgeValue Symbol Guard) :
    CodeAdmission (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId
      (SourceEqualityNativeCheckedCode.sentinel row) := by
  intro value
  trivial

private theorem checked_body_yield_admission {A : Type}
    (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (control : Control A)
    (admitted : EdgeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId request)
    (continuation : ∀ row, CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId (next row))
    (one : SourceEqualityNativeDemand.body request next before = .yielded control after) :
    ∃ code, control = .code code ∧ CodeAdmission (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary bodyId code := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · cases one
    refine ⟨_, rfl, ?_⟩
    exact code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
      _ next (checked_sentinel_admission rootRequest machine operations wholeCount
        entry body depth ordinary bodyId request.left) continuation
  · rename_i sameArity
    have arity : request.left.children.length = request.right.children.length := Classical.not_not.mp sameArity
    split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
            _ next (checked_sentinel_admission rootRequest machine operations wholeCount
              entry body depth ordinary bodyId request.left) continuation
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
            _ next (checked_sentinel_admission rootRequest machine operations wholeCount
              entry body depth ordinary bodyId request.left) continuation
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest machine operations wholeCount entry body depth ordinary bodyId
            _ next (checked_children_admission rootRequest machine operations wholeCount
              entry body depth ordinary bodyId request _ admitted arity) continuation
end CarrierProofs

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
#check NodeAdmission
#check EdgeAdmission
#check CodeAdmission
#check ControlAdmission
#print axioms code_admission_bind
#print axioms code_admission_walk
#print axioms checked_children_admission
#print axioms checked_sentinel_admission
#print axioms checked_body_yield_admission
end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
