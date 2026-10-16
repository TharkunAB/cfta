import MicroCFTA.SourceRecursiveIntersectionDomainAllocation
import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceEqualityNativeDemandTrace

/-!
# Domain allocation history through current checked instructions

Only enter changes the domain cache. Every other instruction preserves it.
Actual checked prefixes therefore retain a sequential domain allocation
history when each literal enter key belongs to the initial inventory.
This local transport does not derive enter admission for a whole query.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeDomainTrace
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel IntersectionFlatMemoKeyDomain
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocation" => SourceRecursiveIntersectionDomainAllocation.Trace
variable {width : Nat} {A : Type}

/-- Only a literal enter instruction needs an initial domain inventory entry. -/
def CodeEntered (inventory : List DomainKey) : Code Symbol Guard A → Prop
  | .enter domain left right first second _ =>
      SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
        (SourceRecursiveIntersectionControl.pair first second) ∈ inventory
  | _ => True

/-- The checked edge body allocates no intersection domain. -/
def Entered (inventory : List DomainKey) : Control A → Prop
  | .code code => CodeEntered inventory code
  | .edgeBody .. => True

private theorem native_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (admitted : CodeEntered inventory code) :
    Allocation inventory state.machine.domains
      (SourceRecursiveIntersectionNative.step emptyGuard conjoin code state).state.machine.domains := by
  cases code with
  | pure | fail | work | read | finishNode | finishEdge => exact .refl _
  | enter domain left right first second next =>
      exact .step (.refl _) _ admitted
  | optionalBinder key value next =>
      cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key value state.machine.heap <;>
        simp only [SourceRecursiveIntersectionNative.step, actual, SourceRecursiveIntersectionNative.Outcome.state] <;>
        exact .refl _
  | node request next =>
      cases selected : lookupNode width request state with
      | mk selection chosen =>
          have same : chosen.machine = state.machine := by
            simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request state
          cases selection with
          | direct actual =>
              simpa only [SourceRecursiveIntersectionNative.step, selected, SourceRecursiveIntersectionNative.Outcome.state, same]
                using (SourceRecursiveIntersectionDomainAllocation.Trace.refl (inventory := inventory) state.machine.domains)
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation after =>
                  have retained : after.machine = state.machine := by
                    have kept := SourceRecursiveIntersectionNative.demandNode_machine handle chosen
                    simpa only [demanded, same] using kept
                  cases observation <;>
                    simpa only [SourceRecursiveIntersectionNative.step, selected, demanded,
                      SourceRecursiveIntersectionNative.Outcome.state, retained]
                    using (SourceRecursiveIntersectionDomainAllocation.Trace.refl (inventory := inventory) state.machine.domains)
  | edge request next =>
      cases selected : lookupEdge width request state with
      | mk handle chosen =>
          have same : chosen.machine = state.machine := by
            simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state
          cases demanded : demandEdge handle chosen with
          | mk observation after =>
              have retained : after.machine = state.machine := by
                have kept := SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                simpa only [demanded, same] using kept
              cases observation <;>
                simpa only [SourceRecursiveIntersectionNative.step, selected, demanded,
                  SourceRecursiveIntersectionNative.Outcome.state, retained]
                using (SourceRecursiveIntersectionDomainAllocation.Trace.refl (inventory := inventory) state.machine.domains)

private theorem lift_domains (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.domains = outcome.state.machine.domains := by
  cases outcome <;> rfl

/-- One actual checked instruction extends only the literal sequential domain history. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (control : Control A) (before : Checked width)
    (admitted : Entered inventory control) :
    Allocation inventory before.native.machine.domains
      (SourceEqualityNativeDemand.step control before).state.native.machine.domains := by
  cases control with
  | edgeBody request next =>
      have retained := SourceEqualityNativeDemandOperations.body_native request next before
      simpa only [SourceEqualityNativeDemand.step, retained] using
        (SourceRecursiveIntersectionDomainAllocation.Trace.refl (inventory := inventory) before.native.machine.domains)
  | code code =>
      have native := native_step inventory SourceEqualityConstraintConstructors.top
        SourceEqualityPCSNativeEdge.conjoin code before.native admitted
      cases code with
      | edge request next =>
          cases selected : lookupEdge width request before.native with
          | mk handle chosen =>
              have same : chosen.machine = before.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
              cases demanded : demandEdge handle chosen with
              | mk observation after =>
                  have retained : after.machine = before.native.machine := by
                    have kept := SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                    simpa only [demanded, same] using kept
                  cases observation <;>
                    simpa only [SourceEqualityNativeDemand.step, selected, demanded,
                      SourceEqualityNativeDemand.Outcome.state, retained] using
                      (SourceRecursiveIntersectionDomainAllocation.Trace.refl (inventory := inventory) before.native.machine.domains)
      | _ =>
          simpa only [SourceEqualityNativeDemand.step, lift_domains] using
            native

/-- An admitted yielded instruction retains the allocation history at the exact returned state. -/
theorem yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (control next : Control A) (before after : Checked width)
    (admitted : Entered inventory control)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after) :
    Allocation inventory before.native.machine.domains after.native.machine.domains := by
  have actual := step inventory control before admitted
  simpa only [one, SourceEqualityNativeDemand.Outcome.state] using actual

/-- Enter admission is explicit over raw prefixes until the source certificate derives it. -/
def Prefixes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (control : Control A) (before : Checked width) : Prop :=
  ∀ fuel next after, Steps fuel control before next after → Entered inventory next

/-- Zero yielded steps retain the current enter admission. -/
theorem Prefixes.current [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : List DomainKey} {control : Control A} {before : Checked width}
    (admitted : Prefixes inventory control before) : Entered inventory control :=
  admitted 0 control before (.refl _ _)

/-- A literal yielded step retains the remaining raw-prefix admission. -/
theorem Prefixes.after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : List DomainKey} {control next : Control A} {before after : Checked width}
    (admitted : Prefixes inventory control before)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after) :
    Prefixes inventory next after := by
  intro fuel final result rest
  exact admitted (fuel + 1) final result (.cons _ _ _ _ _ _ _ one rest)

/-- Every admitted raw checked prefix derives its actual sequential domain allocation history. -/
theorem trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (fuel : Nat) (control next : Control A) (before after : Checked width)
    (actual : Steps fuel control before next after) (admitted : Prefixes inventory control before) :
    Allocation inventory before.native.machine.domains after.native.machine.domains := by
  induction actual with
  | refl => exact .refl _
  | cons control before middle current final result fuel one rest ih =>
      exact (yielded inventory control middle before current admitted.current one).trans
        (ih (admitted.after_step one))

/-- Domain cache supply is bounded independently of the number of admitted repeated enters. -/
theorem next_le [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (fuel : Nat) (control next : Control A) (before after : Checked width)
    (actual : Steps fuel control before next after) (admitted : Prefixes inventory control before) :
    after.native.machine.domains.next ≤ before.native.machine.domains.next + inventory.length :=
  (trace inventory fuel control next before after actual admitted).next_le

/-- Actual prefix history and initial headroom bound every represented shifted domain identity. -/
theorem identity_lt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inventory : List DomainKey) (fuel : Nat) (control next : Control A) (before after : Checked width)
    (actual : Steps fuel control before next after) (admitted : Prefixes inventory control before)
    (valid : Cache.Valid before.native.machine.domains)
    (key : DomainKey) (domain : Interned DomainKey)
    (represented : IntersectionEmptyDomain.Represents after.native.machine.domains key domain)
    (limit : Nat) (room : before.native.machine.domains.next + inventory.length < limit) :
    domain.identity < limit :=
  (trace inventory fuel control next before after actual admitted).identity_lt valid represented room

end MicroCFTA.SourceCurrentAllocatedNativeDomainTrace
