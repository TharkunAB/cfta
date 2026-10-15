import MicroCFTA.SourceEqualityNativeDemandTrace
import MicroCFTA.SourceEqualityNativeDemandProvenance
import MicroCFTA.SourceEqualityNativeDemandWalkExecution

/-!
# Actual ordered checked child calls

Each child call retains its actual finite trace and returned checked state.
Its proved physical effects and node receipt form the recursive induction
hypothesis. The ordered fold derives final available children and language
receipts. It does not assume a future parent result or replay child effects.
-/
namespace MicroCFTA.SourceEqualityNativeDemandChildWalk
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
variable {width : Nat}

/-- An ordered child fold records actual calls and the proved receipts of those calls. -/
inductive Walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    List Pair → State width → List (Value Symbol Guard) → State width → Nat → Prop where
  | nil (state) : Walk holds domain [] state [] state 0
  | cons (pair : Pair) (rest) (before middle after : State width) (value values firstFuel restFuel)
      (called : Steps firstFuel (.code (requestNode domain pair.1 pair.2)) before (.code (.pure value)) middle)
      (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
      (growth : Extension before.native.machine middle.native.machine)
      (produced : NodeProduced (width := width) holds middle.native.machine ⟨domain, pair.1, pair.2⟩ value)
      (tail : Walk holds domain rest middle values after restFuel) :
      Walk holds domain (pair :: rest) before (value :: values) after (firstFuel + restFuel)

/-- Actual child traces compose to the exact emitted ordered source walk. -/
theorem Walk.trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey}
    {pairs : List Pair} {before after : State width} {values : List (Value Symbol Guard)} {fuel : Nat}
    (walk : Walk holds domain pairs before values after fuel) :
    Steps fuel (.code (SourceRecursiveIntersectionCode.walk (fun pair => requestNode domain pair.1 pair.2) pairs)) before
      (.code (.pure values)) after := by
  induction walk with
  | nil state => exact .refl _ _
  | cons pair rest before middle after value values firstFuel restFuel called keeps growth produced tail ih =>
      let next := fun value => (SourceRecursiveIntersectionCode.walk (fun pair => requestNode domain pair.1 pair.2) rest).bind
        fun values => .pure (value :: values)
      have first := called.bind _ _ _ _ _ next
      have second := ih.bind _ _ _ _ _ (fun values => .pure (value :: values))
      exact first.trans _ _ _ _ _ _ _ _ second

/-- The actual ordered fold derives all physical histories and final child-language receipts. -/
theorem Walk.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey}
    {pairs : List Pair} {before after : State width} {values : List (Value Symbol Guard)} {fuel : Nat}
    (walk : Walk holds domain pairs before values after fuel)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap) :
    SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      InternedNestedProvenance.Values after.native.machine.heap values ∧
      Language.All₂ (fun pair value => NodeMeaning holds ⟨domain, pair.1, pair.2⟩ value) pairs values := by
  induction walk with
  | nil state =>
      exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready, Extension.refl _,
        (by intro value member; cases member), .nil⟩
  | cons pair rest before middle after value values firstFuel restFuel called keeps growth produced tail ih =>
      have later := ih keeps.ready
      refine ⟨keeps.trans later.1, growth.trans later.2.1, ?_, .cons produced.spec.2.2 later.2.2.2⟩
      intro child member
      cases member with
      | head => exact later.2.1.available value produced.spec.2.1
      | tail _ member => exact later.2.2.1 child member

/-- The ordered actual child fold retains one returned value per original pair. -/
theorem Walk.length [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey}
    {pairs : List Pair} {before after : State width} {values : List (Value Symbol Guard)} {fuel : Nat}
    (walk : Walk holds domain pairs before values after fuel) : values.length = pairs.length := by
  induction walk with
  | nil => rfl
  | cons pair rest before middle after value values firstFuel restFuel called keeps growth produced tail ih =>
      exact congrArg Nat.succ ih

/-- Only the child calls in this actual ordered execution require physical and language receipts. -/
inductive Checks [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    {pairs : List Pair} → {before after : State width} → {values : List (Value Symbol Guard)} → {fuel : Nat} →
    SourceEqualityNativeDemandWalkExecution.Walk (fun pair : Pair => requestNode domain pair.1 pair.2)
      pairs before values after fuel → Prop where
  | nil (state) : Checks holds domain (.nil state)
  | cons (pair : Pair) (rest) (before middle after : State width) (value values firstFuel restFuel)
      (called : Steps firstFuel (.code (requestNode domain pair.1 pair.2)) before (.code (.pure value)) middle)
      (tail : SourceEqualityNativeDemandWalkExecution.Walk (fun pair : Pair => requestNode domain pair.1 pair.2)
        rest middle values after restFuel)
      (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
      (growth : Extension before.native.machine middle.native.machine)
      (produced : NodeProduced (width := width) holds middle.native.machine ⟨domain, pair.1, pair.2⟩ value)
      (checked : Checks holds domain tail) :
      Checks holds domain (.cons pair rest before middle after value values firstFuel restFuel called tail)

/-- Actual child traces acquire receipts from checks at their exact reached states. -/
theorem certify [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List Pair) (before after : State width) (values : List (Value Symbol Guard)) (fuel : Nat)
    (walk : SourceEqualityNativeDemandWalkExecution.Walk (fun pair : Pair => requestNode domain pair.1 pair.2)
      pairs before values after fuel)
    (calls : Checks holds domain walk) :
    Walk holds domain pairs before values after fuel := by
  induction calls with
  | nil state => exact .nil state
  | cons pair rest before middle after value values firstFuel restFuel called tail keeps growth produced checked ih =>
      exact .cons pair rest before middle after value values firstFuel restFuel called keeps growth produced ih

end MicroCFTA.SourceEqualityNativeDemandChildWalk
