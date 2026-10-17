import MicroCFTA.SourceRecursiveIntersectionCodeMass
import MicroCFTA.SourceEqualityNativeCheckedMass

/-!
# Initial width certificates for actual checked edge code

The original resident row bounds the ordered child zip. Every recursive
continuation accepts each larger causal store at its actual returned heap.
The walk retains the original count and current physical availability.
No completed child walk or future store certificate is a public premise.
Checked equality operations change no native machine in the body prefix.
-/
namespace MicroCFTA.SourceEqualityNativeCheckedWidth
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCodeMass (At)
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Initial resident operands certify the accepted ordered child code at every later causal bound. -/
theorem children_at [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint Formula)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right) :
    At (SourceEqualityNativeCheckedCode.children domain left right combined) state bound
      (fun after edge => EdgeResident after.heap edge) := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have walked := SourceRecursiveIntersectionCodeMass.walk
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode domain pair.1 pair.2)
    (left.children.zip right.children) input (fun after value => Available after.heap value)
    (by
      intro before after growth pair current
      exact ⟨current.1.grows domain growth, growth.available _ current.2.1, growth.available _ current.2.2⟩)
    available_stable
    (by
      intro pair _ current currentBound _ _ inputs
      exact SourceRecursiveIntersectionCodeMass.request_node domain pair.1 pair.2 current currentBound inputs)
    state bound valid stored (by
      intro pair member
      have inside := List.of_mem_zip member
      exact ⟨known, valid.1.cached.edges _ _ leftResident _ inside.1,
        valid.1.cached.edges _ _ rightResident _ inside.2⟩)
  unfold SourceEqualityNativeCheckedCode.children
  apply SourceRecursiveIntersectionCodeMass.bind _ _ state bound valid stored _ _ walked
  intro values after larger afterValid _ increase current outputs
  apply SourceRecursiveIntersectionCodeMass.edge _ _ values after larger afterValid outputs.2
  have original := SourceEqualityNativeCheckedMass.zip_width state.heap bound stored left right leftResident
  have square := Nat.mul_le_mul_left larger current.positive
  simp only [Nat.mul_one] at square
  rw [outputs.1]
  exact Nat.le_trans original (Nat.le_trans increase square)

/-- Initial store positivity certifies the literal rejected code without a recursive callback. -/
theorem sentinel_at [DecidableEq (EdgeKey Symbol Guard)] (left : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) :
    At (SourceEqualityNativeCheckedCode.sentinel left) state bound (fun after edge => EdgeResident after.heap edge) := by
  apply SourceRecursiveIntersectionCodeMass.edge _ _ [.empty] state bound valid
  · intro value member
    cases List.mem_singleton.mp member
    exact empty_available _
  · have square := Nat.mul_le_mul_left bound stored.positive
    simp only [Nat.mul_one] at square
    exact Nat.le_trans stored.positive square

section Current
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- The actual checked body yield certifies its chosen code at the exact returned native machine. -/
theorem body_at [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before after : Checked width)
    (code : Code SourceSymbol SourceGuard (EdgeValue SourceSymbol SourceGuard))
    (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (stored : Stored bound before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    At code after.native.machine bound (fun final edge => EdgeResident final.heap edge) := by
  obtain ⟨same, choice⟩ := SourceEqualityNativeCheckedMass.body_choice request before after code yielded
  rw [same]
  rcases choice with rfl | ⟨combined, _arity, rfl⟩
  · exact sentinel_at request.left before.native.machine bound valid stored
  · exact children_at request.domain request.left request.right combined before.native.machine bound valid stored
      ready.1 ready.2.1 ready.2.2

/-- Literal body continuation binding retains the chosen operation state and every larger causal return. -/
theorem body_bind_at [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before after : Checked width)
    (code : Code SourceSymbol SourceGuard (EdgeValue SourceSymbol SourceGuard))
    (next : EdgeValue SourceSymbol SourceGuard → Code SourceSymbol SourceGuard Output)
    (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (stored : Stored bound before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after)
    (post : Machine SourceSymbol SourceGuard → Output → Prop)
    (continuation : ∀ value final larger, SourceRecursiveIntersectionKernel.Valid final →
      Extension before.native.machine final → bound ≤ larger → Stored larger final.heap →
      EdgeResident final.heap value → At (next value) final larger post) :
    SourceEqualityNativeDemand.body request next before = .yielded (.code (code.bind next)) after ∧
      At (code.bind next) after.native.machine bound post := by
  classical
  have same := (SourceEqualityNativeCheckedMass.body_choice request before after code yielded).1
  have certificate := body_at request before after code bound valid stored ready yielded
  refine ⟨?_, ?_⟩
  · have appended := SourceEqualityNativeDemand.body_bind request .pure next before
    simpa only [Code.bind, yielded, SourceEqualityNativeDemand.appendStep,
      SourceEqualityNativeDemand.Control.bind] using appended
  · apply SourceRecursiveIntersectionCodeMass.bind code next after.native.machine bound
      (by simpa only [same] using valid) (by simpa only [same] using stored) _ post certificate
    intro value final larger finalValid growth increase current resident
    exact continuation value final larger finalValid (by simpa only [same] using growth) increase current resident
end Current
end MicroCFTA.SourceEqualityNativeCheckedWidth
