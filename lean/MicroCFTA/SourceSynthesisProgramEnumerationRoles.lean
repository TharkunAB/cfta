import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.EnumerationReferences

/-!
# Program roles in raw enumeration slots

The predicates refer to the existing Fragment syntax and raw UVar slots.
Type children remain unrestricted. Native handles do not determine Program roles.
Safety and fragment dependency levels remain in the existing execution Packet.
-/
namespace MicroCFTA.SourceSynthesisProgramEnumerationRoles
open Fragments EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Program positions retain their literal layouts or a marked raw occurrence. -/
inductive FragmentRoles (literal : String → Symbol) (marked : Nat → Prop) : Fragment Symbol → Prop where
  | hole (uv : Nat) (known : marked uv) : FragmentRoles literal marked (.hole uv)
  | component (symbol : Symbol) (annotation : Fragment Symbol) :
      FragmentRoles literal marked (.node symbol [annotation])
  | application (annotation marker function argument : Fragment Symbol)
      (first : FragmentRoles literal marked function)
      (second : FragmentRoles literal marked argument) :
      FragmentRoles literal marked (.node (literal "app") [annotation, marker, function, argument])
  | filter (goal candidates : Fragment Symbol) (body : FragmentRoles literal marked candidates) :
      FragmentRoles literal marked (.node (literal "filter") [goal, candidates])

/-- A stored Program payload has actual native fields or an enumerated Program fragment. -/
inductive SlotRole (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (marked : Nat → Prop) : UVarValue Symbol → Prop where
  | pending (handle : Nat) (scs : List Suspended) (value : Node)
      (decoded : lookupNode heap handle = some value) (fields : ValueFields valid literal value)
      (validTries : EnumerationSemantics.ValidSuspended scs)
      (annotationPaths : SourcePruningEnumerationPathTransport.BucketPaths
        SourceSynthesisGuardRegions.annotationRegion scs) :
      SlotRole valid literal heap marked (.unenumerated (some handle) scs)
  | enumerated (fragment : Fragment Symbol) (roles : FragmentRoles literal marked fragment) :
      SlotRole valid literal heap marked (.enumerated fragment)

/-- Marked raw occurrences remain live roots with protected references and actual payloads. -/
structure ProgramSlots (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (state : Core) (marked : Nat → Prop) : Prop where
  /-- Each marked raw occurrence belongs to the allocated slot domain. -/
  bounded : ∀ uv, marked uv → uv < state.counter
  /-- Each marked raw occurrence remains its own representative. -/
  roots : ∀ uv, marked uv → IsRoot state.representatives uv
  /-- Stored equality references avoid every marked Program class. -/
  incoming : ∀ uv, marked uv → EnumerationReferences.IncomingAvoid uv state
  /-- The exact raw slot contains a permitted Program payload. -/
  stored : ∀ uv, marked uv → ∃ payload,
    state.values[uv]? = some payload ∧ SlotRole valid literal heap marked payload

variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- Literal raw initialization marks slot zero with its same native Program readback. -/
theorem initial_program_slots
    (heap : NativeHeap) (handle : Nat) (value : Node)
    (decoded : lookupNode heap handle = some value)
    (fields : ValueFields valid literal value) :
    ProgramSlots valid literal heap (EnumerationState.initial handle) (fun uv => uv = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv marked
    subst uv
    exact Nat.zero_lt_succ 0
  · intro uv marked
    subst uv
    exact ⟨1, .root (UnionFind.read_initial [0] 0)⟩
  · intro uv _marked payload member sc listed
    have same : payload = .unenumerated (some handle) [] := by
      simpa only [EnumerationState.initial, List.mem_singleton] using member
    subst payload
    cases listed
  · intro uv marked
    subst uv
    refine ⟨.unenumerated (some handle) [], rfl, ?_⟩
    exact .pending handle [] value decoded fields
      (by intro sc member; cases member)
      (by intro sc member; cases member)

end MicroCFTA.SourceSynthesisProgramEnumerationRoles
