import MicroCFTA.InternedNestedRootReferences
import MicroCFTA.InternedNestedCoverage

/-!
# Pending frames separated by retained fresh references

A source-declared unary edge retains every enclosing reference. Each pending
frame's earlier probe excludes its own fresh reservation. Thus an inner
probe that retains that reference cannot use the pending frame's key.
-/
namespace MicroCFTA.InternedRetainedConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootReferences
open InternedBinderProtocol (NodeKey Reference)

/-- A pending source frame records the absent fresh name of its earlier complete depth probe. -/
structure Frame (Symbol Guard : Type) where
  name : Reference
  depth : Value Symbol Guard
  ordinary : Value Symbol Guard
  absent : name ∉ depth.free

/-- The pending key retains both original complete source probe references. -/
def Frame.key (frame : Frame Symbol Guard) : NodeKey := muKey frame.depth frame.ordinary

/-- Later construction retains the complete canonical depth records of active frames. -/
def FramesResident (frames : List (Frame Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ frame ∈ frames, Resident state frame.depth

/-- Each active source frame's recursive reference occurs in the actual lexical input environment. -/
def Active (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard)) : Prop :=
  ∀ frame ∈ frames, .reference frame.name ∈ environment

/-- The running source context contains only available variables and the exact active pending keys. -/
structure Context (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) : Prop where
  facts : Facts state
  inputs : Values state environment
  covered : Covered (frames.map Frame.key) state
  resident : FramesResident frames state

/-- A completed source prefix transports its original inputs and active probe records. -/
theorem Context.advance {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (context : Context frames environment before)
    (verified : Verified before outcome property) (returned : outcome = .done value after)
    (covered : Covered (frames.map Frame.key) after) : Context frames environment after := by
  have facts : Facts after := by simpa only [returned, Outcome.state] using verified.facts
  have growth : Grows before after := by simpa only [returned, Outcome.state] using verified.growth
  refine ⟨facts, ?_, covered, ?_⟩
  · intro original member
    simpa only [returned, Outcome.state] using verified.available original (context.inputs original member)
  · intro frame member
    exact resident_grows before after growth frame.depth (context.resident frame member)

/-- A probe or body adds only its actual locally supplied reference to the lexical environment. -/
theorem Context.local (context : Context frames environment state) (name : Reference)
    (available : Available state (.reference name)) : Context frames (.reference name :: environment) state := by
  refine ⟨context.facts, ?_, context.covered, context.resident⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | present
  · exact available
  · exact context.inputs value present

/-- A local reference can be removed from the proof context after its callback returns. -/
theorem Context.dropLocal (context : Context frames (value :: environment) state) : Context frames environment state :=
  ⟨context.facts, fun item member => context.inputs item (List.mem_cons_of_mem _ member), context.covered, context.resident⟩

/-- Actual reservation adds exactly the new source frame and preserves all original inputs. -/
theorem Context.reserve {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)}
    {state : State Symbol Guard} (context : Context frames environment state) (frame : Frame Symbol Guard)
    (resident : Resident state frame.depth) :
    Context (frame :: frames) environment {state with nodes := (Cache.intern state.nodes frame.key).2} := by
  let allocated := {state with nodes := (Cache.intern state.nodes frame.key).2}
  have growth : Grows state allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := intern_issued_extends state.nodes frame.key context.facts.coherent.valid.2
  refine ⟨reserve_facts frame.key state context.facts, ?_, reserve_covered frame.key state context.covered, ?_⟩
  · exact fun value member => (context.inputs value member).grows state allocated growth history
  · intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact resident_grows state allocated growth _ resident
    · exact resident_grows state allocated growth selected.depth (context.resident selected member)

/-- Every enclosing lexical slot has a declared live unary edge at the binder body's root. -/
def Declared (depth : Nat) (edges : List (EdgeSyntax Symbol Guard)) : Prop :=
  ∀ index < depth, ∃ symbol constraint, .mk symbol constraint [.var (index + 1)] ∈ edges

mutual
/-- The source syntax declares direct retention of all enclosing variables at each nested binder. -/
def Retentive (depth : Nat) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesRetentive depth edges
  | .union members => ManyRetentive depth members
  | .binder _ body => match body with
    | .node edges => Declared depth edges ∧ EdgesRetentive (depth + 1) edges
    | _ => False
termination_by expression => sizeOf expression

/-- Child expressions use the same actual lexical depth. -/
def ManyRetentive (depth : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Retentive depth first ∧ ManyRetentive depth rest
termination_by expressions => sizeOf expressions

/-- Edge declarations retain the enclosing-variable requirements of all children. -/
def EdgesRetentive (depth : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyRetentive depth children ∧ EdgesRetentive depth rest
termination_by expressions => sizeOf expressions
end

/-- Retaining every active fresh name excludes the exact key of each pending ancestor. -/
theorem request_not_pending {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)}
    {state : State Symbol Guard} (context : Context frames environment state)
    (depth ordinary : Value Symbol Guard) (resident : Resident state depth)
    (retained : ∀ frame ∈ frames, frame.name ∈ depth.free)
    (entry : Interned NodeKey) (present : state.nodes.table (muKey depth ordinary) = some entry) :
    ∃ value, state.nodeRecords (muKey depth ordinary) = some value := by
  rcases context.covered.nodes _ entry present with pending | complete
  · obtain ⟨frame, member, same⟩ := List.mem_map.mp pending
    have references : frame.depth.referenceOf = depth.referenceOf ∧ frame.ordinary.referenceOf = ordinary.referenceOf := by
      simpa [Frame.key, muKey, InternedBinderProtocol.MuKey.mk.injEq] using same
    have equal := resident_reference_injective state context.facts.coherent frame.depth depth
      (context.resident frame member) resident references.1
    exact False.elim (frame.absent (equal ▸ retained frame member))
  · exact complete

end MicroCFTA.InternedRetainedConstruction
