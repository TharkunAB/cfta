import MicroCFTA.InternedNestedRootLabels
import MicroCFTA.InternedNestedCoverage

/-!
# First-run completion for nested binders with preserved root markers

Each binder body has a nullary root edge and one declared root symbol.
Nested binders use symbols distinct from their enclosing binders. The
source constructors preserve these symbols in both complete key probes.
-/
namespace MicroCFTA.InternedMarkedConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootLabels
open InternedBinderProtocol (NodeKey Reference)

/-- An active binder retains its exact probe key and the proved root marker of its depth probe. -/
structure Frame (Symbol Guard : Type) where
  marker : Symbol
  depth : Value Symbol Guard
  ordinary : Value Symbol Guard
  root : Root marker depth

/-- The pending key is the source pair of complete probe references. -/
def Frame.key (frame : Frame Symbol Guard) : NodeKey := muKey frame.depth frame.ordinary

/-- Every pending depth probe remains its original resident canonical record. -/
def FramesResident (frames : List (Frame Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ frame ∈ frames, Resident state frame.depth

/-- The static forbidden symbols include each active enclosing binder's marker. -/
def Allowed (forbidden : List Symbol) (frames : List (Frame Symbol Guard)) : Prop :=
  ∀ frame ∈ frames, frame.marker ∈ forbidden

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

mutual
/-- Root marker separation is checked directly on the finite nested source expression. -/
def Tagged (forbidden : List Symbol) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesTagged forbidden edges
  | .union members => ManyTagged forbidden members
  | .binder _ body => match body with
    | .node edges => ∃ marker, marker ∉ forbidden ∧ Marked marker edges ∧ EdgesTagged (marker :: forbidden) edges
    | _ => False
termination_by expression => sizeOf expression

/-- Every child expression uses the same enclosing root-marker restrictions. -/
def ManyTagged (forbidden : List Symbol) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Tagged forbidden first ∧ ManyTagged forbidden rest
termination_by expressions => sizeOf expressions

/-- Edge symbols are unchanged while each child checks its own nested binder markers. -/
def EdgesTagged (forbidden : List Symbol) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyTagged forbidden children ∧ EdgesTagged forbidden rest
termination_by edges => sizeOf edges
end

/-- A fresh declared marker cannot address any incomplete enclosing binder record. -/
theorem request_not_pending {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)}
    {state : State Symbol Guard} {forbidden : List Symbol}
    (context : Context frames environment state) (allowed : Allowed forbidden frames)
    (marker : Symbol) (fresh : marker ∉ forbidden) (depth ordinary : Value Symbol Guard)
    (root : Root marker depth) (resident : Resident state depth)
    (entry : Interned NodeKey) (present : state.nodes.table (muKey depth ordinary) = some entry) :
    ∃ value, state.nodeRecords (muKey depth ordinary) = some value := by
  rcases context.covered.nodes _ entry present with pending | complete
  · obtain ⟨frame, member, same⟩ := List.mem_map.mp pending
    have different : marker ≠ frame.marker := by
      intro equal
      exact fresh (equal.symm ▸ allowed frame member)
    exact False.elim ((marked_keys_different state context.facts marker frame.marker different
      depth ordinary frame.depth frame.ordinary resident (context.resident frame member) root frame.root) same.symm)
  · exact complete

end MicroCFTA.InternedMarkedConstruction
