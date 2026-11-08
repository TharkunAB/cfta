import MicroCFTA.SourceSynthesisProgramChildEntry

/-!
# Scoped prefixes of the actual ordered child walk

Each prefix starts at the current row's child list and index zero. A step
records the exact completed earlier node call. The next child need not
complete. Position and outer reachability follow from these witnesses.
Arbitrary reached-phase completeness, caller role history, Type progress,
and the original-request total bound remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisProgramWalkPrefix
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceSynthesisGuardRegions (annotationRegion)
open SourceEqualityConstraintRegions (Within)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Good Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Prefix" => SourceCurrentAllocatedInheritedPrefix.run
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A scoped prefix skips only actual completed earlier children of the same walk. -/
inductive WalkPrefix (g s r e p h m c n budget : Nat) (combined : EqValue)
    (initialFuel : Nat) (originals : List Node) (start : Caller width) :
    Nat → Nat → List Node → Caller width → Prop where
  /-- The actual initial walk has index zero and the complete original child list. -/
  | initial : WalkPrefix g s r e p h m c n budget combined initialFuel originals start
      initialFuel 0 originals start
  /-- A completed earlier node enters the literal next slot with its returned caller. -/
  | next {fuel index : Nat} {value result : Node} {rest : List Node} {before middle : Caller width}
      (earlier : WalkPrefix g s r e p h m c n budget combined initialFuel originals start
        (fuel + 1) index (value :: rest) before)
      (actual : SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget
        ⟨(descend before combined index).1, value⟩ (descend before combined index).2 = .done result middle) :
      WalkPrefix g s r e p h m c n budget combined initialFuel originals start
        fuel (index + 1) rest middle

variable {g s r e p h m c n budget initialFuel fuel index : Nat}
variable {combined inherited : EqValue} {originals remaining : List Node} {start current before : Caller width}
variable {edge : Edge} {child : Node} {rest : List Node} {literal : String → Symbol}

/-- The current suffix has exactly the original walk offset. -/
theorem WalkPrefix.position
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel originals start
      fuel index remaining current) : originals.drop index = remaining := by
  induction actual with
  | initial => rfl
  | next earlier called ih =>
      simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using
        congrArg (List.drop 1) ih

/-- The literal prefix preserves its fuel count and child-list position count. -/
theorem WalkPrefix.bounds
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel originals start
      fuel index remaining current) :
    fuel + index = initialFuel ∧ index + remaining.length = originals.length := by
  induction actual with
  | initial => exact ⟨Nat.add_zero _, Nat.zero_add _⟩
  | next earlier called ih =>
      obtain ⟨fuelSame, lengthSame⟩ := ih
      simp only [List.length_cons] at lengthSame
      constructor <;> omega

/-- Each scoped prefix is an actual prefix of the same outer walk phase. -/
theorem WalkPrefix.reached
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel originals start
      fuel index remaining current) :
    Reached g s r e p h m c n budget (.walk initialFuel combined 0 originals start)
      (.walk fuel combined index remaining current) := by
  induction actual with
  | initial => exact .refl _
  | next earlier called ih => exact .snoc ih (Step.walk_tail called)

/-- The actual inherited prefix and live payload enter this exact scoped walk. -/
theorem descendants_reached
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel edge.children
      (prefixState before edge inherited) fuel index remaining current)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction) :
    Reached g s r e p h m c n budget (.descendants initialFuel inherited edge before)
      (.walk fuel combined index remaining current) := by
  have entered : Reached g s r e p h m c n budget (.descendants initialFuel inherited edge before)
      (.walk initialFuel combined 0 edge.children (prefixState before edge inherited)) :=
    .snoc (.snoc (.refl _) (Step.descendants_children prefixDone)) (Step.children_walk live)
  exact entered.trans actual.reached

/-- The scoped application prefix derives the next Program entry without a supplied frame. -/
theorem application_entry
    (role : ProgramEdge literal edge) (arity : edge.children.length = 4)
    (programSlot : index = 2 ∨ index = 3)
    (good : Good before) (inputs : Inputs (.descendants initialFuel inherited edge before))
    (within : Within annotationRegion inherited.payload)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel edge.children
      (prefixState before edge inherited) (fuel + 1) index (child :: rest) current) :
    ProgramValue literal child ∧ Within annotationRegion (descend current combined index).1.payload ∧
      Reached g s r e p h m c n budget (.descendants initialFuel inherited edge before)
        (.node fuel ⟨(descend current combined index).1, child⟩ (descend current combined index).2) :=
  SourceSynthesisProgramChildEntry.application_entry role arity programSlot good inputs within prefixDone
    (descendants_reached actual prefixDone live) actual.position

/-- The scoped filter prefix derives its next Program entry before that child returns. -/
theorem filter_entry
    (role : ProgramEdge literal edge) (arity : edge.children.length = 2)
    (good : Good before) (inputs : Inputs (.descendants initialFuel inherited edge before))
    (within : Within annotationRegion inherited.payload)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (actual : WalkPrefix g s r e p h m c n budget combined initialFuel edge.children
      (prefixState before edge inherited) (fuel + 1) 1 (child :: rest) current) :
    ProgramValue literal child ∧ Within annotationRegion (descend current combined 1).1.payload ∧
      Reached g s r e p h m c n budget (.descendants initialFuel inherited edge before)
        (.node fuel ⟨(descend current combined 1).1, child⟩ (descend current combined 1).2) :=
  SourceSynthesisProgramChildEntry.filter_entry role arity good inputs within prefixDone
    (descendants_reached actual prefixDone live) actual.position

end MicroCFTA.SourceSynthesisProgramWalkPrefix
