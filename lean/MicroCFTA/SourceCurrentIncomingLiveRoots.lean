import MicroCFTA.SourceCurrentIncomingReadRoots
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

/-! Actual incoming reads and admitted slot replacements preserve live roots. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingLiveRoots
open EnumerationState EnumerationSchedule
open InternedConstructorTemplates (Value EdgeKey)
open EnumerationCanonicalUnion

private theorem set_lookup_cases {α : Type} (values : List α) (target held : Nat)
    (replacement value : α) :
    (values.set target replacement)[held]? = some value →
      (held = target ∧ value = replacement) ∨ values[held]? = some value := by
  induction values generalizing target held with
  | nil => simp
  | cons head tail inductionHyp =>
      intro observed
      cases target with
      | zero =>
          cases held with
          | zero =>
              have same : replacement = value := by simpa using observed
              exact Or.inl ⟨rfl, same.symm⟩
          | succ held => exact Or.inr (by simpa using observed)
      | succ target =>
          cases held with
          | zero => exact Or.inr (by simpa using observed)
          | succ held =>
              rcases inductionHyp target held (by simpa using observed) with ⟨same, valueSame⟩ | original
              · exact Or.inl ⟨congrArg Nat.succ same, valueSame⟩
              · exact Or.inr (by simpa using original)

/-- An original live stored slot permits either unenumerated replacement handle option. -/
theorem live_roots_set {Symbol Guard : Type} (before : State Symbol Guard) (target : Nat)
    (oldNode node : Option Nat) (oldScs scs : List Suspended)
    (live : LiveRoots before)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs)) :
    LiveRoots {before with values := before.values.set target (.unenumerated node scs)} := by
  intro held value observed
  rcases set_lookup_cases before.values target held (.unenumerated node scs) value observed with
    ⟨same, valueSame⟩ | original
  · subst held
    subst value
    have rooted : IsRoot before.representatives target :=
      (live target (.unenumerated oldNode oldScs) stored).mp (by simp)
    exact ⟨fun _ => rooted, fun _ => by simp⟩
  · exact live held value original

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem live_same_roots (before after : Core) (roots : Nat → Nat)
    (beforePaths : Roots before.representatives roots) (afterPaths : Roots after.representatives roots)
    (values : after.values = before.values) (live : LiveRoots before) : LiveRoots after := by
  intro held value observed
  have original : before.values[held]? = some value := by
    rw [← values]
    exact observed
  have old := live held value original
  rw [root_iff _ roots beforePaths held] at old
  rw [root_iff _ roots afterPaths held]
  exact old

/-- Original root paths and live roots derive live roots at every literal outer read. -/
theorem incoming_read_live_roots (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots) (live : LiveRoots before) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    LiveRoots actual.2.2.2 := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  have actualFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before target incoming scs memos roots paths
  dsimp only at actualFacts
  exact live_same_roots before _ roots paths actualFacts.1 actualFacts.2.1 live

end MicroCFTA.SourceCurrentIncomingLiveRoots
