import MicroCFTA.EnumerationFlatCore
import MicroCFTA.SourcePruningEnumerationShallowChild

/-!
# Flat nonterminal child actions

Allocation and child preparation use the direct core operations.
The relation retains optional actions without comparing function values.
-/

namespace MicroCFTA.EnumerationFlatState

variable {Symbol Guard : Type}

/-- Allocate the raw slot and inherit its expansion ancestry. -/
def allocated (node : Option Nat) (before : State Symbol Guard) : State Symbol Guard :=
  {before with
    counter := before.counter + 1
    values := before.values ++ [EnumerationState.UVarValue.unenumerated node []]
    recursionAncestry := fun other =>
      if other = before.counter then
        (before.expansionAncestry ++ before.recursionAncestry before.counter).eraseDups
      else before.recursionAncestry other}

/-- Allocation has one exact successful row. -/
theorem allocate_exact (node : Option Nat) (before : State Symbol Guard) :
    allocate node before = [.ok (before.counter, allocated node before)] := rfl

/-- Allocation preserves every related core field and both forest representations. -/
theorem allocated_related (related : Related flat earlier) (node : Option Nat) :
    Related (allocated node flat) (EnumerationState.allocated node earlier) := by
  refine ⟨related.valid, related.representatives, ?_, ?_, related.obligations, ?_,
    related.expansionAncestry⟩
  · change flat.counter + 1 = earlier.counter + 1
    rw [related.counter]
  · change flat.values ++ _ = earlier.values ++ _
    rw [related.values]
  · change (fun other => if other = flat.counter then _ else flat.recursionAncestry other) = _
    rw [related.counter, related.expansionAncestry, related.recursionAncestry]
    rfl

end MicroCFTA.EnumerationFlatState

namespace MicroCFTA.SourceFlatPruningShallowChild

open EnumerationState EnumerationFlatState EnumerationResultRelation
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard α : Type}

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Stage the actual shallow child action without executing it. -/
def prepareChild (scs : List Suspended) (value : Value Symbol NativeGuard) :
    Option (Action Symbol EnumGuard (Fragments.Fragment Symbol)) :=
  match value with
  | .empty => some EnumerationFlatState.reject
  | .reference _ => none
  | .node _ _ _ _ | .union _ _ _ _ | .mu _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).map fun node =>
          EnumerationFlatState.allocate (some node) >>= fun uv =>
            match value with
            | .node _ _ _ _ =>
                EnumerationFlatState.setValue uv (.unenumerated (some node) scs) >>= fun _ =>
                  pure (.hole uv)
            | _ => pure (.hole uv)

/-- Keep absent preparation separate from all rows of a present action. -/
def OptionalActions
    (flat : Option (Action Symbol EnumGuard α))
    (earlier : Option (EnumerateM Symbol EnumGuard α)) : Prop :=
  match flat, earlier with
  | none, none => True
  | some flat, some earlier =>
      ∀ left right, Related left right → Results Related (flat left) (earlier right)
  | _, _ => False

/-- The actual shallow actions preserve every row at any related input cores. -/
theorem prepareChild_related (scs : List Suspended) (value : Value Symbol NativeGuard) :
    OptionalActions (prepareChild (EnumGuard := EnumGuard) scs value)
      (SourcePruningEnumerationShallowChild.prepareChild scs value) := by
  cases value with
  | empty => exact fun _ _ _ => .nil
  | reference name => trivial
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          ↓reduceIte, OptionalActions]
        trivial
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          Bool.false_eq_true, ↓reduceIte, encodeNode, Option.map_some, OptionalActions]
        intro flat earlier related
        apply stateT_bind _ _ _ _ (allocate_related related (some (entry.identity + 1)))
        intro uv left right states
        apply stateT_bind _ _ _ _ (setValue_related states uv (.unenumerated (some (entry.identity + 1)) scs))
        intro _ left right states
        exact pure_related states (.hole uv)
  | union entry members depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          ↓reduceIte, OptionalActions]
        trivial
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          Bool.false_eq_true, ↓reduceIte, encodeNode, Option.map_some, OptionalActions]
        intro flat earlier related
        exact stateT_bind _ _ _ _ (allocate_related related (some (entry.identity + 1)))
          (fun uv _ _ states => pure_related states (.hole uv))
  | mu entry body depth ordinary =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          ↓reduceIte, OptionalActions]
        trivial
      · simp only [prepareChild, SourcePruningEnumerationShallowChild.prepareChild, terminal,
          Bool.false_eq_true, ↓reduceIte, encodeNode, Option.map_some, OptionalActions]
        intro flat earlier related
        exact stateT_bind _ _ _ _ (allocate_related related (some (entry.identity + 1)))
          (fun uv _ _ states => pure_related states (.hole uv))

end MicroCFTA.SourceFlatPruningShallowChild
