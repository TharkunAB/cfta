import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourcePruningEnumerationShallowChild

/-!
# Exact raw allocation of a Program child

The actual preparation and successful action determine the fresh hole and state.
The input retains complete Program fields and annotation-only suspended paths.
This result does not assert a role invariant for the complete enumeration history.
-/
namespace MicroCFTA.SourceSynthesisProgramChildSlots
open Fragments EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationShallowChild
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- A successful Program child returns its actual fresh hole and complete written state. -/
theorem program_child_slot
    (incoming : Node) (scs : List Suspended)
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (action : EnumerateM Symbol Constraint (Fragment Symbol))
    (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values := (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} := by
  have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
    apply List.any_eq_false.mpr
    intro sc member tagged
    have terminal : sc.trie = .terminal := by
      cases trieRead : sc.trie with
      | empty =>
          simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
      | terminal => rfl
      | branch children =>
          simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    obtain ⟨tail, impossible⟩ := (pathScope sc member).2 []
      ((EqualityTrie.nil_mem sc.trie).mpr terminal)
    cases impossible
  cases fields with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at actual
      simp [Success, reject, ExceptT.run] at actual
  | node entry rows depth free _checked =>
      simp only [prepareChild, nonterminal, Bool.false_eq_true, ↓reduceIte,
        encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at actual
      obtain ⟨uv, middle, allocation, continued⟩ := (success_bind _ _ _ _ _).mp actual
      have allocatedState : uv = before.counter ∧
          middle = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := allocatedState
      obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain ⟨rfl, rfl⟩ := (success_pure _ _ _ _).mp final
      exact ⟨entry.identity + 1, rfl, rfl,
        (EnumerationDriver.modify_success _ _ _).mp writing⟩

end MicroCFTA.SourceSynthesisProgramChildSlots
