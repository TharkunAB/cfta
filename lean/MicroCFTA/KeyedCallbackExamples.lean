import MicroCFTA.KeyedCallbackCausality
import MicroCFTA.RecursiveNaryExamples

/-!
# Concrete mutually recursive keyed callback checks

The two keys use retained finite leaves with masses nine and one. Queries
retain each exact source rank and check both key labels at every boundary.
-/
namespace MicroCFTA.KeyedCallbackExamples
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination KeyedCallbackFields KeyedCallbackInverse
open KeyedTermAlignment (twoKeyExample twoKeyPosition)
open RecursiveNaryExamples (pureCallbacks pure_exact)

/-- The complete source key order of the concrete two-key family. -/
def keys : List Bool := [false, true]

theorem keys_complete (key : Bool) : key ∈ keys := by cases key <;> simp [keys]

/-- Both source body guards pass with the actual discovered keyed metadata. -/
theorem accepted : Guarded keys keys_complete twoKeyExample := by
  intro key
  cases key <;> simp [twoKeyExample, KeyedTermAlignment.valueProgram,
    KeyedTermAlignment.valueRecipe, KeyedSource.guarded]

/-- Retained finite weights use the same independently correct leaf callbacks. -/
theorem exact_leaves : ∀ key, LeavesExact (pureCallbacks (Symbol := Nat)) (twoKeyExample key) := by
  intro key
  cases key
  · exact ⟨⟨pure_exact _, pure_exact _⟩, trivial⟩
  · trivial

/-- The first retained member under the second key's actual private boundary. -/
def firstTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 1
  (.node (.user 11) [KeyedTermBoundary.atKeyTerm 0
    (.node (.choice 0) [.node (.choice 0) [.node .pure []]])])

/-- The second finite member keeps its distinct private source branch. -/
def secondTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 1
  (.node (.user 11) [KeyedTermBoundary.atKeyTerm 0
    (.node (.choice 0) [.node (.choice 1) [.node .pure []]])])

theorem first_inverse :
    positions twoKeyPosition pureCallbacks twoKeyExample true .whole [firstTerm] = [(⟨1, 0⟩, true)] := by cbv

theorem second_inverse :
    positions twoKeyPosition pureCallbacks twoKeyExample true .whole [secondTerm] = [(⟨1, 1⟩, true)] := by cbv

/-- Every view preserves the same complete family boundary and source position. -/
theorem member_views :
    positions twoKeyPosition pureCallbacks twoKeyExample true .spine [firstTerm] = [(⟨1, 0⟩, true)] ∧
    positions twoKeyPosition pureCallbacks twoKeyExample true .labelled [firstTerm] = [(⟨1, 0⟩, true)] := by cbv

/-- The next mutual step returns to the first key and retains its own class rank. -/
def mutualTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 0
  (.node (.choice 1) [.node (.user 10) [firstTerm]])

theorem mutual_inverse :
    positions twoKeyPosition pureCallbacks twoKeyExample false .whole [mutualTerm] = [(⟨2, 0⟩, true)] := by cbv

/-- A complete term under another root key cannot enter the current key's body. -/
theorem wrong_outer_key :
    positions twoKeyPosition pureCallbacks twoKeyExample false .whole [firstTerm] = [] := by cbv

/-- Matching the outer key alone is insufficient when the inner family key differs. -/
theorem wrong_inner_key :
    positions twoKeyPosition pureCallbacks twoKeyExample true .whole
      [.node .atKey [.node (.key 1) [], .node .family [.node (.key 0) [], .node .pure []]]] = [] := by cbv

/-- The generic inverse theorem applies to the actual guarded mutual source and these leaf producers. -/
theorem first_exact (position : Position) :
    (position, true) ∈ positions twoKeyPosition pureCallbacks twoKeyExample true .whole [firstTerm] ↔
      rootSelect twoKeyPosition twoKeyExample true position = some firstTerm := by
  rw [positions_exact keys keys_complete twoKeyPosition pureCallbacks twoKeyExample accepted exact_leaves]
  simp [project]

end MicroCFTA.KeyedCallbackExamples
