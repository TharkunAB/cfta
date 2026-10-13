import MicroCFTA.MergedPhysicalMergeContext

/-!
# Finite-term meaning of the prepared physical comparison graph

The epsilon graph follows stored union members and actual prepared Mu
unfoldings. Its constructor rows retain complete child records and guards.
The finite row reader has exactly this graph's finite-run language.
-/
namespace MicroCFTA.MergedPhysicalLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedPhysicalComparison MergedPhysicalMergeContext
open Language Productivity

/-- The physical graph before its finite epsilon references are eliminated. -/
def graph [DecidableEq (EdgeKey Symbol Guard)] (state : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) : EpsilonUnion.Graph (Value Symbol Guard) Symbol :=
  ⟨successors state, constructorRows meaning⟩

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Every copied row comes from an actual finite epsilon path. -/
theorem edge_forward [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (roots outputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) (root : Value Symbol Guard)
    (edge : Edge (Value Symbol Guard) Symbol) (member : edge ∈ rows state roots outputs meaning root) :
    ∃ source, Reachable (successors state) [root] source ∧ edge ∈ constructorRows meaning source := by
  obtain ⟨source, present, original⟩ := List.mem_flatMap.mp member
  have spec := EpsilonUnion.visit_spec (successors state) (inventory state roots outputs).eraseDups [root]
    (SymbolicDriver.eraseDups_nodup _)
  exact ⟨source, spec.reachable source present, original⟩

/-- Prepared source rows contain every constructor reached through the actual epsilon graph. -/
theorem edge_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Term Symbol → Bool) (root : Value Symbol Guard)
    (rootIn : root ∈ inventory state roots outputs) (edge : Edge (Value Symbol Guard) Symbol) :
    edge ∈ rows state roots outputs meaning root ↔
      ∃ source, Reachable (successors state) [root] source ∧ edge ∈ constructorRows meaning source := by
  constructor
  · exact edge_forward state roots outputs meaning root edge
  · rintro ⟨source, reached, member⟩
    exact List.mem_flatMap.mpr ⟨source,
      (visited_exact state context.facts roots outputs inputs context.retained context.ready root rootIn source).mpr reached,
      member⟩

/-- Reading finitely many physical rows cannot invent an accepted finite term. -/
theorem accepts_forward [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (roots outputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) (root : Value Symbol Guard) (term : Term Symbol)
    (accepted : Language.Accepts (rows state roots outputs meaning) root term) :
    EpsilonUnion.Accepts (graph state meaning) root term := by
  induction accepted using Language.Accepts.rec
    (motive_2 := fun qs ts _ => All₂ (EpsilonUnion.Accepts (graph state meaning)) qs ts) with
  | @node root edge children member accepted allowed ih =>
      obtain ⟨source, reached, original⟩ := edge_forward state roots outputs meaning root edge member
      exact EpsilonUnion.along_reference (graph state meaning) root source reached _
        (.node edge children original ih allowed)
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Prepared epsilon exposure retains every finite run of the physical graph. -/
theorem accepts_backward [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Term Symbol → Bool) (root : Value Symbol Guard) (term : Term Symbol)
    (accepted : EpsilonUnion.Accepts (graph state meaning) root term)
    (rootIn : root ∈ inventory state roots outputs) :
    Language.Accepts (rows state roots outputs meaning) root term := by
  revert rootIn
  induction accepted using EpsilonUnion.Accepts.rec
    (motive_2 := fun qs ts _ => (∀ q ∈ qs, q ∈ inventory state roots outputs) →
      All₂ (Language.Accepts (rows state roots outputs meaning)) qs ts) with
  | @reference root target term member accepted ih =>
      intro rootIn
      have targetIn := successors_closed state context.facts roots outputs inputs context.retained context.ready
        root rootIn target member
      cases ih targetIn with
      | node edge children copied subtrees allowed =>
          obtain ⟨source, reached, original⟩ := edge_forward state roots outputs meaning target edge copied
          have first : Reachable (successors state) [root] target := .step (.seed (by simp)) member
          exact .node edge children
            ((edge_exact state outputs context roots inputs meaning root rootIn edge).mpr
              ⟨source, EpsilonUnion.reach_trans _ _ _ _ first reached, original⟩) subtrees allowed
  | @node root edge children member subtrees allowed ih =>
      intro rootIn
      have available := inventory_available state context.facts roots outputs inputs context.retained root rootIn
      exact .node edge children
        ((edge_exact state outputs context roots inputs meaning root rootIn edge).mpr ⟨root, .seed (by simp), member⟩)
        (ih (fun child selected => constructor_children state context.facts roots outputs root available meaning edge member child selected)) allowed
  | nil => exact .nil
  | @cons q term qs terms head tail ihHead ihTail =>
      rename_i contained
      exact .cons (ihHead (contained q List.mem_cons_self))
        (ihTail (fun child member => contained child (List.mem_cons_of_mem _ member)))

/-- The complete finite row reader has exactly the prepared physical graph's finite-term language. -/
theorem accepts_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Term Symbol → Bool) (root : Value Symbol Guard)
    (rootIn : root ∈ inventory state roots outputs) (term : Term Symbol) :
    Language.Accepts (rows state roots outputs meaning) root term ↔
      EpsilonUnion.Accepts (graph state meaning) root term :=
  ⟨accepts_forward state roots outputs meaning root term,
    fun accepted => accepts_backward state outputs context roots inputs meaning root term accepted rootIn⟩

/-- Literal EmptyNode contributes no row to the physical reader. -/
theorem rows_empty [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (roots outputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) : rows state roots outputs meaning .empty = [] := by
  simp [rows, visited, EpsilonUnion.visit, MergedPhysicalComparison.successors, constructorRows, inventory]

/-- Successful source comparison includes the physical epsilon language of the narrow operand. -/
theorem comparison_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (narrowIn : narrow ∈ inventory state roots outputs)
    (success : MergedComparisonSource.check (rows state roots outputs meaning)
      (fun value => value.referenceOf == .empty) unconstrained fuel [] wide narrow = true)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (graph state meaning) narrow term) :
    EpsilonUnion.Accepts (graph state meaning) wide term := by
  apply accepts_forward state roots outputs meaning wide term
  have emptyRows : ∀ value : Value Symbol Guard, (value.referenceOf == .empty) = true →
      rows state roots outputs meaning value = [] := by
    intro value empty
    have same : value = .empty := by
      cases value <;> simp_all [Value.referenceOf]
    rw [same, rows_empty]
  exact MergedComparisonSource.check_sound (rows state roots outputs meaning)
    (fun value => value.referenceOf == .empty) unconstrained emptyRows clear fuel wide narrow success term
    (accepts_backward state outputs context roots inputs meaning narrow term accepted narrowIn)

/-- A retained explicit union denotes exactly the union of its original members. -/
theorem retained_union_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (meaning : Guard → Term Symbol → Bool)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph state meaning) (.union entry members depth free) term ↔
      ∃ member ∈ members, EpsilonUnion.Accepts (graph state meaning) member term :=
  EpsilonUnion.union_exact (graph state meaning) _ rfl term

end
end MicroCFTA.MergedPhysicalLanguage
