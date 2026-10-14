import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryBodyFilter
import MicroCFTA.InternedStoredUnfoldingRank

/-!
# Guarded head progress in actual repaired stored unfolding

Ordinary constructors stop the current gate path. Repaired source execution
preserves their guards through arbitrary nested child effects and union
normalization. General decoded completion supplies the actual finite call.
No shallow-body or first-order restriction is imposed on the children.
-/
namespace MicroCFTA.InternedFreshOrdinaryGuardedUnfold
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedStoredUnfoldingRank (GuardedSyntax encode_guarded stored_guarded)
open InternedStoredSubstitution (leaves input inputs_available leaves_available)
open InternedPreparedSubstitution (GuardedValue)
open InternedUnionHeadGuard InternedGateRank InternedStoredSelfFilter
open InternedBinderProtocol (Reference NodeKey)

mutual
/-- The full source executor retains original root guards after every nested child effect. -/
theorem build_guarded [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (guarded : GuardedSyntax environment expression)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build expression environment state = .done value final) : HeadSafe value := by
  cases guarded with
  | empty => simp only [build, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; exact .empty
  | var index safe => simp only [build, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; exact safe
  | node edges =>
      simp only [build] at completed
      have checked := buildEdges_verified edges environment state facts inputs
      cases built : buildEdges edges environment state with
      | pending key after => simp [built, Outcome.bind] at completed
      | done values after =>
          have later : Facts after := by simpa only [built, Outcome.state] using checked.facts
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
          exact completed.1 ▸ makeNode_safeHead values after later.coherent
  | union members safe =>
      simp only [build] at completed
      have checked := buildMany_verified members environment state facts inputs
      cases built : buildMany members environment state with
      | pending key after => simp [built, Outcome.bind] at completed
      | done values after =>
          have later : Facts after := by simpa only [built, Outcome.state] using checked.facts
          have guardedMembers := buildMany_guarded members environment state facts inputs safe values after built
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
          exact completed.1 ▸ makeUnion_safeHead values after later.coherent later.cached (checked.result values after built) guardedMembers
termination_by sizeOf expression

/-- Ordered root union members retain their guards through all previous effects. -/
theorem buildMany_guarded [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (guarded : ∀ expression ∈ expressions, GuardedSyntax environment expression)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (completed : buildMany expressions environment state = .done values final) : ∀ value ∈ values, HeadSafe value := by
  cases expressions with
  | nil => simp only [buildMany, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; simp
  | cons first rest =>
      simp only [buildMany] at completed
      have checked := build_verified first environment state facts inputs
      cases head : build first environment state with
      | pending key after => simp [head, Outcome.bind] at completed
      | done value after =>
          have headFacts : Facts after := by simpa only [head, Outcome.state] using checked.facts
          have laterInputs : Values after environment := by
            intro value member
            simpa only [head, Outcome.state] using checked.available value (inputs value member)
          have headSafe := build_guarded first environment state facts inputs (guarded first (by simp)) value after head
          simp only [head, Outcome.bind] at completed
          cases tail : buildMany rest environment after with
          | pending key later => simp [tail] at completed
          | done remaining later =>
              have tailSafe := buildMany_guarded rest environment after headFacts laterInputs
                (fun expression member => guarded expression (by simp [member])) remaining later tail
              simp only [tail, Outcome.done.injEq] at completed
              rcases completed with ⟨rfl, _⟩
              intro selected member
              rcases List.mem_cons.mp member with rfl | member
              · exact headSafe
              · exact tailSafe selected member
termination_by sizeOf expressions
end


/-- Actual repaired stored substitution preserves a selected-name root guard. -/
theorem execute_guarded_rank [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (body replacement : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state body) (replacementAvailable : Available state replacement)
    (guarded : GuardedValue name body) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedFreshOrdinaryStoredSubstitution.execute body
      (fun reference => if reference = name then some replacement else none) state = .done value final) :
    headRank value = 0 := by
  apply HeadSafe.rank
  apply build_guarded _ _ state facts _
    (encode_guarded name (leaves body) body replacement state facts.coherent
      (leaves_available body state available) (fun _ member => member) guarded) value final completed
  apply inputs_available body _ state available
  intro reference selected found
  dsimp only at found
  split at found
  · cases found; exact replacementAvailable
  · contradiction

/-- Every completed repaired unfolding of a source-filtered guarded body has head rank zero. -/
theorem unfold_guarded_zero [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (safe : HeadSafe body)
    (opened : (Value.mu entry body depth ordinary).free ≠ [])
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final) :
    headRank value = 0 :=
  execute_guarded_rank (.interned entry.identity) body (.mu entry body depth ordinary) state context.normal.facts
    (available.children body (by simp [children])) available
    (stored_guarded entry body depth ordinary state context.normal.flat clean available safe opened) value final completed

/-- Repaired stored substitution preserves all complete source body filters. -/
theorem execute_clean [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (available : Available state body)
    (replacements : InternedStoredSubstitution.Replacements state environment) (clean : Clean state) :
    Clean (InternedFreshOrdinaryStoredSubstitution.execute body environment state).state :=
  InternedFreshOrdinaryBodyFilter.build_clean _ _ state context.normal
    (inputs_available body environment state available replacements) clean

/-- Arbitrary repaired unfolding retains body filters in its exact completed or pending cache. -/
theorem unfold_clean [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures) (available : Available state value)
    (clean : Clean state) :
    Clean (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact clean
  | mu entry body depth ordinary =>
      apply execute_clean body _ state context (available.children body (by simp [children])) ?_ clean
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · contradiction

/-- General decoded completion derives strict repaired gate progress for every guarded body. -/
theorem unfold_complete_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (heap : InternedFreshOrdinaryDepthHeap.Heap state)
    (covered : Covered [] state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (safe : HeadSafe body)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final ∧
      Context final captures ∧ InternedFreshOrdinaryDepthHeap.Heap final ∧ Covered [] final ∧
      Available final value ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      Clean final ∧ headRank value = 0 ∧ headRank value < headRank (.mu entry body depth ordinary) := by
  obtain ⟨value, final, done, afterContext, afterHeap, afterCovered, afterAvailable, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
      state context available heap covered
  have zero := unfold_guarded_zero entry body depth ordinary state context clean available safe opened value final done
  have afterClean : Clean final := by
    simpa only [done, Outcome.state] using unfold_clean (.mu entry body depth ordinary) state context available clean
  exact ⟨value, final, done, afterContext, afterHeap, afterCovered, afterAvailable, growth, history, afterClean, zero,
    by simp [zero, headRank]⟩

/-- Original empty-cache source construction derives all representation premises of guarded repaired progress. -/
theorem closed_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (safe : HeadSafe body) (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
      (build expression [] empty).state = .done value final ∧
      Clean final ∧ headRank value = 0 ∧ headRank value < headRank (.mu entry body depth ordinary) := by
  obtain ⟨source, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have context : Context state [] := by simpa only [built, Outcome.state] using empty_context.build expression
  have heap : InternedFreshOrdinaryDepthHeap.Heap state := by
    simpa only [built, Outcome.state] using
      (InternedRecordDepthExecution.build_depth expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have clean : Clean state := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryBodyFilter.closed_clean expression
  have available : Available state (.mu entry body depth ordinary) :=
    context.normal.facts.cached.nodes key _ (by simpa only [built, Outcome.state] using stored)
  obtain ⟨value, final, done, _, _, _, _, _, _, afterClean, zero, smaller⟩ :=
    unfold_complete_decreases entry body depth ordinary state context heap
      (InternedFreshOrdinaryCoverage.closed_covered expression source state built) clean available safe opened
  exact ⟨value, final, by simpa only [built, Outcome.state] using done, afterClean, zero, smaller⟩

end MicroCFTA.InternedFreshOrdinaryGuardedUnfold
