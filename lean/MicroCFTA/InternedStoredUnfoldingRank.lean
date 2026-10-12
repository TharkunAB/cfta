import MicroCFTA.InternedStoredSubstitutionBindings

/-!
# Head-rank laws for the full stored substitution adapter

Ordinary constructors guard arbitrary open nested work in their children.
Root unions preserve those guards through actual normalization. Every
successful guarded stored-body unfolding therefore has head rank zero.
A pending canonical readback remains a separate completion obligation.
-/
namespace MicroCFTA.InternedStoredUnfoldingRank
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionHeadGuard InternedPreparedSubstitution InternedGateRank
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedUnionNormalForm InternedStoredSelfFilter
open InternedBinderProtocol (Reference NodeKey)

/-- Every root union path in the original lexical expression reaches a
constructor or a captured input whose own root union paths are guarded. -/
inductive GuardedSyntax (environment : List (Value Symbol Guard)) : Syntax Symbol Guard → Prop where
  | empty : GuardedSyntax environment .empty
  | var (index) (safe : HeadSafe (environment[index]?.getD .empty)) : GuardedSyntax environment (.var index)
  | node (edges) : GuardedSyntax environment (.node edges)
  | union (members) (safe : ∀ expression ∈ members, GuardedSyntax environment expression) :
      GuardedSyntax environment (.union members)

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

mutual
/-- Actual record preparation preserves root guards for the selected source replacement. -/
theorem encode_guarded (name : Reference) (context : List (Value Symbol Guard)) (body replacement : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (covered : ∀ leaf ∈ leaves body, leaf ∈ context) (guarded : GuardedValue name body) :
    GuardedSyntax (context.map (input (fun reference => if reference = name then some replacement else none)))
      (encode context [] body) := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : body ∈ context := covered body (by rw [leaves.eq_def]; simp [closed])
    apply GuardedSyntax.var
    simp only [List.length_nil, Nat.zero_add]
    rw [List.getElem?_map, slot_lookup context body state coherent contextAvailable member]
    simp only [Option.map_some, Option.getD_some,
      input_closed body _ (List.isEmpty_iff.mp closed)]
    exact guarded.headSafe
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases guarded with
    | empty => exact .empty
    | reference other different =>
        simp only [List.findIdx?_nil]
        apply GuardedSyntax.var
        simp only [List.length_nil, Nat.zero_add]
        rw [List.getElem?_map, slot_lookup context (.reference other) state coherent contextAvailable (covered _ (by simp))]
        simp only [Option.map_some, Option.getD_some, input, different, ↓reduceIte, Option.getD_none]
        exact .reference other
    | node entry edges depth free => exact .node _
    | union entry members depth free safe =>
        exact .union _ (encodeMany_guarded name context members replacement state coherent contextAvailable covered safe)
termination_by sizeOf body

/-- Prepared source union members retain guards without inspecting their rebuilt results. -/
theorem encodeMany_guarded (name : Reference) (context : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (replacement : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (contextAvailable : Values state context) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (guarded : ∀ value ∈ values, GuardedValue name value) :
    ∀ expression ∈ encodeMany context [] values,
      GuardedSyntax (context.map (input (fun reference => if reference = name then some replacement else none))) expression := by
  cases values with
  | nil => simp [encodeMany]
  | cons first rest =>
      intro expression member
      simp only [encodeMany, List.mem_cons] at member
      rcases member with rfl | member
      · exact encode_guarded name context first replacement state coherent contextAvailable
          (fun leaf present => covered leaf (by simp [manyLeaves, present])) (guarded first (by simp))
      · exact encodeMany_guarded name context rest replacement state coherent contextAvailable
          (fun leaf present => covered leaf (by simp [manyLeaves, present]))
          (fun value present => guarded value (by simp [present])) expression member
termination_by sizeOf values
end

/-- Actual full source substitution returns rank zero on a guarded body,
even when its constructor children rebuild open nested Mu records. -/
theorem execute_guarded_rank [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (body replacement : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state body) (replacementAvailable : Available state replacement)
    (guarded : GuardedValue name body) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : execute body (fun reference => if reference = name then some replacement else none) state = .done value final) :
    headRank value = 0 := by
  apply HeadSafe.rank
  apply build_guarded _ _ state facts _
    (encode_guarded name (leaves body) body replacement state facts.coherent
      (leaves_available body state available) (fun _ member => member) guarded) value final completed
  apply inputs_available body _ state available
  intro reference selected found
  simp only [] at found
  split at found
  · cases found; exact replacementAvailable
  · contradiction

/-- Stored source normalization supplies the selected-name guard whenever
all root union paths stop before Mu. Nested Mu below ordinary nodes are allowed. -/
theorem stored_guarded (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (flat : Flat state) (clean : Clean state) (available : Available state (.mu entry body depth ordinary))
    (safe : HeadSafe body) (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    GuardedValue (.interned entry.identity) body := by
  have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
  have noSelf := resident_clean state clean (.mu entry body depth ordinary) available.resident
  cases safe with
  | empty => exact .empty
  | reference name =>
      apply GuardedValue.reference
      intro same
      simp [same, Value.free] at opened
  | node entry edges depth free => exact .node entry edges depth free
  | union actual members level free safe =>
      apply GuardedValue.union
      intro value member
      have different : value ≠ .reference (.interned entry.identity) := fun same => noSelf (same ▸ member)
      have memberSafe := safe value member
      have atomic := resident_flat state flat _ bodyAvailable.resident value member
      cases memberSafe with
      | empty => exact .empty
      | reference other => exact .reference other (fun same => different (congrArg Value.reference same))
      | node entry edges depth free => exact .node entry edges depth free
      | union => contradiction

/-- Successful unfolding of a source-normalized guarded Mu strictly
reduces the actual head rank, with arbitrary open nested constructor children. -/
theorem stored_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (safe : HeadSafe body)
    (opened : (Value.mu entry body depth ordinary).free ≠ [])
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final) :
    headRank value < headRank (.mu entry body depth ordinary) := by
  have guarded := stored_guarded entry body depth ordinary state flat clean available safe opened
  have rank := execute_guarded_rank (.interned entry.identity) body (.mu entry body depth ordinary) state facts
    (available.children body (by simp [InternedProbeProvenance.children])) available guarded value final completed
  simp [rank, headRank]

/-- The ordinary-body source branch needs no condition on nested binders
inside its children beyond successful actual canonical reconstruction. -/
theorem ordinary_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry nodeEntry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry (.node nodeEntry edges level free) depth ordinary))
    (opened : (Value.mu entry (.node nodeEntry edges level free) depth ordinary).free ≠ [])
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedStoredSubstitution.unfold (.mu entry (.node nodeEntry edges level free) depth ordinary) state = .done value final) :
    headRank value = 0 := by
  have smaller := stored_unfold_decreases entry (.node nodeEntry edges level free) depth ordinary state facts flat clean
    available (.node nodeEntry edges level free) opened value final completed
  simpa [headRank] using smaller

end MicroCFTA.InternedStoredUnfoldingRank
