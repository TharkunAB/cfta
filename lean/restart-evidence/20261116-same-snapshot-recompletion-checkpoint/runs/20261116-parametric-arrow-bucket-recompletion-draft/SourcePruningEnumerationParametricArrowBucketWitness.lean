import MicroCFTA.SourcePruningEnumerationSharedProperPathWitness

namespace MicroCFTA.SourcePruningEnumerationParametricArrowBucketWitness
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false

/-- Use the first actual target at this position, or a free variable if none occurs. -/
private def arrowChoice (position : Nat) (rho : Nat → Term Symbol) : List Suspended → Term Symbol
  | [] => .node (literal "var1") []
  | sc :: rest =>
      if [position] ∈ EqualityTrie.fromPathTrie sc.trie then rho sc.var
      else arrowChoice position rho rest

private theorem arrowChoice_spec
    (catalog : List (String × Nat)) (position : Nat) (rho : Nat → Term Symbol) :
    ∀ bucket : List Suspended,
      (∀ sc ∈ bucket, [position] ∈ EqualityTrie.fromPathTrie sc.trie → TypeIn catalog (rho sc.var)) →
      (∀ first ∈ bucket, ∀ second ∈ bucket,
        [position] ∈ EqualityTrie.fromPathTrie first.trie →
        [position] ∈ EqualityTrie.fromPathTrie second.trie → rho first.var = rho second.var) →
      TypeIn catalog (arrowChoice position rho bucket) ∧
        ∀ sc ∈ bucket, [position] ∈ EqualityTrie.fromPathTrie sc.trie →
          arrowChoice position rho bucket = rho sc.var := by
  intro bucket
  induction bucket with
  | nil =>
    intro _typed _agrees
    refine ⟨TypeIn.leaf "var1" (by simp), ?_⟩
    intro sc member _represented
    cases member
  | cons first rest ih =>
    intro typed agrees
    by_cases represented : [position] ∈ EqualityTrie.fromPathTrie first.trie
    · simp only [arrowChoice, ite_eq_left represented]
      refine ⟨typed first List.mem_cons_self represented, ?_⟩
      intro sc member atPosition
      exact agrees first List.mem_cons_self sc member represented atPosition
    · simp only [arrowChoice, ite_eq_right represented]
      have tail := ih
        (fun sc member atPosition => typed sc (List.mem_cons_of_mem _ member) atPosition)
        (fun left leftMember right rightMember leftPath rightPath =>
          agrees left (List.mem_cons_of_mem _ leftMember) right (List.mem_cons_of_mem _ rightMember)
            leftPath rightPath)
      refine ⟨tail.1, ?_⟩
      intro sc member atPosition
      rcases List.mem_cons.mp member with same | later
      · subst sc
        exact (represented atPosition).elim
      · exact tail.2 sc later atPosition

/-- One owner-class change satisfies compatible arrow paths at their actual target terms. -/
theorem parametric_arrow_bucket_recompletion
    (catalog : List (String × Nat)) (forest : UnionFind.Forest) (owner : Nat)
    (bucket : List Suspended) (rho : Nat → Term Symbol)
    (root : IsRoot forest owner) (aliases : UnionFind.Satisfies forest rho)
    (separate : Avoids forest owner bucket)
    (arrowPaths : ∀ sc ∈ bucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      path = [1] ∨ path = [2])
    (targetTypes : ∀ sc ∈ bucket, ∀ (position : Nat),
      [position] ∈ EqualityTrie.fromPathTrie sc.trie → TypeIn catalog (rho sc.var))
    (compatible : ∀ (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
      bucket[firstIndex]? = some first → bucket[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie → rho first.var = rho second.var) :
    ∃ (argument result : Term Symbol) (updated : Nat → Term Symbol),
      TypeIn catalog argument ∧ TypeIn catalog result ∧
      updated owner = .node (literal "->") [.node (literal "(->)") [], argument, result] ∧
      TypeIn catalog (updated owner) ∧ UnionFind.Satisfies forest updated ∧
      (∀ slot, ¬UnionFind.SameClass forest owner slot → updated slot = rho slot) ∧
      (∀ sc ∈ bucket, updated sc.var = rho sc.var) ∧
      (∀ sc ∈ bucket, Suspended.Holds updated (updated owner) sc) ∧
      ∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        Suspended.Holds updated (updated owner) sc
 := by
  classical
  have agree : ∀ first ∈ bucket, ∀ second ∈ bucket, ∀ (position : Nat),
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie → rho first.var = rho second.var := by
    intro first firstMember second secondMember position firstPath secondPath
    obtain ⟨firstIndex, firstAt⟩ := List.mem_iff_getElem?.mp firstMember
    obtain ⟨secondIndex, secondAt⟩ := List.mem_iff_getElem?.mp secondMember
    exact compatible firstIndex secondIndex first second position firstAt secondAt firstPath secondPath
  have argumentFacts := arrowChoice_spec catalog 1 rho bucket
    (fun sc member atPosition => targetTypes sc member 1 atPosition)
    (fun first firstMember second secondMember firstPath secondPath =>
      agree first firstMember second secondMember 1 firstPath secondPath)
  have resultFacts := arrowChoice_spec catalog 2 rho bucket
    (fun sc member atPosition => targetTypes sc member 2 atPosition)
    (fun first firstMember second secondMember firstPath secondPath =>
      agree first firstMember second secondMember 2 firstPath secondPath)
  let argument := arrowChoice 1 rho bucket
  let result := arrowChoice 2 rho bucket
  let chosen : Term Symbol := .node (literal "->") [.node (literal "(->)") [], argument, result]
  let updated : Nat → Term Symbol := fun slot =>
    if UnionFind.SameClass forest owner slot then chosen else rho slot
  have selfClass : UnionFind.SameClass forest owner owner :=
    ⟨owner, root.choose, root.choose_spec, root.choose_spec⟩
  have ownerValue : updated owner = chosen := by
    simp only [updated, ite_eq_left selfClass]
  have updatedAliases : UnionFind.Satisfies forest updated := by
    intro left right same
    by_cases first : UnionFind.SameClass forest owner left
    · have second := UnionFind.sameClass_trans first same
      simp only [updated, ite_eq_left first, ite_eq_left second]
    · have second : ¬UnionFind.SameClass forest owner right := by
        intro joined
        exact first (UnionFind.sameClass_trans joined (UnionFind.sameClass_symm same))
      simpa only [updated, ite_eq_right first, ite_eq_right second] using aliases left right same
  have outside : ∀ slot, ¬UnionFind.SameClass forest owner slot → updated slot = rho slot := by
    intro slot different
    simp only [updated, ite_eq_right different]
  have targets : ∀ sc ∈ bucket, updated sc.var = rho sc.var := by
    intro sc member
    exact outside sc.var (separate sc member)
  have held : ∀ sc ∈ bucket, Suspended.Holds updated (updated owner) sc := by
    intro sc member path atPath
    rcases arrowPaths sc member path atPath with first | second
    · have firstPath : [1] ∈ EqualityTrie.fromPathTrie sc.trie := by
        simpa only [first] using atPath
      rw [first, ownerValue, targets sc member]
      change some argument = some (rho sc.var)
      exact congrArg some (argumentFacts.2 sc member firstPath)
    · have secondPath : [2] ∈ EqualityTrie.fromPathTrie sc.trie := by
        simpa only [second] using atPath
      rw [second, ownerValue, targets sc member]
      change some result = some (rho sc.var)
      exact congrArg some (resultFacts.2 sc member secondPath)
  have ownerTyped : TypeIn catalog (updated owner) := by
    rw [ownerValue]
    exact TypeIn.arrow argument result argumentFacts.1 resultFacts.1
  refine ⟨argument, result, updated, argumentFacts.1, resultFacts.1, ownerValue,
    ownerTyped, updatedAliases, outside, targets, held, ?_⟩
  intro occurrence sc indexed
  exact held sc (List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩)

end MicroCFTA.SourcePruningEnumerationParametricArrowBucketWitness
