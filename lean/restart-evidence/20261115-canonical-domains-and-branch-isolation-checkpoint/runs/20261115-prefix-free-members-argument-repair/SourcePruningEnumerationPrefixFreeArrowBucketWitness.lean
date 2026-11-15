import MicroCFTA.SourcePruningEnumerationSharedArrowBucketFragmentWitness
import MicroCFTA.SourceSynthesisNormalizedVariablePaths
import MicroCFTA.SourceSynthesisGuardRegions

/-!
# One finite assignment for prefix-free arrow paths

The whole bucket supplies one finite ordered list of represented paths.
A finite arrow tree ends at every path in that list.
Actual selection separates every raw target from the selected class.
The assignment uses this tree for that class and one leaf for all others.
The source projection result proves joint prefix freedom for one original guard.
It does not prove that every later bucket retains that property.
-/
namespace MicroCFTA.SourcePruningEnumerationPrefixFreeArrowBucketWitness
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

set_option autoImplicit false
variable {Typing : Type} {width : Nat}

private def base : Term Symbol := .node (literal "var1") []

private def tails (index : Nat) (paths : List EqualityTrie.Path) : List EqualityTrie.Path :=
  paths.filterMap fun path => match path with
    | [] => none
    | first :: rest => if first = index then some rest else none

private theorem mem_tails (index : Nat) (paths : List EqualityTrie.Path) (suffix : EqualityTrie.Path) :
    suffix ∈ tails index paths ↔ index :: suffix ∈ paths := by
  simp only [tails, List.mem_filterMap]
  constructor
  · rintro ⟨path, member, selected⟩
    cases path with
    | nil => cases selected
    | cons first rest =>
        by_cases same : first = index
        · simp only [same, ↓reduceIte, Option.some.injEq] at selected
          subst first
          subst rest
          exact member
        · simp [same] at selected
  · intro member
    exact ⟨index :: suffix, member, by simp⟩

private def tree : Nat → List EqualityTrie.Path → Term Symbol
  | 0, _ => base
  | fuel + 1, paths =>
      if [] ∈ paths then base else .node (literal "->")
        [.node (literal "(->)") [], tree fuel (tails 1 paths), tree fuel (tails 2 paths)]

private theorem tree_typeIn (catalog : List (String × Nat)) (fuel : Nat)
    (paths : List EqualityTrie.Path) : TypeIn catalog (tree fuel paths) := by
  induction fuel generalizing paths with
  | zero => exact .leaf "var1" (by simp)
  | succ fuel ih =>
      simp only [tree]
      split
      · exact .leaf "var1" (by simp)
      · exact .arrow _ _ (ih _) (ih _)

private theorem tree_paths (fuel : Nat) (paths : List EqualityTrie.Path)
    (free : ∀ first ∈ paths, ∀ second ∈ paths, first.IsPrefix second → first = second)
    (arrows : ∀ path ∈ paths, ∀ index ∈ path, index = 1 ∨ index = 2)
    (bounded : ∀ path ∈ paths, path.length < fuel) :
    ∀ path ∈ paths, (tree fuel paths).atPath path = some base := by
  induction fuel generalizing paths with
  | zero =>
      intro path member
      have impossible := bounded path member
      omega
  | succ fuel ih =>
      intro path member
      cases path with
      | nil => simp only [tree, ite_eq_left member, Term.atPath]
      | cons index rest =>
          have noEmpty : [] ∉ paths := by
            intro empty
            have same := free [] empty (index :: rest) member ⟨index :: rest, rfl⟩
            cases same
          have tailFree : ∀ first ∈ tails index paths, ∀ second ∈ tails index paths,
              first.IsPrefix second → first = second := by
            intro first firstMember second secondMember initial
            have same := free (index :: first) ((mem_tails index paths first).mp firstMember)
              (index :: second) ((mem_tails index paths second).mp secondMember)
              (List.cons_prefix_cons.mpr ⟨rfl, initial⟩)
            exact (List.cons.inj same).2
          have tailArrows : ∀ path ∈ tails index paths, ∀ child ∈ path, child = 1 ∨ child = 2 := by
            intro path included child present
            exact arrows (index :: path) ((mem_tails index paths path).mp included)
              child (List.mem_cons_of_mem index present)
          have tailBound : ∀ path ∈ tails index paths, path.length < fuel := by
            intro path included
            have shorter := bounded (index :: path) ((mem_tails index paths path).mp included)
            simp only [List.length_cons] at shorter
            omega
          have located := ih (tails index paths) tailFree tailArrows tailBound
            rest ((mem_tails index paths rest).mpr member)
          rcases arrows (index :: rest) member index List.mem_cons_self with rfl | rfl
          · simpa only [tree, ite_eq_right noEmpty, Term.atPath,
              List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some] using located
          · simpa only [tree, ite_eq_right noEmpty, Term.atPath,
              List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some] using located

/-- UF-equivalent raw targets cannot occur at two strictly nested represented paths. -/
theorem strict_prefix_alias_no_bucket_assignment
    (forest : UnionFind.Forest) (owner : Nat) (bucket : List Suspended)
    (first second : Suspended) (firstMember : first ∈ bucket) (secondMember : second ∈ bucket)
    (path rest : EqualityTrie.Path) (proper : rest ≠ [])
    (firstPath : path ∈ EqualityTrie.fromPathTrie first.trie)
    (secondPath : path ++ rest ∈ EqualityTrie.fromPathTrie second.trie)
    (aliased : UnionFind.SameClass forest first.var second.var) :
    ¬ ∃ rho : Nat → Term Symbol,
      UnionFind.Satisfies forest rho ∧ ∀ sc ∈ bucket, Suspended.Holds rho (rho owner) sc := by
  rintro ⟨rho, aliases, held⟩
  apply strict_prefix_paths_not_equal (rho owner) path rest proper
  refine ⟨rho first.var, held first firstMember path firstPath, ?_⟩
  simpa only [aliases first.var second.var aliased] using
    held second secondMember (path ++ rest) secondPath

/-- The actual projection of one original source guard retains joint prefix freedom. -/
theorem projected_original_source_paths_prefix_free
    (typ : SourceSynthesisTypeSyntax.Ty) (tries : List EqualityTrie.Trie)
    (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project
      (SourceSynthesisGeneralizeSyntax.eqGuard (SourceSynthesisGeneralizeSyntax.equalityClasses typ)) =
        some (tries, residual)) :
    ∀ first ∈ tries.flatMap EqualityTrie.fromPathTrie,
      ∀ second ∈ tries.flatMap EqualityTrie.fromPathTrie,
        first.IsPrefix second → first = second := by
  classical
  let guard := SourceSynthesisGeneralizeSyntax.eqGuard
    (SourceSynthesisGeneralizeSyntax.equalityClasses typ)
  have accessor : SourceCompactGuards.sourceEqualities guard = guard.equalities :=
    SourceSynthesisGuardRegions.eqGuard_accessor _
  have cached : SourceEqualityGuardReadback.Cached guard.equalities := by
    dsimp only [guard]
    rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
    exact SourceEqualityGuardReadback.normalize_cached _
  cases physical : SourceCompactGuards.sourceEqualities guard with
  | none =>
      have impossible : SourcePruningEnumerationConstraint.project guard = none := by
        simp only [SourcePruningEnumerationConstraint.project, physical]
      rw [impossible] at projected
      cases projected
  | some classes =>
      have storedClasses : guard.equalities = some classes := accessor.symm.trans physical
      have readback := SourcePruningEnumerationConstraint.project_complete guard cached
      rw [physical] at readback
      have triesSame : EnumerationEquality.readClasses classes = tries := by
        have same := readback.1.symm.trans projected
        exact congrArg Prod.fst (Option.some.inj same)
      have original : ∀ path ∈ tries.flatMap EqualityTrie.fromPathTrie,
          path ∈ EqualityNormalize.members (guard.equalities.getD []) := by
        intro path included
        obtain ⟨trie, present, represented⟩ := List.mem_flatMap.mp included
        rw [← triesSame] at present
        obtain ⟨paths, pathsMember, rfl⟩ := List.mem_map.mp present
        rw [storedClasses]
        exact (EqualityNormalize.mem_members path classes).mpr
          ⟨paths, pathsMember, (readback.2.2.1 paths pathsMember path).mp represented⟩
      intro first firstMember second secondMember initial
      exact SourceSynthesisNormalizedVariablePaths.eqGuard_prefix_free typ first second
        (original first firstMember) (original second secondMember) initial

/-- Actual selection admits one finite Type assignment for the whole prefix-free arrow bucket. -/
theorem selected_prefix_free_arrow_bucket_assignment
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached) (uv handle : Nat)
    (safe : Safe before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selected : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (bucket : List Suspended)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket))
    (prefixFree : ∀ first ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
      ∀ second ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
        first.IsPrefix second → first = second)
    (arrowIndices : ∀ path ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
      ∀ index ∈ path, index = 1 ∨ index = 2)
    (catalog : List (String × Nat)) :
    ∃ rho : Nat → Term Symbol,
      UnionFind.Satisfies before.core.representatives rho ∧
      (∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        Suspended.Holds rho (rho uv) sc) ∧
      (∀ slot, TypeIn catalog (rho slot)) ∧
      ∀ (holds : SourceSynthesisGeneralizeSyntax.Guard → Term Symbol → Bool),
        (∀ term, holds SourceSynthesisGeneralizeSyntax.top term = true) →
        ∀ slot, InternedGuardedSyntax.evaluate holds []
          (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal
            (SourceSynthesisTypeSyntax.allTypes SourceSynthesisGeneralizeSyntax.top catalog))
          (rho slot) := by
  classical
  obtain ⟨ready, incoming, _realized⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv valid safe selected
  let paths := bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie)
  let chosen := tree (EqualityTrie.pathBudget paths) paths
  have chosenMember : TypeIn catalog chosen := tree_typeIn catalog _ paths
  have chosenPaths : ∀ path ∈ paths, chosen.atPath path = some base :=
    tree_paths _ paths prefixFree arrowIndices (EqualityTrie.pathBudget_sufficient paths)
  let rho : Nat → Term Symbol := fun slot =>
    if UnionFind.SameClass before.core.representatives uv slot then chosen else base
  obtain ⟨size, rootRead⟩ := ready.root
  have selfClass : UnionFind.SameClass before.core.representatives uv uv :=
    ⟨uv, size, rootRead, rootRead⟩
  have ownerValue : rho uv = chosen := by simp only [rho, ite_eq_left selfClass]
  have targetValue : ∀ sc ∈ bucket, rho sc.var = base := by
    intro sc member
    have separate := incoming (.unenumerated (some handle) bucket)
      (List.mem_iff_getElem?.mpr ⟨uv, stored⟩) sc member
    simp only [rho, ite_eq_right separate]
  have aliases : UnionFind.Satisfies before.core.representatives rho := by
    intro left right same
    by_cases first : UnionFind.SameClass before.core.representatives uv left
    · have second := UnionFind.sameClass_trans first same
      simp only [rho, ite_eq_left first, ite_eq_left second]
    · have second : ¬UnionFind.SameClass before.core.representatives uv right := by
        intro joined
        exact first (UnionFind.sameClass_trans joined (UnionFind.sameClass_symm same))
      simp only [rho, ite_eq_right first, ite_eq_right second]
  have held : ∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc := by
    intro sc member path represented
    rw [ownerValue, targetValue sc member]
    exact chosenPaths path (List.mem_flatMap.mpr ⟨sc, member, represented⟩)
  have members : ∀ slot, TypeIn catalog (rho slot) := by
    intro slot
    dsimp only [rho]
    split
    · exact chosenMember
    · exact .leaf "var1" (by simp)
  refine ⟨rho, aliases, held, ?_, members, ?_⟩
  · intro occurrence sc indexed
    exact held sc (List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩)
  · intro holds topHeld slot
    exact (members slot).member holds topHeld

/-- One assignment also satisfies every stored fragment equation after pending reconstruction. -/
theorem selected_prefix_free_arrow_bucket_fragment_assignment
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached) (uv handle : Nat)
    (safe : Safe before.core)
    (level : Nat → Nat) (frontier : Nat)
    (stratified : EnumerationOrder.Stratified before.core level frontier)
    (pending : EnumerationReferences.PendingReferences before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selected : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (bucket : List Suspended)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket))
    (prefixFree : ∀ first ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
      ∀ second ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
        first.IsPrefix second → first = second)
    (arrowIndices : ∀ path ∈ bucket.flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie),
      ∀ index ∈ path, index = 1 ∨ index = 2)
    (catalog : List (String × Nat)) :
    ∃ rho : Nat → Term Symbol,
      UnionFind.Satisfies before.core.representatives rho ∧
      (∀ slot fragment, before.core.values[slot]? = some (.enumerated fragment) →
        rho slot = fill rho fragment) ∧
      (∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        Suspended.Holds rho (rho uv) sc) ∧
      ∀ slot node scs, before.core.values[slot]? = some (.unenumerated node scs) →
        TypeIn catalog (rho slot) := by
  obtain ⟨baseAssignment, baseAliases, baseHeld, _baseIndexed, baseMembers, _sourceMembers⟩ :=
    selected_prefix_free_arrow_bucket_assignment stop order metadata caller before uv handle
      safe valid selected bucket stored prefixFree arrowIndices catalog
  obtain ⟨rho, aliases, equations, agreement⟩ :=
    EnumerationPendingAssignment.stratified_extend_pending before.core safe level frontier
      stratified baseAssignment baseAliases
  have held := EnumerationPendingAgreement.stored_bucket_holds_transfer before.core safe pending
    baseAssignment rho baseAliases aliases
    (fun slot node scs atSlot => (agreement slot node scs atSlot).symm)
    uv (some handle) bucket stored baseHeld
  refine ⟨rho, aliases, equations, held, ?_, ?_⟩
  · intro occurrence sc indexed
    exact held sc (List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩)
  · intro slot node scs atSlot
    rw [agreement slot node scs atSlot]
    exact baseMembers slot

end MicroCFTA.SourcePruningEnumerationPrefixFreeArrowBucketWitness
