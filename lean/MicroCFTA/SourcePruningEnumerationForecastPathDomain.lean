import MicroCFTA.SourcePruningEnumerationPathTransport

/-!
# Finite paths from an original guard forecast

The carrier contains the original stored paths and the projected forecast paths.
It contains every suffix of those paths. The forecast can depend on capacity.
This carrier does not give a control bound that is independent of capacity.
-/
namespace MicroCFTA.SourcePruningEnumerationForecastPathDomain
open EnumerationState SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- List a path and each suffix, including the empty path. -/
def suffixes : EqualityTrie.Path → List EqualityTrie.Path
  | [] => [[]]
  | index :: rest => (index :: rest) :: suffixes rest

private theorem suffixes_self (path : EqualityTrie.Path) : path ∈ suffixes path := by
  cases path <;> simp only [suffixes, List.mem_cons, true_or]

private theorem suffixes_tail {whole suffix : EqualityTrie.Path} {index : Nat}
    (member : index :: suffix ∈ suffixes whole) : suffix ∈ suffixes whole := by
  induction whole with
  | nil => simp only [suffixes, List.mem_singleton, List.cons_ne_nil] at member
  | cons first rest ih =>
      simp only [suffixes, List.mem_cons] at member
      rcases member with same | retained
      · cases same
        exact List.mem_cons_of_mem _ (suffixes_self _)
      · exact List.mem_cons_of_mem _ (ih retained)

/-- Read every represented path from the actual projected forecast tries. -/
noncomputable def projectedPaths (guards : List Constraint) : List EqualityTrie.Path :=
  guards.flatMap fun guard =>
    match SourcePruningEnumerationConstraint.project guard with
    | none => []
    | some (tries, _) => tries.flatMap EqualityTrie.fromPathTrie

/-- Form a finite suffix carrier from the original state and guard forecast. -/
noncomputable def carrier (guards : List Constraint) (initial : Core) : List EqualityTrie.Path :=
  (initial.values.flatMap (fun value =>
    (EnumerationSchedule.references value).flatMap (fun sc => EqualityTrie.fromPathTrie sc.trie)) ++
    projectedPaths guards).flatMap suffixes

/-- Every original stored path belongs to the finite carrier. -/
theorem initial_paths (guards : List Constraint) (initial : Core) :
    StatePaths (fun path => path ∈ carrier guards initial) initial := by
  intro value stored sc suspended path represented
  apply List.mem_flatMap.mpr
  refine ⟨path, List.mem_append.mpr (.inl ?_), suffixes_self path⟩
  exact List.mem_flatMap.mpr ⟨value, stored,
    List.mem_flatMap.mpr ⟨sc, suspended, represented⟩⟩

/-- Every projected forecast path belongs to the same finite carrier. -/
theorem projected_paths (guards : List Constraint) (initial : Core) :
    ProjectionPaths guards (fun path => path ∈ carrier guards initial) := by
  intro guard included tries residual projected trie chosen path represented
  apply List.mem_flatMap.mpr
  refine ⟨path, List.mem_append.mpr (.inr ?_), suffixes_self path⟩
  apply List.mem_flatMap.mpr
  refine ⟨guard, included, ?_⟩
  simp only [projected]
  exact List.mem_flatMap.mpr ⟨trie, chosen, represented⟩

/-- Delete one leading child index without leaving the original finite carrier. -/
theorem tail_closed (guards : List Constraint) (initial : Core)
    (index : Nat) (suffix : EqualityTrie.Path)
    (member : index :: suffix ∈ carrier guards initial) :
    suffix ∈ carrier guards initial := by
  obtain ⟨whole, original, retained⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨whole, original, suffixes_tail retained⟩

end MicroCFTA.SourcePruningEnumerationForecastPathDomain
