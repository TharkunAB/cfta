import MicroCFTA.KeyedNarySource
import MicroCFTA.KeyedNaryFields

/-!
# Source dispatch for same-key recursive merges

The source omits an empty group list and retains a singleton unchanged.
Only a list with at least two groups adds flat private choice wrappers.
-/
namespace MicroCFTA.KeyedNaryDispatch
open Language GeneratorCombinators KeyedNaryAlignment

/-- Mirror `mergeRecursiveGroups`, including its empty and singleton shortcuts. -/
def mergeGroups (branches : List (Recipe Key Root Symbol α)) : Option (Recipe Key Root Symbol α) :=
  match branches with
  | [] => none
  | [only] => some only
  | first :: second :: rest => some (.choice (first :: second :: rest).length
      (fun index => (first :: second :: rest)[index]))

/-- An absent key group does not become an empty recursive choice. -/
theorem merge_empty : mergeGroups ([] : List (Recipe Key Root Symbol α)) = none := rfl

/-- A singleton group does not acquire a private `Choice 0` wrapper. -/
theorem merge_single (only : Recipe Key Root Symbol α) : mergeGroups [only] = some only := rfl

/-- At least two same-key groups use one flat choice in their source order. -/
theorem merge_many (first second : Recipe Key Root Symbol α) (rest : List (Recipe Key Root Symbol α)) :
    mergeGroups (first :: second :: rest) = some (.choice (first :: second :: rest).length
      (fun index => (first :: second :: rest)[index])) := rfl

/-- Dispatch rejects exactly the empty source group list. -/
theorem merge_absent (branches : List (Recipe Key Root Symbol α)) : mergeGroups branches = none ↔ branches = [] := by
  cases branches with
  | nil => simp [mergeGroups]
  | cons first rest => cases rest <;> simp [mergeGroups]

/-- The indexed flat alternatives are exactly the original ordered group list. -/
theorem merge_order (branches : List (Recipe Key Root Symbol α)) :
    List.ofFn (fun index : Fin branches.length => branches[index]) = branches := by simp

/-- A singleton retains the child's complete value record at every size. -/
theorem singleton_value (only : Recipe Key Root Symbol α) (environment : Key → GroupedRecord.Classes Root) (size : Nat) :
    (mergeGroups [only]).map (fun body => KeyedNarySource.valueRecord body environment size) =
      some (KeyedNarySource.valueRecord only environment size) := rfl

/-- A singleton retains the child's complete private term record at every size. -/
theorem singleton_term (only : Recipe Key Root Symbol α) (environment : Key → GroupedRecord.Classes (EngineTerm Symbol)) (size : Nat) :
    (mergeGroups [only]).map (fun body => KeyedNarySource.termRecord body environment size) =
      some (KeyedNarySource.termRecord only environment size) := rfl

/-- A singleton retains the child's callback and every checked flag. -/
theorem singleton_callback [DecidableEq Symbol]
    (callbacks : KeyedNaryFields.LeafCallbacks Symbol) (roots : Key → RecursiveCallbackTermination.Finite Symbol)
    (only : Recipe Key Root Symbol α) :
    (mergeGroups [only]).map (KeyedNaryFields.compile callbacks roots) =
      some (KeyedNaryFields.compile callbacks roots only) := rfl

/-- The multi-group value record uses the actual flat mass-weighted merge. -/
theorem many_value (first second : Recipe Key Root Symbol α) (rest : List (Recipe Key Root Symbol α))
    (environment : Key → GroupedRecord.Classes Root) (size : Nat) :
    (mergeGroups (first :: second :: rest)).map (fun body => KeyedNarySource.valueRecord body environment size) =
      some (GroupedRecord.merge ((first :: second :: rest).map fun body => KeyedNarySource.valueRecord body environment size)) := by
  simp only [mergeGroups, Option.map_some, KeyedNarySource.valueRecord]
  congr 2
  simpa only [List.map_ofFn, Function.comp_def] using congrArg
    (List.map (fun body => KeyedNarySource.valueRecord body environment size)) (merge_order (first :: second :: rest))

end MicroCFTA.KeyedNaryDispatch
