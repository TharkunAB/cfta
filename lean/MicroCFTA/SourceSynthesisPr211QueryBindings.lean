import MicroCFTA.SourceSynthesisOrdinaryTyping

/-!
# Query bindings for the PR211 candidate

This contract follows PR211 at a3092c6c780b7138654b2de00578815fb9df7e6b.
PR211 is merged. This contract retains its reviewed head version. Each original
argument keeps its position and name. Its type becomes the last binding's type.
These laws concern query lists. They do not establish runtime correspondence,
native acceptance, or refinement lookup behavior.
-/
namespace MicroCFTA.SourceSynthesisPr211QueryBindings
open SourceSynthesisTypeSyntax
open SourceSynthesisOrdinaryTyping (queryLookup)

/-- Keep each argument and replace its type with the last binding of its name. -/
def queryBindings (query : Query) : List (String × Ty) :=
  query.queryArguments.map fun entry =>
    (entry.1, (queryLookup query.queryArguments entry.1).getD entry.2)

private theorem lookup_map_types (arguments : List (String × Ty))
    (updateType : String → Ty → Ty) (name : String) :
    List.lookup name (arguments.map fun entry => (entry.1, updateType entry.1 entry.2)) =
      (List.lookup name arguments).map (updateType name) := by
  induction arguments with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, typ⟩ := entry
      by_cases same : name = key
      · subst key
        simp
      · have different : (name == key) = false := beq_eq_false_iff_ne.mpr same
        simpa only [List.map_cons, List.lookup, different] using ih

/-- The full name sequence preserves argument order and repeated occurrences. -/
theorem queryBindings_names (query : Query) :
    (queryBindings query).map Prod.fst = query.queryArguments.map Prod.fst := by
  unfold queryBindings
  rw [List.map_map]
  rfl

/-- The candidate retains every argument occurrence. -/
theorem queryBindings_length (query : Query) :
    (queryBindings query).length = query.queryArguments.length := by
  simp only [queryBindings, List.length_map]

/-- Canonicalization preserves last lookup for every name, including absent names. -/
theorem queryBindings_lookup (query : Query) (name : String) :
    queryLookup (queryBindings query) name = queryLookup query.queryArguments name := by
  change List.lookup name ((query.queryArguments.map fun entry =>
    (entry.1, (queryLookup query.queryArguments entry.1).getD entry.2)).reverse) =
      queryLookup query.queryArguments name
  rw [← List.map_reverse]
  rw [lookup_map_types query.queryArguments.reverse
    (fun key typ => (queryLookup query.queryArguments key).getD typ) name]
  change (queryLookup query.queryArguments name).map
    (fun typ => (queryLookup query.queryArguments name).getD typ) =
      queryLookup query.queryArguments name
  cases queryLookup query.queryArguments name <;> rfl

/-- Every output row has the exact type returned by the original last lookup. -/
theorem queryBindings_member (query : Query) (name : String) (typ : Ty)
    (member : (name, typ) ∈ queryBindings query) :
    queryLookup query.queryArguments name = some typ := by
  obtain ⟨⟨sourceName, sourceType⟩, present, same⟩ := List.mem_map.mp member
  have names : sourceName = name := congrArg Prod.fst same
  subst sourceName
  cases found : queryLookup query.queryArguments name with
  | none =>
      have absent := List.lookup_eq_none_iff.mp found
      have impossible := absent (name, sourceType) (List.mem_reverse.mpr present)
      simp at impossible
  | some lastType =>
      have types : lastType = typ := by
        simpa only [found, Option.getD_some] using congrArg Prod.snd same
      exact congrArg some types

/-- Two output arguments with one name have the same type. -/
theorem queryBindings_coherent (query : Query) (name : String) (first second : Ty)
    (one : (name, first) ∈ queryBindings query)
    (two : (name, second) ∈ queryBindings query) : first = second := by
  exact Option.some.inj
    ((queryBindings_member query name first one).symm.trans
      (queryBindings_member query name second two))

/-- Applying the candidate rule twice preserves the exact ordered argument list. -/
theorem queryBindings_idempotent (query : Query) :
    queryBindings {query with queryArguments := queryBindings query} = queryBindings query := by
  change (queryBindings query).map (fun entry =>
    (entry.1, (queryLookup (queryBindings query) entry.1).getD entry.2)) = queryBindings query
  calc
    _ = (queryBindings query).map (fun entry => entry) := by
      apply List.map_congr_left
      intro entry member
      rw [queryBindings_lookup, queryBindings_member query entry.1 entry.2 member]
      rfl
    _ = queryBindings query := List.map_id' _

end MicroCFTA.SourceSynthesisPr211QueryBindings
