import MicroCFTA.InternedRecordDepthSource

/-!
# Source Empty depends on lexical Empty tests

An external root can be replaced by an opaque nonempty alternative.
The interpretation retains each fresh binder local until that binder
closes. This projection preserves the physical Empty test through the
complete source syntax. It does not compare different stored plans.
-/
namespace MicroCFTA.SourceCurrentSourceEmptyAbstraction
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedProfileSemantics

private def project (function : Atom → Option Other) : Abstract Atom → Abstract Other
  | none => none
  | some names => if names.any (fun name => (function name).isNone) then none
      else some (names.filterMap function)

private def lift (function : Atom → Option Other) : Sum Unit Atom → Option (Sum Unit Other)
  | .inl token => some (.inl token)
  | .inr atom => (function atom).map Sum.inr

private theorem project_empty (function : Atom → Option Other) (value : Abstract Atom) :
    isEmpty (project function value) = isEmpty value := by
  cases value with
  | none => rfl
  | some names =>
      cases names with
      | nil => rfl
      | cons first rest =>
          cases found : function first <;> simp [project,isEmpty,found]

private theorem project_combine (function : Atom → Option Other) (first second : Abstract Atom) :
    combine (project function first) (project function second) = project function (combine first second) := by
  cases first with
  | none => cases second <;> simp [project,combine]
  | some first =>
      cases second with
      | none => simp [project,combine]
      | some second =>
          simp only [project,combine,List.any_append,List.filterMap_append]
          cases first.any (fun name => (function name).isNone) <;>
            cases second.any (fun name => (function name).isNone) <;> rfl

private theorem project_many (function : Atom → Option Other) (values : List (Abstract Atom)) :
    combineMany (values.map (project function)) = project function (combineMany values) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons,combineMany,ih,project_combine]

private theorem lower_any (function : Atom → Option Other) (names : List (Sum Unit Atom)) :
    (names.filterMap (fun name => match name with | .inl _ => none | .inr atom => some atom)).any
        (fun atom => (function atom).isNone) =
      names.any (fun name => (lift function name).isNone) := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | inl token => simp [lift,ih]
      | inr atom => cases found : function atom <;> simp [lift,found,ih]

private theorem lower_names (function : Atom → Option Other) (names : List (Sum Unit Atom)) :
    (names.filterMap (lift function)).filterMap
        (fun name => match name with | .inl _ => none | .inr atom => some atom) =
      (names.filterMap (fun name => match name with | .inl _ => none | .inr atom => some atom)).filterMap function := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | inl token => simp [lift,ih]
      | inr atom => cases found : function atom <;> simp [lift,found,ih]

private theorem project_lower (function : Atom → Option Other) (value : Abstract (Sum Unit Atom)) :
    lower (project (lift function) value) = project function (lower value) := by
  cases value with
  | none => rfl
  | some names =>
      change lower (if names.any (fun name => (lift function name).isNone) then none
          else some (names.filterMap (lift function))) =
        if (names.filterMap (fun name => match name with | .inl _ => none | .inr atom => some atom)).any
          (fun atom => (function atom).isNone) then none
        else some ((names.filterMap (fun name => match name with | .inl _ => none | .inr atom => some atom)).filterMap function)
      rw [lower_any function names]
      split
      · rfl
      · simp only [lower,lower_names]

private theorem project_map (function : Atom → Option Other) (value : Abstract Atom) :
    project (lift function) (mapNames Sum.inr value) = mapNames Sum.inr (project function value) := by
  cases value with
  | none => rfl
  | some names =>
      have tests : (names.map Sum.inr).any (fun name => (lift function name).isNone) =
          names.any (fun name => (function name).isNone) := by
        rw [List.any_map]
        congr 1
        funext atom
        cases found : function atom <;> simp [lift,found]
      have mapped : (names.map Sum.inr).filterMap (lift function) = (names.filterMap function).map Sum.inr := by
        clear tests
        induction names with
        | nil => rfl
        | cons first rest ih =>
            rw [List.map_cons,List.filterMap_cons,List.filterMap_cons]
            cases found : function first <;> simp only [lift,found,Option.map_none,Option.map_some,
              List.map_cons,ih]
      simp only [mapNames,Option.map_some,project,tests]
      split <;> simp [mapped]

private theorem project_local (function : Atom → Option Other) (environment : List (Abstract Atom)) :
    (some [Sum.inl ()] :: environment.map (mapNames Sum.inr)).map (project (lift function)) =
      some [.inl ()] :: (environment.map (project function)).map (mapNames Sum.inr) := by
  simp only [List.map_cons,List.map_map,Function.comp_def,project_map]
  rfl

mutual
private theorem evaluate_project (function : Atom → Option Other) (expression : Syntax Symbol Guard)
    (environment : List (Abstract Atom)) :
    evaluate expression (environment.map (project function)) = project function (evaluate expression environment) := by
  cases expression with
  | empty => simp [evaluate,project]
  | var index =>
      rw [evaluate,evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map,found,project]
  | node rows =>
      rw [evaluate,evaluate,evaluateEdges_project function rows environment]
      cases evaluateEdges rows environment <;> rfl
  | union members =>
      rw [evaluate,evaluate,evaluateMany_project function members environment,project_many]
  | binder smart body =>
      cases smart with
      | false => simp [evaluate,project]
      | true =>
          rw [evaluate,evaluate,←project_local function environment,
            evaluate_project (lift function) body _,project_lower]
termination_by sizeOf expression

private theorem evaluateMany_project (function : Atom → Option Other) (expressions : List (Syntax Symbol Guard))
    (environment : List (Abstract Atom)) :
    evaluateMany expressions (environment.map (project function)) =
      (evaluateMany expressions environment).map (project function) := by
  cases expressions with
  | nil => simp [evaluateMany]
  | cons first rest =>
      simp only [evaluateMany,evaluate_project function first environment,
        evaluateMany_project function rest environment,List.map_cons]
termination_by sizeOf expressions

private theorem evaluateEdges_project (function : Atom → Option Other) (rows : List (EdgeSyntax Symbol Guard))
    (environment : List (Abstract Atom)) :
    evaluateEdges rows (environment.map (project function)) = evaluateEdges rows environment := by
  cases rows with
  | nil => simp [evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [evaluateEdges,evaluateMany_project function children environment,
            evaluateEdges_project function rest environment,List.all_map,Function.comp_def,project_empty]
termination_by sizeOf rows
end

private theorem project_all (value : Abstract Atom) :
    project (fun _ : Atom => (none : Option Empty)) value =
      if isEmpty value then some [] else none := by
  cases value with
  | none => rfl
  | some names => cases names <;> simp [project,isEmpty]

/-- Full source evaluation has the same Empty test for lexical profiles with equal Empty tests. -/
theorem same_empty (expression : Syntax Symbol Guard)
    (first : List (Abstract Atom)) (second : List (Abstract Other))
    (inputs : first.map isEmpty = second.map isEmpty) :
    isEmpty (evaluate expression first) = isEmpty (evaluate expression second) := by
  have mapped : first.map (project (fun _ : Atom => (none : Option Empty))) =
      second.map (project (fun _ : Other => (none : Option Empty))) := by
    calc
      _ = (first.map isEmpty).map (fun empty => if empty then (some [] : Abstract Empty) else none) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro value _
        exact project_all value
      _ = (second.map isEmpty).map (fun empty => if empty then (some [] : Abstract Empty) else none) :=
        congrArg (List.map (fun empty => if empty then (some [] : Abstract Empty) else none)) inputs
      _ = _ := by
        rw [List.map_map]
        apply List.map_congr_left
        intro value _
        exact (project_all value).symm
  rw [←project_empty (fun _ : Atom => (none : Option Empty)),
    ←project_empty (fun _ : Other => (none : Option Empty)),
    ←evaluate_project,←evaluate_project,mapped]

end MicroCFTA.SourceCurrentSourceEmptyAbstraction
