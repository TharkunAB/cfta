import MicroCFTA.InternedDepthSemantics

/-!
# Free-reference costs in the existing source shape interpretation

The existing shapes decide edge survival and smart binder retention.
Ordered cost lists retain every free-reference occurrence. A retained Mu
adds one cost. Ordinary constructors and unions add no cost. This pure
interpretation does not yet assert correspondence with cached execution.
-/
namespace MicroCFTA.InternedOccurrenceCostSemantics
open InternedNestedConstruction
open InternedDepthSemantics (Shape)

/-- Rename occurrence names and retain their exact binder costs. -/
def rename (function : Atom → Other) (values : List (Atom × Nat)) : List (Other × Nat) :=
  values.map (fun item => (function item.1, item.2))

/-- Remove the bound local and add the retained binder cost to each capture. -/
def lower (shift : Nat) (values : List (Sum Unit Atom × Nat)) : List (Atom × Nat) :=
  values.filterMap fun item => match item.1 with
    | .inl _ => none
    | .inr name => some (name, item.2 + shift)

/-- Raw binders always remain. Smart binders remain only for a deep local occurrence. -/
def binderShift (smart : Bool) (body : Shape (Sum Unit Atom)) : Nat :=
  if !smart || InternedDepthSemantics.hasLocal body.deep then 1 else 0

mutual
/-- Interpret each free occurrence with the Mu cost of its actual source path. -/
def evaluate {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) : List (Atom × Nat) :=
  match expression with
  | .empty => []
  | .var index => occurrences[index]?.getD []
  | .node edges => evaluateEdges edges environment occurrences
  | .union members => evaluateMany members environment occurrences
  | .binder smart body =>
      let inner := ⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)
      lower (binderShift smart (InternedDepthSemantics.evaluate body inner))
        (evaluate body inner ([(Sum.inl (), 0)] :: occurrences.map (rename Sum.inr)))
termination_by sizeOf expression

/-- Ordered union operands retain the union of their occurrence lists. -/
def evaluateMany {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) : List (Atom × Nat) :=
  match expressions with
  | [] => []
  | first :: rest => evaluate first environment occurrences ++ evaluateMany rest environment occurrences
termination_by sizeOf expressions

/-- Each surviving edge retains every original child occurrence at its original cost. -/
def evaluateEdges {Atom : Type} (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) : List (Atom × Nat) :=
  match expressions with
  | [] => []
  | .mk _ _ children :: rest =>
      (if (InternedDepthSemantics.evaluateMany children environment).any Shape.isEmpty then []
        else evaluateMany children environment occurrences) ++ evaluateEdges rest environment occurrences
termination_by sizeOf expressions
end

/-- Composing external renamings preserves all occurrence costs. -/
theorem rename_rename (first : Atom → Other) (second : Other → Result) (values : List (Atom × Nat)) :
    rename second (rename first values) = rename (second ∘ first) values := by
  simp [rename, List.map_map, Function.comp_def]

/-- Renaming distributes over the ordered occurrence union. -/
theorem rename_append (function : Atom → Other) (first second : List (Atom × Nat)) :
    rename function (first ++ second) = rename function first ++ rename function second := by
  simp [rename]

/-- External renaming commutes with local removal and the exact retained binder cost. -/
theorem lower_rename (function : Atom → Other) (shift : Nat) (values : List (Sum Unit Atom × Nat)) :
    lower shift (rename (Sum.map id function) values) = rename function (lower shift values) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨name, cost⟩
      cases name <;> simp [lower, rename] at ih ⊢ <;> exact ih

/-- External renaming preserves the existing deep-local retention decision. -/
theorem binderShift_map (function : Atom → Other) (smart : Bool) (body : Shape (Sum Unit Atom)) :
    binderShift smart (body.map (Sum.map id function)) = binderShift smart body := by
  simp [binderShift, Shape.map, InternedDepthSemantics.hasLocal_map]

/-- The fresh local occurrence remains distinct while external occurrences are renamed. -/
theorem local_rename (function : Atom → Other) (occurrences : List (List (Atom × Nat))) :
    ([(Sum.inl (), 0)] :: occurrences.map (rename Sum.inr)).map (rename (Sum.map id function)) =
      [(Sum.inl (), 0)] :: (occurrences.map (rename function)).map (rename Sum.inr) := by
  simp [rename, List.map_map, Function.comp_def]

mutual
/-- Full nested cost interpretation commutes with arbitrary external-name maps. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (expression : Syntax Symbol Guard)
    (environment : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) :
    evaluate expression (environment.map (Shape.map function)) (occurrences.map (rename function)) =
      rename function (evaluate expression environment occurrences) := by
  cases expression with
  | empty => simp [evaluate, rename]
  | var index =>
      rw [evaluate, evaluate]
      cases found : occurrences[index]? <;> simp [List.getElem?_map, found, rename]
  | node edges => simpa only [evaluate] using evaluateEdges_map function edges environment occurrences
  | union members => simpa only [evaluate] using evaluateMany_map function members environment occurrences
  | binder smart body =>
      rw [evaluate, evaluate, ← InternedDepthSemantics.local_map function environment,
        ← local_rename function occurrences, InternedDepthSemantics.evaluate_map,
        evaluate_map (Sum.map id function), binderShift_map, lower_rename]
termination_by sizeOf expression

/-- External maps preserve the complete ordered union occurrence list. -/
theorem evaluateMany_map {Atom Other : Type} (function : Atom → Other) (expressions : List (Syntax Symbol Guard))
    (environment : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) :
    evaluateMany expressions (environment.map (Shape.map function)) (occurrences.map (rename function)) =
      rename function (evaluateMany expressions environment occurrences) := by
  cases expressions with
  | nil => simp [evaluateMany, rename]
  | cons first rest => rw [evaluateMany, evaluateMany, evaluate_map function, evaluateMany_map function, rename_append]
termination_by sizeOf expressions

/-- External maps preserve edge deletion and every surviving child cost. -/
theorem evaluateEdges_map {Atom Other : Type} (function : Atom → Other) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) :
    evaluateEdges expressions (environment.map (Shape.map function)) (occurrences.map (rename function)) =
      rename function (evaluateEdges expressions environment occurrences) := by
  cases expressions with
  | nil => simp [evaluateEdges, rename]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [evaluateEdges, evaluateEdges, InternedDepthSemantics.evaluateMany_map function children environment]
          simp only [List.any_map, Function.comp_def, InternedDepthSemantics.isEmpty_map]
          rw [evaluateEdges_map function, rename_append]
          congr 1
          split <;> simp [rename, evaluateMany_map function children environment occurrences]
termination_by sizeOf expressions
end

/-- Interpret one fresh symbolic callback argument with all original captured occurrence costs. -/
def symbolic (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) : List (Sum Unit Atom × Nat) :=
  evaluate expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))
    ([(Sum.inl (), 0)] :: occurrences.map (rename Sum.inr))

/-- Supply the callback's literal argument and retain each external name. -/
def supply (argument : Atom) : Sum Unit Atom → Atom
  | .inl _ => argument
  | .inr name => name

/-- The captured part removes only the distinct symbolic local. -/
def captured (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) : List (Atom × Nat) :=
  lower 0 (symbolic expression environment occurrences)

/-- Lowering retains exactly the external occurrences and adds the requested cost. -/
theorem lower_member (shift : Nat) (values : List (Sum Unit Atom × Nat)) (name : Atom) (cost : Nat) :
    (name, cost) ∈ lower shift values ↔
      ∃ prior, (Sum.inr name, prior) ∈ values ∧ cost = prior + shift := by
  constructor
  · intro member
    obtain ⟨⟨atom, prior⟩, present, equal⟩ := List.mem_filterMap.mp member
    cases atom with
    | inl => cases equal
    | inr other =>
        have fields : other = name ∧ prior + shift = cost := by simpa only [Option.some.injEq, Prod.mk.injEq] using equal
        rcases fields with ⟨rfl, rfl⟩
        exact ⟨prior, present, rfl⟩
  · rintro ⟨prior, present, rfl⟩
    exact List.mem_filterMap.mpr ⟨(Sum.inr name, prior), present, rfl⟩

/-- A captured cost is exactly an external occurrence of the symbolic body. -/
theorem captured_member (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) (name : Atom) (cost : Nat) :
    (name, cost) ∈ captured expression environment occurrences ↔
      (Sum.inr name, cost) ∈ symbolic expression environment occurrences := by
  rw [captured, lower_member]
  simp

/-- Each interpreted binder removes its local and adds only its actual retained-wrapper cost. -/
theorem binder_member (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) (name : Atom) (cost : Nat) :
    (name, cost) ∈ evaluate (.binder smart expression) environment occurrences ↔
      ∃ prior, (name, prior) ∈ captured expression environment occurrences ∧
        cost = prior + binderShift smart (InternedDepthSemantics.evaluate expression
          (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))) := by
  rw [evaluate]
  change (name, cost) ∈ lower _ (symbolic expression environment occurrences) ↔ _
  rw [lower_member]
  simp only [captured_member]

/-- Supplying a literal argument renames the complete symbolic cost interpretation. -/
theorem supplied_costs (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) (argument : Atom) :
    evaluate expression (⟨[argument], [], false, 0⟩ :: environment) ([(argument, 0)] :: occurrences) =
      rename (supply argument) (symbolic expression environment occurrences) := by
  have mapped := evaluate_map (supply argument) expression
    (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))
    ([(Sum.inl (), 0)] :: occurrences.map (rename Sum.inr))
  simpa [symbolic, Shape.map, rename, supply, List.map_map, Function.comp_def] using mapped

/-- Away from the supplied argument, renaming retains exactly the captured costs. -/
theorem supplied_member (argument name : Atom) (different : name ≠ argument)
    (values : List (Sum Unit Atom × Nat)) (cost : Nat) :
    (name, cost) ∈ rename (supply argument) values ↔ (name, cost) ∈ lower 0 values := by
  rw [lower_member]
  constructor
  · intro member
    obtain ⟨⟨atom, prior⟩, present, equal⟩ := List.mem_map.mp member
    cases atom with
    | inl => exact False.elim (different (congrArg Prod.fst equal).symm)
    | inr other =>
        have fields : other = name ∧ prior = cost := Prod.mk.inj equal
        rcases fields with ⟨rfl, rfl⟩
        exact ⟨prior, present, by simp⟩
  · rintro ⟨prior, present, same⟩
    have equal : cost = prior := by simpa using same
    subst cost
    exact List.mem_map.mpr ⟨(Sum.inr name, prior), present, rfl⟩

/-- Any two literal callback arguments observe the same costs for every other name. -/
theorem evaluate_other (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (occurrences : List (List (Atom × Nat))) (argument name : Atom) (different : name ≠ argument) (cost : Nat) :
    (name, cost) ∈ evaluate expression (⟨[argument], [], false, 0⟩ :: environment) ([(argument, 0)] :: occurrences) ↔
      (name, cost) ∈ captured expression environment occurrences := by
  rw [supplied_costs]
  exact supplied_member argument name different _ cost

end MicroCFTA.InternedOccurrenceCostSemantics
