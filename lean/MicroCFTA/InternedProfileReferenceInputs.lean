import MicroCFTA.InternedSpecialProbeKeys

/-!
# Reference names do not change pure profile classes

Map every external reference to the same literal reference. This map can
identify arbitrary aliases. It preserves empty results, empty captures,
and the distinguished callback argument. Literal input lists of equal
length therefore give the same profile class for complete nested syntax.
-/
namespace MicroCFTA.InternedProfileReferenceInputs
open InternedNestedConstruction InternedProfileSemantics InternedProfileCallbackForm
open InternedRootProfile InternedSpecialProbeKeys
open InternedBinderProtocol (Reference)

/-- External-name maps preserve the symbolic callback argument. -/
theorem symbolic_map (function : Reference → Reference) (body : Syntax Symbol Guard)
    (environment : List Profile) :
    symbolic body (environment.map (mapNames function)) =
      mapNames (Sum.map id function) (symbolic body environment) := by
  have mapped := evaluate_map (Sum.map id function) body
    (some [Sum.inl ()] :: environment.map (mapNames Sum.inr))
  rw [local_map] at mapped
  exact mapped

/-- Mapping external names maps the captured list without changing its length. -/
theorem captures_map (function : Reference → Reference) (names : List (Sum Unit Reference)) :
    captures (names.map (Sum.map id function)) = (captures names).map function := by
  induction names with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [captures] at ih ⊢ <;> exact ih

/-- Mapping external names cannot add or remove the distinguished argument marker. -/
theorem usesArgument_map (function : Reference → Reference) (names : List (Sum Unit Reference)) :
    usesArgument (names.map (Sum.map id function)) = usesArgument names := by
  induction names with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [usesArgument] at ih ⊢ <;> exact ih

/-- The no-capture callback class is preserved and reflected by every external-name map. -/
theorem classified_map (function : Reference → Reference) (body : Syntax Symbol Guard)
    (environment : List Profile) (uses : Bool) :
    Classified body (environment.map (mapNames function)) uses ↔ Classified body environment uses := by
  cases computed : symbolic body environment with
  | none => simp [Classified, symbolic_map, computed, mapNames]
  | some names => simp [Classified, symbolic_map, computed, mapNames, captures_map, usesArgument_map]

/-- Collapsing literal inputs depends only on their count. -/
theorem literal_collapse (names : List Reference) :
    (names.map (fun name => some [name])).map (mapNames (fun _ => Reference.depth)) =
      List.replicate names.length (some [Reference.depth]) := by
  induction names with
  | nil => rfl
  | cons first rest ih => simp [mapNames, ih, List.replicate_succ]

/-- Empty-result classification equals the classification under one repeated canonical name. -/
theorem isEmpty_replicate (body : Syntax Symbol Guard) (names : List Reference) :
    isEmpty (evaluate body (names.map (fun name => some [name]))) =
      isEmpty (evaluate body (List.replicate names.length (some [Reference.depth]))) := by
  have mapped := congrArg isEmpty (evaluate_map (fun _ => Reference.depth) body
    (names.map (fun name => some [name])))
  rw [literal_collapse, isEmpty_map] at mapped
  exact mapped.symm

/-- Equal-length literal-reference inputs give the same empty-result decision, with any aliases. -/
theorem isEmpty_equal_length (body : Syntax Symbol Guard) (first second : List Reference)
    (same : first.length = second.length) :
    isEmpty (evaluate body (first.map (fun name => some [name]))) =
      isEmpty (evaluate body (second.map (fun name => some [name]))) := by
  rw [isEmpty_replicate, isEmpty_replicate, same]

/-- A syntax-derived repeated-name context determines both special callback classes. -/
theorem classified_replicate (body : Syntax Symbol Guard) (names : List Reference) (uses : Bool) :
    Classified body (names.map (fun name => some [name])) uses ↔
      Classified body (List.replicate names.length (some [Reference.depth])) uses := by
  have mapped := classified_map (fun _ => Reference.depth) body (names.map (fun name => some [name])) uses
  rw [literal_collapse] at mapped
  exact mapped.symm

/-- The two special source key classes depend on syntax and scope length, not reference aliases. -/
theorem classified_equal_length (body : Syntax Symbol Guard) (first second : List Reference)
    (same : first.length = second.length) (uses : Bool) :
    Classified body (first.map (fun name => some [name])) uses ↔
      Classified body (second.map (fun name => some [name])) uses := by
  rw [classified_replicate, classified_replicate, same]

/-- Retain opacity, the empty-capture flag, and the argument-use flag. -/
def callbackClass : Abstract (Sum Unit Reference) → Option (Bool × Bool)
  | none => none
  | some names => some ((captures names).isEmpty, usesArgument names)

/-- Arbitrary external-name maps preserve the complete callback classification. -/
theorem callbackClass_map (function : Reference → Reference) (value : Abstract (Sum Unit Reference)) :
    callbackClass (mapNames (Sum.map id function) value) = callbackClass value := by
  cases value with
  | none => rfl
  | some names => simp [callbackClass, mapNames, captures_map, usesArgument_map]

/-- Complete symbolic callback classes equal their repeated-name interpretation. -/
theorem callbackClass_replicate (body : Syntax Symbol Guard) (names : List Reference) :
    callbackClass (symbolic body (names.map (fun name => some [name]))) =
      callbackClass (symbolic body (List.replicate names.length (some [Reference.depth]))) := by
  have mapped := congrArg callbackClass
    (symbolic_map (fun _ => Reference.depth) body (names.map (fun name => some [name])))
  rw [literal_collapse, callbackClass_map] at mapped
  exact mapped.symm

/-- All four symbolic cases agree under equal-length literal input contexts. -/
theorem callbackClass_equal_length (body : Syntax Symbol Guard) (first second : List Reference)
    (same : first.length = second.length) :
    callbackClass (symbolic body (first.map (fun name => some [name]))) =
      callbackClass (symbolic body (second.map (fun name => some [name]))) := by
  rw [callbackClass_replicate, callbackClass_replicate, same]

end MicroCFTA.InternedProfileReferenceInputs
