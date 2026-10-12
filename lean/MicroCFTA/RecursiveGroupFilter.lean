import MicroCFTA.KeyedSource

/-!
# Key-only filtering of recursive group records

The recursive source branch traverses the ascending key map with filterM in
ExceptT. It keeps complete records and stops at the first callback error.
This model records the predicate effects. It never reads a group member.
-/
namespace MicroCFTA.RecursiveGroupFilter
universe uKey uValue uEffect uError uSource

/-- A predicate call can update effect state before it returns a decision or error. -/
abbrev Predicate (Key : Type uKey) (Effect : Type uEffect) (Error : Type uError) :=
  Key → Effect → Except Error Bool × Effect

/-- The complete filter result retains its actual callback trace and effect state. -/
structure Outcome (Key : Type uKey) (Value : Type uValue) (Effect : Type uEffect) (Error : Type uError) where
  result : Except Error (List (Key × Value))
  state : Effect
  calls : List (Key × Except Error Bool)

/-- Execute the source filterM order on the already ascending map entries. -/
def run (predicate : Predicate Key Effect Error) : List (Key × Value) → Effect → Outcome Key Value Effect Error
  | [], state => ⟨.ok [], state, []⟩
  | entry :: rest, state =>
      let decision := predicate entry.1 state
      match decision.1 with
      | .error error => ⟨.error error, decision.2, [(entry.1, .error error)]⟩
      | .ok keep =>
          let next := run predicate rest decision.2
          ⟨next.result.map (fun retained => if keep then entry :: retained else retained),
            next.state, (entry.1, .ok keep) :: next.calls⟩

/-- Every executed callback belongs to an initial segment of the input key order. -/
theorem calls_prefix (predicate : Predicate Key Effect Error) (entries : List (Key × Value)) (state : Effect) :
    ∃ remaining, (run predicate entries state).calls.map Prod.fst ++ remaining = entries.map Prod.fst := by
  induction entries generalizing state with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
      cases decision : (predicate entry.1 state).1 with
      | error error => exact ⟨rest.map Prod.fst, by simp [run, decision]⟩
      | ok keep =>
          obtain ⟨remaining, same⟩ := ih (predicate entry.1 state).2
          exact ⟨remaining, by simpa [run, decision] using congrArg (List.cons entry.1) same⟩

/-- Successful filtering calls the predicate once for every input entry in source order. -/
theorem successful_calls (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (retained : List (Key × Value)) (success : (run predicate entries state).result = .ok retained) :
    (run predicate entries state).calls.map Prod.fst = entries.map Prod.fst := by
  induction entries generalizing state retained with
  | nil => rfl
  | cons entry rest ih =>
      cases decision : (predicate entry.1 state).1 with
      | error error => simp [run, decision] at success
      | ok keep =>
          cases result : (run predicate rest (predicate entry.1 state).2).result with
          | error error => simp [run, decision, result, Except.map] at success
          | ok later =>
              simpa [run, decision] using congrArg (List.cons entry.1) (ih _ later result)

/-- A trace error is the last call, and every preceding callback returned a Boolean decision. -/
theorem failed_calls (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (error : Error) (failed : (run predicate entries state).result = .error error) :
    ∃ before key, (run predicate entries state).calls = before ++ [(key, .error error)] ∧
      ∀ event ∈ before, ∃ keep, event.2 = .ok keep := by
  induction entries generalizing state with
  | nil => simp [run] at failed
  | cons entry rest ih =>
      cases decision : (predicate entry.1 state).1 with
      | error cause =>
          have same : cause = error := by simpa [run, decision] using failed
          subst cause
          exact ⟨[], entry.1, by simp [run, decision], by simp⟩
      | ok keep =>
          cases result : (run predicate rest (predicate entry.1 state).2).result with
          | ok later => simp [run, decision, result, Except.map] at failed
          | error cause =>
              have same : cause = error := by simpa [run, decision, result, Except.map] using failed
              subst cause
              obtain ⟨before, key, same, earlier⟩ := ih _ result
              refine ⟨(entry.1, .ok keep) :: before, key, ?_, ?_⟩
              · simp [run, decision, same]
              · intro event member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨keep, rfl⟩
                · exact earlier event member

/-- Successful results retain a subsequence of the original complete records. -/
theorem retained_sublist (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (retained : List (Key × Value)) (success : (run predicate entries state).result = .ok retained) :
    retained.Sublist entries := by
  induction entries generalizing state retained with
  | nil =>
      have same : retained = [] := by simpa [run] using success.symm
      subst retained
      exact .slnil
  | cons entry rest ih =>
      cases decision : (predicate entry.1 state).1 with
      | error error => simp [run, decision] at success
      | ok keep =>
          cases result : (run predicate rest (predicate entry.1 state).2).result with
          | error error => simp [run, decision, result, Except.map] at success
          | ok later =>
              have laterSub := ih _ later result
              cases keep with
              | false =>
                  have same : retained = later := by simpa [run, decision, result, Except.map] using success.symm
                  subst retained
                  exact .cons _ laterSub
              | true =>
                  have same : retained = entry :: later := by simpa [run, decision, result, Except.map] using success.symm
                  subst retained
                  exact .cons_cons _ laterSub

/-- Every recorded key is an original key, also on failure. -/
theorem called_key (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (key : Key) (decision : Except Error Bool)
    (called : (key, decision) ∈ (run predicate entries state).calls) : key ∈ entries.map Prod.fst := by
  obtain ⟨remaining, same⟩ := calls_prefix predicate entries state
  rw [← same]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨(key, decision), called, rfl⟩)

/-- A source map has unique keys, so each predicate is called at most once. -/
theorem calls_unique (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (unique : (entries.map Prod.fst).Nodup) (state : Effect) :
    ((run predicate entries state).calls.map Prod.fst).Nodup := by
  obtain ⟨remaining, same⟩ := calls_prefix predicate entries state
  rw [← same] at unique
  exact (List.nodup_append.mp unique).1

/-- Filtering preserves the map's sorted key relation and its unique-key property. -/
theorem retained_order (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (retained : List (Key × Value)) (success : (run predicate entries state).result = .ok retained)
    (relation : Key → Key → Prop) (ordered : entries.Pairwise (fun left right => relation left.1 right.1)) :
    retained.Pairwise (fun left right => relation left.1 right.1) :=
  ordered.sublist (retained_sublist predicate entries state retained success)

/-- A successful unique-key filter retains exactly the keys whose actual callback returned True. -/
theorem retained_exact [DecidableEq Key] (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (unique : (entries.map Prod.fst).Nodup) (state : Effect) (retained : List (Key × Value))
    (success : (run predicate entries state).result = .ok retained) (entry : Key × Value) :
    entry ∈ retained ↔ entry ∈ entries ∧ (entry.1, .ok true) ∈ (run predicate entries state).calls := by
  induction entries generalizing state retained with
  | nil =>
      have same : retained = [] := by simpa [run] using success.symm
      simp [same]
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp unique
      have noHead : ∀ decision, (first.1, decision) ∉ (run predicate rest (predicate first.1 state).2).calls := by
        intro decision present
        exact distinct.1 (called_key predicate rest _ first.1 decision present)
      have noSame : ∀ entry ∈ rest, entry.1 ≠ first.1 := by
        intro entry member same
        exact distinct.1 (same ▸ List.mem_map.mpr ⟨entry, member, rfl⟩)
      cases decision : (predicate first.1 state).1 with
      | error error => simp [run, decision] at success
      | ok keep =>
          cases result : (run predicate rest (predicate first.1 state).2).result with
          | error error => simp [run, decision, result, Except.map] at success
          | ok later =>
              have tail := ih distinct.2 _ later result
              cases keep with
              | false =>
                  have same : retained = later := by simpa [run, decision, result, Except.map] using success.symm
                  subst retained
                  simp only [run, decision, List.mem_cons, Prod.mk.injEq, Except.ok.injEq, Bool.true_eq_false,
                    and_false, false_or]
                  rw [tail]
                  constructor
                  · rintro ⟨member, called⟩; exact ⟨Or.inr member, called⟩
                  · rintro ⟨rfl | member, called⟩
                    · exact False.elim (noHead (.ok true) called)
                    · exact ⟨member, called⟩
              | true =>
                  have same : retained = first :: later := by simpa [run, decision, result, Except.map] using success.symm
                  subst retained
                  simp only [List.mem_cons, run, decision, Prod.mk.injEq, and_true]
                  rw [tail]
                  constructor
                  · rintro (rfl | ⟨member, called⟩)
                    · exact ⟨Or.inl rfl, Or.inl rfl⟩
                    · exact ⟨Or.inr member, Or.inr called⟩
                  · rintro ⟨rfl | member, accepted⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨member, accepted.resolve_left (noSame entry member)⟩

/-- Changing every opaque record leaves all predicate effects and callback decisions unchanged. -/
theorem effects_key_only (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (state : Effect) (transform : Value → Other) :
    (run predicate (entries.map fun entry => (entry.1, transform entry.2)) state).state =
      (run predicate entries state).state ∧
    (run predicate (entries.map fun entry => (entry.1, transform entry.2)) state).calls =
      (run predicate entries state).calls := by
  induction entries generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
      cases decision : (predicate entry.1 state).1 with
      | error error => simp [run, decision]
      | ok keep =>
          have next := ih (predicate entry.1 state).2
          simp [run, decision, next.1, next.2]

/-- Functional readback of the unique-key map rebuilt from retained ascending entries. -/
def lookup [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | entry :: rest => if key = entry.1 then some entry.2 else lookup key rest

/-- Unique-key map readback returns exactly its stored complete entry. -/
theorem lookup_member [DecidableEq Key] (entries : List (Key × Value))
    (unique : (entries.map Prod.fst).Nodup) (key : Key) (value : Value) :
    lookup key entries = some value ↔ (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup]
  | cons entry rest ih =>
      rcases entry with ⟨other, stored⟩
      have distinct := List.nodup_cons.mp unique
      by_cases same : key = other
      · subst other
        have absent : (key, value) ∉ rest := by
          intro present
          exact distinct.1 (List.mem_map.mpr ⟨(key, value), present, rfl⟩)
        simp [lookup, absent, Prod.mk.injEq, eq_comm]
      · simpa [lookup, same, Prod.mk.injEq] using ih distinct.2

/-- Rebuilding the map preserves exactly each accepted original key and its whole record. -/
theorem lookup_retained [DecidableEq Key] (predicate : Predicate Key Effect Error) (entries : List (Key × Value))
    (unique : (entries.map Prod.fst).Nodup) (state : Effect) (retained : List (Key × Value))
    (success : (run predicate entries state).result = .ok retained) (key : Key) (value : Value) :
    lookup key retained = some value ↔
      lookup key entries = some value ∧ (key, .ok true) ∈ (run predicate entries state).calls := by
  have retainedUnique := unique.sublist ((retained_sublist predicate entries state retained success).map Prod.fst)
  rw [lookup_member retained retainedUnique, lookup_member entries unique]
  exact retained_exact predicate entries unique state retained success (key, value)

/-- Keep source errors inside the recursive family and predicate errors outside it. -/
structure FamilyOutcome (Key : Type uKey) (Value : Type uValue) (Effect : Type uEffect)
    (SourceError : Type uSource) (RelationError : Type uError) where
  result : Except RelationError (Except SourceError (List (Key × Value)))
  state : Effect
  calls : List (Key × Except RelationError Bool)

/-- The repaired CyclicGrouped branch uses the complete record-preserving filter. -/
def filterRecursive (predicate : Predicate Key Effect RelationError)
    (family : Except SourceError (List (Key × Value))) (state : Effect) :
    FamilyOutcome Key Value Effect SourceError RelationError :=
  match family with
  | .error error => ⟨.ok (.error error), state, []⟩
  | .ok entries =>
      let filtered := run predicate entries state
      ⟨filtered.result.map Except.ok, filtered.state, filtered.calls⟩

/-- A stored source error is returned unchanged without any predicate calls. -/
theorem source_error (predicate : Predicate Key Effect RelationError) (error : SourceError) (state : Effect) :
    filterRecursive (Value := Value) predicate (.error error) state = ⟨.ok (.error error), state, []⟩ := rfl

/-- Predicate failure stays an outer error, instead of becoming a failed generator. -/
theorem relation_error (predicate : Predicate Key Effect RelationError) (entries : List (Key × Value))
    (state : Effect) (error : RelationError) :
    (filterRecursive (SourceError := SourceError) predicate (.ok entries) state).result = .error error ↔
      (run predicate entries state).result = .error error := by
  cases found : (run predicate entries state).result <;> simp [filterRecursive, found, Except.map]

/-- Every successful recursive result contains exactly the retained complete entries. -/
theorem recursive_success (predicate : Predicate Key Effect RelationError) (entries : List (Key × Value))
    (state : Effect) (retained : List (Key × Value)) :
    (filterRecursive (SourceError := SourceError) predicate (.ok entries) state).result = .ok (.ok retained) ↔
      (run predicate entries state).result = .ok retained := by
  cases found : (run predicate entries state).result <;> simp [filterRecursive, found, Except.map]

/-- The complete repaired recursive branch exposes exactly the accepted original records. -/
theorem recursive_keys_exact [DecidableEq Key] (predicate : Predicate Key Effect RelationError)
    (entries : List (Key × Value)) (unique : (entries.map Prod.fst).Nodup)
    (state : Effect) (retained : List (Key × Value))
    (success : (filterRecursive (SourceError := SourceError) predicate (.ok entries) state).result = .ok (.ok retained))
    (key : Key) (value : Value) :
    lookup key retained = some value ↔ lookup key entries = some value ∧
      (key, .ok true) ∈ (filterRecursive (SourceError := SourceError) predicate (.ok entries) state).calls := by
  exact lookup_retained predicate entries unique state retained
    ((recursive_success predicate entries state retained).mp success) key value

/-- Removing every key retains a successful empty recursive family. -/
theorem empty_retained (predicate : Predicate Key Effect RelationError) (entries : List (Key × Value))
    (state : Effect) (empty : (run predicate entries state).result = .ok []) :
    (filterRecursive (SourceError := SourceError) predicate (.ok entries) state).result = .ok (.ok []) :=
  (recursive_success predicate entries state []).mpr empty

/-- Tie the original keyed records once and retain all other recursive fields as opaque metadata. -/
def keyedEntries (keys : List Key) (program : Key → KeyedSource.Recipe Key Value Value)
    (metadata : Key → Metadata) : List (Key × (GroupedRecord.Classes Value × Metadata)) :=
  keys.map fun key => (key, (fun size => KeyedSource.family program size key), metadata key)

/-- Retention preserves the original tied class function and every other stored field. -/
theorem keyed_record_retained (predicate : Predicate Key Effect Error) (keys : List Key)
    (program : Key → KeyedSource.Recipe Key Value Value) (metadata : Key → Metadata) (state : Effect)
    (retained : List (Key × (GroupedRecord.Classes Value × Metadata)))
    (success : (run predicate (keyedEntries keys program metadata) state).result = .ok retained)
    (key : Key) (classes : GroupedRecord.Classes Value) (stored : Metadata) (member : (key, classes, stored) ∈ retained) :
    key ∈ keys ∧ classes = (fun size => KeyedSource.family program size key) ∧ stored = metadata key := by
  have original := (retained_sublist predicate _ state retained success).subset member
  obtain ⟨originalKey, present, same⟩ := List.mem_map.mp original
  have keyEq := congrArg Prod.fst same
  simp only at keyEq
  subst originalKey
  have fields := congrArg Prod.snd same
  exact ⟨present, (congrArg Prod.fst fields).symm, (congrArg Prod.snd fields).symm⟩

/-- Retained groups keep exact class counts, replay, conditional samplers, masses, and metadata. -/
theorem keyed_fields (predicate : Predicate Key Effect Error) (keys : List Key)
    (program : Key → KeyedSource.Recipe Key Value Value) (metadata : Key → Metadata) (state : Effect)
    (retained : List (Key × (GroupedRecord.Classes Value × Metadata)))
    (success : (run predicate (keyedEntries keys program metadata) state).result = .ok retained)
    (key : Key) (classes : GroupedRecord.Classes Value) (stored : Metadata) (member : (key, classes, stored) ∈ retained)
    (size rank : Nat) :
    GroupedRecord.Valid (classes size) ∧
      Decoder.count (classes size).members.plan = (KeyedSource.languageClass program size key).length ∧
      Decoder.decode (classes size).members.plan rank = (KeyedSource.languageClass program size key)[rank]? ∧
      (classes size).mass = (KeyedSource.family program size key).mass ∧
      (classes size).members.sampling = (KeyedSource.family program size key).members.sampling ∧
      stored = metadata key := by
  obtain ⟨_, same, storedEq⟩ := keyed_record_retained predicate keys program metadata state retained success key classes stored member
  subst classes
  refine ⟨KeyedSource.family_valid program size key, KeyedSource.family_count program size key, ?_, rfl, rfl, storedEq⟩
  rw [Decoder.decode_correct, KeyedSource.family_values]

/-- Every metadata projection, including minimum, support and weight flags, is unchanged. -/
theorem keyed_metadata (predicate : Predicate Key Effect Error) (keys : List Key)
    (program : Key → KeyedSource.Recipe Key Value Value) (metadata : Key → Metadata) (state : Effect)
    (retained : List (Key × (GroupedRecord.Classes Value × Metadata)))
    (success : (run predicate (keyedEntries keys program metadata) state).result = .ok retained)
    (key : Key) (classes : GroupedRecord.Classes Value) (stored : Metadata) (member : (key, classes, stored) ∈ retained)
    (observe : Metadata → Field) : observe stored = observe (metadata key) :=
  congrArg observe (keyed_record_retained predicate keys program metadata state retained success key classes stored member).2.2

/-- Filtering keys does not retie the recursive program or remove internal cross-key derivations. -/
theorem keyed_language (predicate : Predicate Key Effect Error) (keys : List Key)
    (complete : ∀ key, key ∈ keys) (program : Key → KeyedSource.Recipe Key Value Value)
    (guarded : ∀ key, KeyedSource.guarded (program key) (KeyedSource.minima keys complete program) = true)
    (metadata : Key → Metadata) (state : Effect) (retained : List (Key × (GroupedRecord.Classes Value × Metadata)))
    (success : (run predicate (keyedEntries keys program metadata) state).result = .ok retained)
    (key : Key) (classes : GroupedRecord.Classes Value) (stored : Metadata) (member : (key, classes, stored) ∈ retained)
    (size : Nat) (value : Value) :
    value ∈ Decoder.values (classes size).members.plan ↔ KeyedSource.Derives program (program key) value size := by
  obtain ⟨_, same, _⟩ := keyed_record_retained predicate keys program metadata state retained success key classes stored member
  subst classes
  exact KeyedSource.family_exact keys complete program guarded size key value

end MicroCFTA.RecursiveGroupFilter
