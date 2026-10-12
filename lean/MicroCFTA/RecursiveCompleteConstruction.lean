import MicroCFTA.RecursivePlainApplication
import MicroCFTA.RecursiveConstructionQueries

/-!
# Construction markers in complete recursive records

The existing complete body inventory determines every construction marker.
This connects the repaired query gate to the support, sampling, inspection,
and inverse compiler without adding a separate body schema assumption.
-/
namespace MicroCFTA.RecursiveCompleteConstruction
open RecursiveRuntimeOrigins

/-- Completed finite inputs have no construction token; occurrences read their current context. -/
def inputTokens (roots : Key → List Nat) : Input Key → List Nat
  | .inl _ => []
  | .inr key => roots key

/-- Execute the source union of the primitive construction sets in one complete body. -/
def construction (body : RecursiveCompleteRecord.Body Key Root Symbol Value) (roots : Key → List Nat) : List Nat :=
  (body.runtime.template.inputs.flatMap (inputTokens roots)).eraseDups

/-- Marker provenance follows the same primitive occurrences as every other record field. -/
theorem construction_exact (body : RecursiveCompleteRecord.Body Key Root Symbol Value) (roots : Key → List Nat) (token : Nat) :
    token ∈ construction body roots ↔
      ∃ key, Sum.inr key ∈ body.runtime.template.inputs ∧ token ∈ roots key := by
  simp only [construction, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨input, present, found⟩
    cases input with
    | inl fields => simp [inputTokens] at found
    | inr key => exact ⟨key, present, found⟩
  · rintro ⟨key, present, found⟩
    exact ⟨.inr key, present, found⟩

/-- An occurrence retains all enclosing construction markers carried by its key. -/
theorem occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (inspections : RecursiveJoinInspectionBody.LeafInspections Symbol) (key : Key) (roots : Key → List Nat) :
    construction (RecursiveCompleteRecord.occurrence (Root := Root) callbacks inspections key) roots = (roots key).eraseDups := by
  simp [construction, RecursiveCompleteRecord.occurrence, RecursiveRuntimeVerified.occurrence,
    RecursiveRuntimeOrigins.occurrence, inputTokens]

/-- Value maps preserve the construction field exactly. -/
theorem map (transform : Value → Result) (body : RecursiveCompleteRecord.Body Key Root Symbol Value) (roots : Key → List Nat) :
    construction (RecursiveCompleteRecord.map transform body) roots = construction body roots := rfl

/-- Size changes retain construction provenance independently of size occurrence flags. -/
theorem pay [DecidableEq Symbol] (body : RecursiveCompleteRecord.Body Key Root Symbol Value) (roots : Key → List Nat) :
    construction (RecursiveCompleteRecord.pay body) roots = construction body roots := rfl

/-- Closing a constructor layer retains active occurrences. -/
theorem label [DecidableEq Symbol] (symbol : Symbol) (body : RecursiveCompleteRecord.Body Key Root Symbol Value)
    (roots : Key → List Nat) : construction (RecursiveCompleteRecord.label symbol body) roots = construction body roots := rfl

/-- Diagnostic names do not affect construction lifetime. -/
theorem named (name : Option String) (body : RecursiveCompleteRecord.Body Key Root Symbol Value) (roots : Key → List Nat) :
    construction (RecursiveCompleteRecord.named name body) roots = construction body roots := rfl

/-- A flat choice combines exactly the markers of its actual complete alternatives. -/
theorem nary (count : Nat) (branches : Fin count → RecursiveCompleteRecord.Body Key Root Symbol Value)
    (roots : Key → List Nat) (token : Nat) :
    token ∈ construction (RecursiveCompleteRecord.nary count branches) roots ↔ ∃ index, token ∈ construction (branches index) roots := by
  simp [construction, RecursiveCompleteRecord.nary, RecursiveRuntimeVerified.nary, RecursiveRuntimeOrigins.nary,
    List.flatMap_assoc, List.mem_flatMap]

/-- Ordinary application unions both plain record inputs without mass promotion. -/
theorem ap [DecidableEq Symbol] (functions : RecursivePlainApplication.Body Key Root Symbol (A → B))
    (arguments : RecursivePlainApplication.Body Key Root Symbol A) (roots : Key → List Nat) (token : Nat) :
    token ∈ construction (RecursivePlainApplication.ap functions arguments).complete roots ↔
      token ∈ construction functions.complete roots ∨ token ∈ construction arguments.complete roots := by
  simp [construction, RecursivePlainApplication.ap, RecursivePlainApplication.runtime,
    RecursivePlainApplication.template, List.flatMap_append]

/-- Heterogeneous joins keep the operation and every ordered argument's primitive markers. -/
theorem join (component : Nat) (operation : RecursiveCompleteRecord.Body Key Root Symbol Operand)
    (arguments : RecursiveCompleteRecord.Chain Key Root Symbol Operand Result) (roots : Key → List Nat) (token : Nat) :
    token ∈ construction (RecursiveCompleteRecord.join component operation arguments) roots ↔
      token ∈ construction operation roots ∨
        token ∈ (arguments.runtime.lower.inputs.flatMap (inputTokens roots)) := by
  simp [construction, RecursiveCompleteRecord.join, RecursiveRuntimeVerified.join, RecursiveRuntimeOrigins.join,
    List.flatMap_append]

/-- The source family combines every probed body, then closes its own construction token. -/
def familyRecord (token : Nat) (keys : List Key) (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root)
    (roots : Key → List Nat) (payload : Payload) : RecursiveConstructionQueries.Record Payload :=
  RecursiveConstructionQueries.family token payload (keys.map fun key => construction (program key) roots)

/-- A completed family retains exactly the external markers reached by its complete bodies. -/
theorem family_exact (token external : Nat) (keys : List Key) (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root)
    (roots : Key → List Nat) (payload : Payload) :
    external ∈ (familyRecord token keys program roots payload).construction ↔
      external ≠ token ∧ ∃ bodyKey ∈ keys, ∃ occurrenceKey,
        Sum.inr occurrenceKey ∈ (program bodyKey).runtime.template.inputs ∧ external ∈ roots occurrenceKey := by
  rw [familyRecord, RecursiveConstructionQueries.family_outer]
  constructor
  · rintro ⟨different, body, present, found⟩
    rcases List.mem_map.mp present with ⟨key, member, rfl⟩
    exact ⟨different, key, member, (construction_exact (program key) roots external).mp found⟩
  · rintro ⟨different, key, present, found⟩
    exact ⟨different, construction (program key) roots, List.mem_map.mpr ⟨key, present, rfl⟩,
      (construction_exact (program key) roots external).mpr found⟩

/-- A top-level family has no active marker after all body occurrences close. -/
theorem family_closed (token : Nat) (keys : List Key) (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root)
    (payload : Payload) : (familyRecord token keys program (fun _ => [token]) payload).construction = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro external present
  rcases (family_exact token external keys program _ payload).mp present with ⟨different, bodyKey, _, occurrenceKey, _, found⟩
  simp only [List.mem_singleton] at found
  exact different found

/-- The repaired query gate returns every completed field of the same checked program unchanged. -/
theorem completed_query (token : Nat) (keys : List Key) (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root)
    (payload : Payload) (read : Payload → Result) :
    RecursiveConstructionQueries.query (Cause := Cause) read (.ok (familyRecord token keys program (fun _ => [token]) payload)) =
      .ok (read payload) := by
  simp only [RecursiveConstructionQueries.query, family_closed]
  rfl

/-- An inner family remains unqueryable while it reaches a distinct enclosing occurrence. -/
theorem enclosing_query (token external : Nat) (different : external ≠ token) (keys : List Key)
    (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root) (roots : Key → List Nat)
    (bodyKey : Key) (bodyPresent : bodyKey ∈ keys) (occurrenceKey : Key)
    (used : Sum.inr occurrenceKey ∈ (program bodyKey).runtime.template.inputs)
    (active : external ∈ roots occurrenceKey) (payload : Payload) (read : Payload → Result) :
    RecursiveConstructionQueries.query (Cause := Cause) read (.ok (familyRecord token keys program roots payload)) = .error .queriedOccurrence :=
  RecursiveConstructionQueries.active_query external _ ((family_exact token external keys program roots payload).mpr
    ⟨different, bodyKey, bodyPresent, occurrenceKey, used, active⟩) read

/-- The public support query checks construction before it reads the assembled family graph. -/
def supportQuery (token : Nat) (code : Key → Nat) (keys : List Key)
    (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root) (key : Key) :
    Except (RecursiveConstructionQueries.Error Unit) (SupportGraph.Support Symbol) :=
  RecursiveConstructionQueries.query id (.ok (familyRecord token keys program (fun _ => [token])
    (RecursiveJoinSupportFamily.memberGraph token code keys (fun key => (program key).support) key)))

/-- Successful support queries retain the independent finite-term semantics of the complete record. -/
theorem support_query_exact (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (injective : Function.Injective code)
    (program : Key → RecursiveCompleteRecord.Body Key Root Symbol Root)
    (accepted : RecursiveCompleteRecord.Accepted token keys complete program)
    (environment : BinderLanguage.Env (GeneratorCombinators.Label Symbol)) (key : Key)
    (term : RecursiveCallbackTermination.EngineTerm Symbol) :
    (match supportQuery token code keys program key with
      | .ok graph => BinderLanguage.meaning environment graph term
      | .error _ => False) ↔
      ∃ size, term ∈ Decoder.values (KeyedSource.family
        (RecursiveJoinFamily.termProgram code
          (RecursiveJoinInverse.lower (RecursiveCompleteRecord.checked program))) size key).members.plan := by
  rw [supportQuery, completed_query]
  exact RecursiveCompleteRecord.support_exact token keys complete code injective program accepted environment key term

end MicroCFTA.RecursiveCompleteConstruction
