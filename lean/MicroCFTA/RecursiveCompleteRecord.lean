import MicroCFTA.RecursiveRuntimeVerified
import MicroCFTA.RecursiveJoinSupportFamily
import MicroCFTA.RecursiveJoinInspectionBody
import MicroCFTA.BoundedRecursiveDispatch

/-!
# Complete records for typed recursive join bodies

Each constructor builds its runtime, support, diagnostic, and occurrence
fields together. Their checked-body equalities are local wiring facts.
Family theorems therefore refer to one value, term, mass, and inverse
compiler throughout the record.
-/
namespace MicroCFTA.RecursiveCompleteRecord

/-- All record views describe the same complete checked body. -/
structure Body (Key Root Symbol Value : Type) where
  runtime : RecursiveRuntimeVerified.Body Key Root Symbol Value
  support : RecursiveJoinSupportBody.Body Key Root Symbol Value
  inspection : RecursiveJoinInspectionBody.Body Key Root Symbol Value
  guards : RecursiveJoinGuards.Body Key Root Symbol Value
  support_same : support.checked = runtime.template.checked
  inspection_same : inspection.checked = runtime.template.checked
  guards_same : guards.checked = runtime.template.checked

/-- A finite input supplies only its local support, diagnostic, inverse, and probability contracts. -/
def finite [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (description : FiniteSource.Source (Value × RecursiveCallbackTermination.EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite (Key := Key) (Root := Root) description))
    (weighted : Bool) (ordinary : weighted = false → ∀ size, RecursiveUniformRuntime.Uniform (FiniteSource.atSize description size))
    (view : RecursiveJoinSupportView.View Symbol)
    (supports : ∀ environment term, BinderLanguage.meaning environment view.graph term ↔
      ∃ size, term ∈ FiniteSource.classMembers (.map Prod.snd description) size)
    (inspections : RecursiveJoinInspectionBody.LeafInspections Symbol)
    (valid : RecursiveJoinInspection.Valid (inspections description).layer) : Body Key Root Symbol Value where
  runtime := RecursiveRuntimeVerified.finite callbacks description inverse weighted ordinary
  support := RecursiveJoinSupportBody.finite callbacks description inverse view supports
  inspection := RecursiveJoinInspectionBody.ofNary callbacks inspections (.finite description) inverse valid
  guards := RecursiveJoinGuards.ofNary callbacks (.finite description) inverse
  support_same := rfl
  inspection_same := rfl
  guards_same := rfl

/-- Retained key masses use the weighted route and leave support and inspection members unchanged. -/
def retained [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (mass : Nat → Rat) (positive : ∀ size, 0 < mass size)
    (description : FiniteSource.Source (Value × RecursiveCallbackTermination.EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite (Key := Key) (Root := Root) description))
    (weighted : Bool) (view : RecursiveJoinSupportView.View Symbol)
    (supports : ∀ environment term, BinderLanguage.meaning environment view.graph term ↔
      ∃ size, term ∈ FiniteSource.classMembers (.map Prod.snd description) size)
    (inspections : RecursiveJoinInspectionBody.LeafInspections Symbol)
    (valid : RecursiveJoinInspection.Valid (inspections description).layer) : Body Key Root Symbol Value where
  runtime := RecursiveRuntimeVerified.retained callbacks mass positive description inverse weighted
  support := RecursiveJoinSupportBody.retained callbacks mass positive description inverse view supports
  inspection := RecursiveJoinInspectionBody.ofNary callbacks inspections (.retained mass positive description) inverse valid
  guards := RecursiveJoinGuards.ofNary callbacks (.retained mass positive description) inverse
  support_same := rfl
  inspection_same := rfl
  guards_same := rfl

/-- A recursive occurrence reads each independent family context at the same key. -/
def occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (inspections : RecursiveJoinInspectionBody.LeafInspections Symbol) (key : Key) : Body Key Root Symbol Root where
  runtime := RecursiveRuntimeVerified.occurrence callbacks key
  support := RecursiveJoinSupportBody.occurrence callbacks key
  inspection := RecursiveJoinInspectionBody.ofNary callbacks inspections (.occurrence key) True.intro True.intro
  guards := RecursiveJoinGuards.ofNary callbacks (.occurrence key) True.intro
  support_same := rfl
  inspection_same := rfl
  guards_same := rfl

/-- User maps change the common value compiler and preserve all matching field views. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result where
  runtime := RecursiveRuntimeVerified.map transform inner.runtime
  support := RecursiveJoinSupportBody.map transform inner.support
  inspection := RecursiveJoinInspectionBody.map transform inner.inspection
  guards := RecursiveJoinGuards.map transform inner.guards
  support_same := congrArg (RecursiveJoinBodyFields.map transform) inner.support_same
  inspection_same := congrArg (RecursiveJoinBodyFields.map transform) inner.inspection_same
  guards_same := congrArg (RecursiveJoinBodyFields.map transform) inner.guards_same

/-- Pay advances every size-indexed view through the same checked operation. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  runtime := RecursiveRuntimeVerified.pay inner.runtime
  support := RecursiveJoinSupportBody.pay inner.support
  inspection := RecursiveJoinInspectionBody.pay inner.inspection
  guards := RecursiveJoinGuards.pay inner.guards
  support_same := congrArg RecursiveJoinBodyFields.pay inner.support_same
  inspection_same := congrArg RecursiveJoinBodyFields.pay inner.inspection_same
  guards_same := congrArg RecursiveJoinBodyFields.pay inner.guards_same

/-- Labels close support and diagnostic roots while retaining the same checked term compiler. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  runtime := RecursiveRuntimeVerified.label symbol inner.runtime
  support := RecursiveJoinSupportBody.label symbol inner.support
  inspection := RecursiveJoinInspectionBody.label symbol inner.inspection
  guards := RecursiveJoinGuards.label symbol inner.guards
  support_same := congrArg (RecursiveJoinBodyFields.label symbol) inner.support_same
  inspection_same := congrArg (RecursiveJoinBodyFields.label symbol) inner.inspection_same
  guards_same := congrArg (RecursiveJoinBodyFields.label symbol) inner.guards_same

/-- Every flat alternative retains the same position in all record fields. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value where
  runtime := RecursiveRuntimeVerified.nary count (fun index => (branches index).runtime)
  support := RecursiveJoinSupportBody.nary count (fun index => (branches index).support)
  inspection := RecursiveJoinInspectionBody.nary count (fun index => (branches index).inspection)
  guards := RecursiveJoinGuards.nary count (fun index => (branches index).guards)
  support_same := congrArg (RecursiveJoinBodyFields.nary count) (funext fun index => (branches index).support_same)
  inspection_same := congrArg (RecursiveJoinBodyFields.nary count) (funext fun index => (branches index).inspection_same)
  guards_same := congrArg (RecursiveJoinBodyFields.nary count) (funext fun index => (branches index).guards_same)

/-- Naming changes only the independent diagnostic view. -/
def named (name : Option String) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  {inner with inspection := RecursiveJoinInspectionBody.named name inner.inspection}

/-- The same typed chain supplies every heterogeneous argument field. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Read the runtime argument records in signature order. -/
def Chain.runtime : Chain Key Root Symbol Operand Result → RecursiveRuntimeVerified.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.runtime rest.runtime

/-- Read supports from the same arguments. -/
def Chain.support : Chain Key Root Symbol Operand Result → RecursiveJoinSupportBody.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.support rest.support

/-- Read diagnostic names and graphs from the same arguments. -/
def Chain.inspection : Chain Key Root Symbol Operand Result → RecursiveJoinInspectionBody.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.inspection rest.inspection

/-- Read original occurrence metadata from the same arguments. -/
def Chain.guards : Chain Key Root Symbol Operand Result → RecursiveJoinGuards.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.guards rest.guards

/-- Support lowering preserves the complete runtime argument compiler. -/
theorem Chain.support_same (arguments : Chain Key Root Symbol Operand Result) :
    arguments.support.lower = arguments.runtime.lower.lower := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [support, RecursiveJoinSupportBody.Chain.lower, runtime,
        RecursiveRuntimeVerified.Chain.lower, RecursiveRuntimeOrigins.Chain.lower, argument.support_same, ih]

/-- Diagnostic lowering preserves that same argument compiler. -/
theorem Chain.inspection_same (arguments : Chain Key Root Symbol Operand Result) :
    arguments.inspection.lower = arguments.runtime.lower.lower := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [inspection, RecursiveJoinInspectionBody.Chain.lower, runtime,
        RecursiveRuntimeVerified.Chain.lower, RecursiveRuntimeOrigins.Chain.lower, argument.inspection_same, ih]

/-- Occurrence checks inspect the arguments used by the actual runtime compiler. -/
theorem Chain.guards_same (arguments : Chain Key Root Symbol Operand Result) :
    arguments.guards.lower = arguments.runtime.lower.lower := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [guards, RecursiveJoinGuards.Chain.lower, runtime,
        RecursiveRuntimeVerified.Chain.lower, RecursiveRuntimeOrigins.Chain.lower, argument.guards_same, ih]

/-- A heterogeneous join constructs every field from the same operation and argument records. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Body Key Root Symbol Result where
  runtime := RecursiveRuntimeVerified.join component operation.runtime arguments.runtime
  support := RecursiveJoinSupportBody.join component operation.support arguments.support
  inspection := RecursiveJoinInspectionBody.join component operation.inspection arguments.inspection
  guards := RecursiveJoinGuards.join component operation.guards arguments.guards
  support_same := by
    change RecursiveJoinBodyFields.join component operation.support.checked arguments.support.lower = _
    rw [operation.support_same, arguments.support_same]
    rfl
  inspection_same := by
    change RecursiveJoinBodyFields.join component operation.inspection.checked arguments.inspection.lower = _
    rw [operation.inspection_same, arguments.inspection_same]
    rfl
  guards_same := by
    change RecursiveJoinBodyFields.join component operation.guards.checked arguments.guards.lower = _
    rw [operation.guards_same, arguments.guards_same]
    rfl

/-- One common checked program supplies values, terms, masses, decoders, and inverse callbacks. -/
def checked (program : Key → Body Key Root Symbol Root) : Key → RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root :=
  fun key => (program key).runtime.template.checked

/-- The support family's value and term recipes are the runtime family's recipes. -/
theorem support_program (program : Key → Body Key Root Symbol Root) :
    RecursiveJoinSupportFamily.lower (fun key => (program key).support) = RecursiveJoinInverse.lower (checked program) := by
  funext key
  exact congrArg (·.body) (program key).support_same

/-- The original public guard is checked against the runtime family's actual value recipe. -/
theorem guards_program (program : Key → Body Key Root Symbol Root) :
    RecursiveJoinGuards.lower (fun key => (program key).guards) = RecursiveJoinInverse.lower (checked program) := by
  funext key
  exact congrArg (·.body) (program key).guards_same

/-- The public occurrence check uses the minimum table of the common value compiler. -/
def Accepted (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) : Prop :=
  ∀ key, OccurrenceGuard.isUnguarded token ((program key).guards.shape token
    (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (RecursiveJoinInverse.lower (checked program))))) = false

/-- The original record guard supplies the required common family size guard. -/
theorem accepted_guarded (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (accepted : Accepted token keys complete program) :
    RecursiveJoinInverse.Guarded keys complete (checked program) := by
  have original := RecursiveJoinGuards.public_value_guards token keys complete
    (fun key => (program key).guards) (by simpa only [guards_program, Accepted] using accepted)
  simpa only [guards_program, RecursiveJoinInverse.Guarded] using original

/-- The full support field accepts exactly the independent term classes of the common runtime body. -/
theorem support_exact (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (injective : Function.Injective code)
    (program : Key → Body Key Root Symbol Root) (accepted : Accepted token keys complete program)
    (environment : BinderLanguage.Env (GeneratorCombinators.Label Symbol)) (key : Key)
    (term : RecursiveCallbackTermination.EngineTerm Symbol) :
    BinderLanguage.meaning environment
      (RecursiveJoinSupportFamily.memberGraph token code keys (fun key => (program key).support) key) term ↔
      ∃ size, term ∈ Decoder.values (KeyedSource.family
        (RecursiveJoinFamily.termProgram code (RecursiveJoinInverse.lower (checked program))) size key).members.plan := by
  have guarded := accepted_guarded token keys complete program accepted
  have exact := RecursiveJoinSupportFamily.family_exact token code injective keys complete
    (fun key => (program key).support) (by simpa only [support_program, RecursiveJoinInverse.Guarded] using guarded) environment key term
  simpa only [RecursiveJoinSupportFamily.termProgram, support_program] using exact

/-- The complete inverse field returns exactly the bounded term preimages of the same record. -/
theorem ranks_exact [DecidableEq (RecursiveCallbackTermination.EngineTerm Symbol)]
    (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → Body Key Root Symbol Root) (accepted : Accepted token keys complete program)
    (key : Key) (bound : Nat) (view : IntegerTermViews.View)
    (wanted : List (RecursiveCallbackTermination.EngineTerm Symbol)) (rank : Nat) :
    rank ∈ RecursiveJoinQuery.boundedQuery code (checked program) key bound view wanted ↔
      ∃ term, RecursiveJoinQuery.boundedDecode code (checked program) key bound rank = some term ∧
        IntegerTermViews.project view term = wanted :=
  RecursiveJoinQuery.bounded_query_exact code (checked program) key keys complete
    (accepted_guarded token keys complete program accepted) bound view wanted rank

/-- Every diagnostic family body has the descriptor required by source closing. -/
theorem inspection_valid (token : Nat) (code : Key → Nat) (names : Key → Option String)
    (program : Key → Body Key Root Symbol Root) (key : Key) :
    RecursiveJoinInspection.Valid ((program key).inspection.inspect
      (fun key => RecursiveJoinInspection.occurrence token (code key) (names key))).layer :=
  RecursiveJoinInspectionBody.family_body_valid token code names (fun key => (program key).inspection) key

/-- Naming cannot change any checked generation field. -/
theorem named_checked (names : Key → Option String) (program : Key → Body Key Root Symbol Root) :
    checked (fun key => named (names key) (program key)) = checked program := rfl

/-- Both source sampler branches belong to the common checked program. -/
theorem sampling_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (key : Key) (bound : Nat) :
    (RecursiveJoinRuntime.boundedSampler
      (RecursiveRuntimeOrigins.memberMetadata keys
        (RecursiveRuntimeVerified.templates (fun key => (program key).runtime)) key).weighted
      (fun size => KeyedSource.family (fun key => (checked program key).body.value) size key) bound).sampling.ranked =
      (GroupedRecord.bounded
        (fun size => KeyedSource.family (fun key => (checked program key).body.value) size key) bound).sampling.ranked :=
  RecursiveRuntimeVerified.dispatched_family_exact keys complete (fun key => (program key).runtime) key bound

end MicroCFTA.RecursiveCompleteRecord
