import MicroCFTA.SourceEqualityAccessorAllocation
import MicroCFTA.SourceEqualityConstraintConstructors
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SymbolicSignedPaths

/-!
# Equality allocation in the checked source edge constructor

The contradiction test reads the stored field and Bottom guard first.
Only the live branch demands the full equality accessor for its arity test.
A rejected edge still retains those accessor effects. The edge constructor
then interns either the original fields or the source empty-edge sentinel.
The sentinel also demands the canonical empty stored equality field.
Natural paths enter the existing signed source test through exact casts.
Machine-index representation and runtime demand adequacy remain separate.
-/
namespace MicroCFTA.SourceEqualityMkEdgeAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (Grows Valid)
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Constraint" => SourceSymbolicIndex.Constraint

/-- Encode represented natural paths as nonnegative source paths. -/
def signed (classes : Option EqualityNormalize.Constraints) : Option (List (List SymbolicSignedPaths.Path)) :=
  classes.map fun records => records.map fun paths => paths.map fun path => path.map Int.ofNat

/-- Use the exact signed source arity check on represented equality classes. -/
def fits (arity : Nat) (classes : Option EqualityNormalize.Constraints) : Bool :=
  SymbolicSignedPaths.fitsArity arity (signed classes)

/-- Source contradiction reads only the stored equality tag and the outer guard. -/
def contradictory (constraint : Constraint Formula) : Bool :=
  constraint.equalities.isNone || match constraint.guard with
    | .bottom => true
    | _ => false

/-- The checked constructor preserves the source short circuit before accessor demand. -/
noncomputable def accepted (constraint : Constraint Formula) (arity : Nat) : Bool :=
  if contradictory constraint then false else fits arity (SourceCompactGuards.sourceEqualities constraint)

/-- Demand only the accessor needed by the actual source constructor guard. -/
noncomputable def check (stored : Value) (guard : SourceGuards.Guard Formula) (arity : Nat) (before : OpState) :
    Except String Bool × OpState :=
  if contradictory (SourceEqualityAccessorAllocation.constraint stored guard) then (.ok false, before)
  else
    let own := SourceEqualityAccessorAllocation.equalities stored guard before
    (own.1.map fun value => fits arity (SourceEqualityInheritedPayload.classes value.payload), own.2)

/-- A contradictory stored field or Bottom skips all positive-guard allocations. -/
theorem check_contradictory (stored : Value) (guard : SourceGuards.Guard Formula) (arity : Nat) (before : OpState)
    (rejected : contradictory (SourceEqualityAccessorAllocation.constraint stored guard) = true) :
    check stored guard arity before = (.ok false, before) := by
  simp only [check, rejected, ↓reduceIte]

/-- The checked guard derives its exact source answer and all completed-cache effects. -/
theorem check_correct (stored : Value) (guard : SourceGuards.Guard Formula) (arity : Nat) (before : OpState)
    (valid : Valid before) (ready : Ready before.constraints stored) :
    (check stored guard arity before).1 = .ok (accepted (SourceEqualityAccessorAllocation.constraint stored guard) arity) ∧
      Valid (check stored guard arity before).2 ∧ Grows before (check stored guard arity before).2 := by
  by_cases rejected : contradictory (SourceEqualityAccessorAllocation.constraint stored guard) = true
  · simp only [check, accepted, rejected, ↓reduceIte]
    exact ⟨trivial, valid, SourceEqualityConstraintMemoAllocation.grows_refl before⟩
  · obtain ⟨own, done, afterValid, _, classes, growth⟩ :=
      SourceEqualityAccessorAllocation.equalities_correct stored guard before valid ready
    simp only [check, accepted, rejected, done, Except.map, classes]
    exact ⟨rfl, afterValid, growth⟩

/-- Choose the source sentinel or the original complete edge fields after the checks. -/
def work (symbol : Symbol) (constraint : Constraint Formula)
    (children : List (InternedConstructorTemplates.Value Symbol (Constraint Formula))) (keep : Bool) :
    InternedConstructorTemplates.Work Symbol (Constraint Formula) (InternedConstructorTemplates.EdgeValue Symbol (Constraint Formula)) :=
  if keep then InternedConstructorTemplates.makeEdge symbol constraint children
  else InternedConstructorTemplates.makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]

/-- The direct source sentinel demands noConstraint and its canonical empty equality field. -/
def emptyField (before : OpState) : OpState :=
  {before with constraints := (intern (some []) before.constraints).2}

/-- Sentinel equality construction preserves both completed operation tables. -/
theorem emptyField_correct (before : OpState) (valid : Valid before) :
    Valid (emptyField before) ∧ Grows before (emptyField before) ∧
      Ready (emptyField before).constraints (intern (some []) before.constraints).1 := by
  have steps := intern_steps (some []) before.constraints
  refine ⟨valid.steps _ steps, ⟨steps, Cache.extends_refl _, Cache.extends_refl _⟩,
    intern_ready (some []) before.constraints valid.constraints ?_⟩
  intro records same
  cases same
  simp

/-- Only the rejected branch demands the sentinel's stored equality field. -/
def outputState (before : OpState) (keep : Bool) : OpState :=
  if keep then before else emptyField before

/-- Both selected branches retain actual valid growing operation state. -/
theorem outputState_correct (before : OpState) (keep : Bool) (valid : Valid before) :
    Valid (outputState before keep) ∧ Grows before (outputState before keep) := by
  cases keep with
  | false => exact (emptyField_correct before valid).imp_right And.left
  | true => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl before⟩

/-- Retain equality effects and then execute the actual selected edge interner request. -/
noncomputable def build [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol (Constraint Formula))]
    (symbol : Symbol) (stored : Value) (guard : SourceGuards.Guard Formula)
    (children : List (InternedConstructorTemplates.Value Symbol (Constraint Formula))) (before : OpState)
    (heap : InternedConstructorTemplates.State Symbol (Constraint Formula)) :
    Except String (InternedConstructorTemplates.EdgeValue Symbol (Constraint Formula)) × OpState ×
      InternedConstructorTemplates.State Symbol (Constraint Formula) :=
  let checked := check stored guard children.length before
  match checked.1 with
  | .error message => (.error message, checked.2, heap)
  | .ok keep =>
      let built := InternedConstructorTemplates.run
        (work symbol (SourceEqualityAccessorAllocation.constraint stored guard) children keep) heap
      (.ok built.1, outputState checked.2 keep, built.2)

/-- Exact source checks select a concrete constructor receipt without an assumed cached answer. -/
theorem build_receipt [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol (Constraint Formula))]
    (symbol : Symbol) (stored : Value) (guard : SourceGuards.Guard Formula)
    (children : List (InternedConstructorTemplates.Value Symbol (Constraint Formula))) (before : OpState)
    (heap : InternedConstructorTemplates.State Symbol (Constraint Formula))
    (valid : Valid before) (ready : Ready before.constraints stored) :
    let constraint := SourceEqualityAccessorAllocation.constraint stored guard
    let built := InternedConstructorTemplates.run (work symbol constraint children (accepted constraint children.length)) heap
    build symbol stored guard children before heap =
      (.ok built.1, outputState (check stored guard children.length before).2 (accepted constraint children.length), built.2) ∧
      Valid (build symbol stored guard children before heap).2.1 ∧
      Grows before (build symbol stored guard children before heap).2.1 := by
  obtain ⟨done, afterValid, growth⟩ := check_correct stored guard children.length before valid ready
  have after := outputState_correct _ (accepted (SourceEqualityAccessorAllocation.constraint stored guard) children.length) afterValid
  simp only [build, done]
  exact ⟨trivial, after.1, ⟨steps_trans growth.constraints after.2.constraints,
    Cache.extends_trans growth.combinations after.2.combinations,
    Cache.extends_trans growth.descents after.2.descents⟩⟩

/-- Either selected source edge request preserves the complete constructor heap. -/
theorem work_keeps [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol (Constraint Formula))]
    (symbol : Symbol) (constraint : Constraint Formula)
    (children : List (InternedConstructorTemplates.Value Symbol (Constraint Formula))) (keep : Bool)
    (heap : InternedConstructorTemplates.State Symbol (Constraint Formula))
    (ready : SourceEqualityRequiredCache.Ready heap) (available : InternedNestedProvenance.Values heap children) :
    SourceEqualityRequiredCache.Keeps heap (InternedConstructorTemplates.run (work symbol constraint children keep) heap).2 := by
  cases keep with
  | true => exact (SourceEqualityRequiredCache.edge symbol constraint children heap ready available).1
  | false =>
      apply (SourceEqualityRequiredCache.edge symbol SourceEqualityConstraintConstructors.top [.empty] heap ready ?_).1
      intro child member
      simp only [List.mem_singleton] at member
      subst child
      exact InternedProbeProvenance.empty_available heap

end MicroCFTA.SourceEqualityMkEdgeAllocation
