import MicroCFTA.SourceCurrentAllocatedNativeEffects
import MicroCFTA.SourceCurrentConjunctionMemo
import MicroCFTA.SourceEqualityNativeDemandRunning
import MicroCFTA.SourceEqualityNativeDemandRequestExact
import MicroCFTA.SourceCurrentAllocatedNativeRunning

/-!
# Actual checked queries enter the current conjunction memo

Completed queries derive result availability and conjunction readiness from
their actual checked states. New memo calls retain both native tables and
advance their physical heap with the returned equality-operation cache.
The native completion observation and reached input plan stay explicit.
General query completion and the whole class scan remain separate targets.
-/
namespace MicroCFTA.SourceCurrentAllocatedQueryMemo
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceEqualityNativeDemandProvenance (NodeProduced)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- A checked source key has represented operands and therefore cannot select a direct unresolved call. -/
theorem key_exists (request : NodeRequest Symbol Guard)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  obtain ⟨_, _, first, second, left, right, _, _⟩ := safe
  exact ⟨IntersectionFlatMemoKeyDomain.flatKey width request.domain first second,
    IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second left right⟩

/-- Actual completed call readback derives the returned checked receipt from the same final native cells. -/
theorem call_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (result : Value Symbol Guard) (steps : Nat)
    (call : SourceEqualityNativeDemandNodeReadback.Call request before result after steps)
    (initial : SourceEqualityNativeDemandProvenance.Valid holds before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (final : SourceEqualityNativeDemandProvenance.Valid holds after.native) :
    NodeProduced (width := width) holds after.native.machine request result := by
  cases call with
  | direct fuel after value unresolved body =>
      obtain ⟨key, actual⟩ := key_exists request safe
      rw [unresolved] at actual
      cases actual
  | ready key handle original value requested published returned =>
      exact (SourceEqualityNativeDemandProvenance.node_ready_receipt before.native initial request original
        ready key ⟨requested, safe⟩ handle published result returned).2.2.1
  | started fuel handle chosen running actual middle value selected demanded suspended evaluating machine body =>
      have same := SourceEqualityNativeDemandRequestExact.node_started holds request actual before.native chosen running
        handle initial ready safe selected demanded
      subst actual
      have chosenShape := SourceRecursiveIntersectionNative.lookupNode_shape request before.native initial.shape
      simp only [selected] at chosenShape
      have runningShape := SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
      simp only [demanded] at runningShape
      have retained := SourceEqualityNativeDemandRunning.trace_retains fuel (.code (compileNode request))
        (⟨running, before.operations⟩ : Checked width) middle result body
        (SourceRecursiveIntersectionCode.compileNode_bodyCode request) runningShape
      have present := retained.2.1 handle request evaluating
      have returned : (finishNode handle result middle.native).nodes.cells handle = some ⟨request, .returned result⟩ := by
        simp only [finishNode, FlatMemoThunk.finish, present, FlatMemoThunk.setStatus, Cache.put, ↓reduceIte]
      exact (final.nodes.checked handle _ returned).2

/-- The original reached input check is part of every finite checked input plan. -/
theorem inputs_head [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : Checked width)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    SourceEqualityNativeDemandValidity.Inputs holds control state := by
  cases fuel with
  | zero => exact inputs
  | succ => exact inputs.1

/-- An actual completed node query derives physical effects, availability, and its independent language receipt. -/
theorem query_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (fuel : Nat) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (result : Value Symbol Guard)
    (native : SourceEqualityNativeDemandProvenance.Valid holds before.native) (ready : Ready (physical before))
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel
      (.code (requestNode request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done result after) :
    Effects (physical before) (physical after) ∧ SourceEqualityNativeDemandProvenance.Valid holds after.native ∧
      Available after.native.machine.heap result ∧ NodeProduced (width := width) holds after.native.machine request result := by
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (requestNode request.domain request.left request.right)) before := fun _ => trivial
  have actual := SourceCurrentAllocatedNativeEffects.execute_effects holds fuel _ before native ready fields inputs
  have final : Effects (physical before) (physical after) ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native := by
    simpa only [done, Outcome.state] using And.intro actual.1 actual.2.1
  have head := inputs_head holds fuel _ before inputs
  obtain ⟨steps, _, call⟩ := SourceEqualityNativeDemandNodeReadback.of_done fuel request before after result done
  have produced := call_produced holds request before after result steps call native head.1 head.2 final.2
  exact ⟨final.1, final.2, produced.spec.2.1, produced⟩

/-- A conjunction result advances the same native state with its actual heap and operation cache. -/
def advancePhysical (before : Checked width) (after : Physical) : Checked width :=
  ⟨advance before.native {before.native.machine with heap := after.heap}, after.equality⟩

/-- Advancing the native state retains the complete returned physical state. -/
theorem physical_advance (before : Checked width) (after : Physical) :
    physical (advancePhysical before after) = after := by cases after; rfl

/-- Constructor-only effects retain every native memo table and the domain cache. -/
theorem advance_tables (before : Checked width) (after : Physical) :
    (advancePhysical before after).native.nodes = before.native.nodes ∧
      (advancePhysical before after).native.edges = before.native.edges ∧
      (advancePhysical before after).native.machine.domains = before.native.machine.domains :=
  ⟨rfl, rfl, rfl⟩

/-- Returned conjunction effects extend the same native machine and its original records. -/
theorem advance_extension (before : Checked width) (after : Physical)
    (effects : Effects (physical before) after) :
    Extension before.native.machine (advancePhysical before after).native.machine :=
  ⟨effects.keeps.growth, effects.keeps.history, Cache.extends_refl _⟩

/-- Actual conjunction effects retain the checked receipts of both native tables. -/
theorem advance_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (before : Checked width) (after : Physical)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds before.native)
    (effects : Effects (physical before) after) :
    SourceEqualityNativeDemandProvenance.Valid holds (advancePhysical before after).native :=
  SourceEqualityNativeDemandProvenance.advance_valid before.native valid _
    ⟨effects.ready.semantic.ready.semantic.1.normal.facts, valid.machine.2⟩
    (advance_extension before after effects)

/-- One checked query precedes one call to the new conjunction memo at the same returned heap. -/
inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (request : NodeRequest Symbol Guard) (before : Checked width) :
    Value Symbol Guard → Bool → Checked width → SourceCurrentEmptinessMemo.Memo → Prop where
  | done (fuel : Nat) (query : Value Symbol Guard) (queried : Checked width)
      (answer : Bool) (after : Physical) (saved : SourceCurrentEmptinessMemo.Memo)
      (native : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done query queried)
      (memoized : SourceCurrentConjunctionMemo.Call budget memo query (physical queried) answer after saved) :
      Call budget memo request before query answer (advancePhysical queried after) saved

/-- A completed checked query constructs the current memo call and derives its final full-state invariants. -/
theorem finite_after_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget fuel : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (request : NodeRequest Symbol Guard)
    (before queried : Checked width) (query : Value Symbol Guard)
    (native : SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native) (ready : Ready (physical before))
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough (SourceEqualityPCSGuard.holds formulas solver) fuel
      (.code (requestNode request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done query queried) :
    ∃ answer after saved, Call budget memo request before query answer after saved ∧
      Effects (physical before) (physical after) ∧
      SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      NodeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) after.native.machine request query := by
  obtain ⟨queryEffects, queryValid, available, produced⟩ :=
    query_effects (SourceEqualityPCSGuard.holds formulas solver) fuel request before queried query native ready inputs done
  have queryIdle := SourceCurrentAllocatedNativeRunning.done_idle fuel _ before queried query
    (by intro value; trivial) native.shape idle done
  have memoCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
  obtain ⟨answer, after, saved, call, effects, savedCorrect, sound, retained⟩ :=
    SourceCurrentConjunctionMemo.finite formulas solver budget memo query (physical queried)
      queryEffects.ready available memoCorrect
  refine ⟨answer, advancePhysical queried after, saved, .done fuel query queried answer after saved done call,
    ?_, advance_valid _ queried after queryValid effects,
    SourceRecursiveIntersectionNative.Idle.advance _ _ queryIdle, savedCorrect, sound, retained,
    produced.grows (advance_extension queried after effects)⟩
  simpa only [physical_advance] using queryEffects.trans effects

/-- A true memo answer after a closed empty-domain query excludes every common original input term. -/
theorem true_excludes_common [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : NodeRequest Symbol Guard) (state : Checked width) (query : Value Symbol Guard)
    (produced : NodeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) state.native.machine request query)
    (sound : SourceCurrentEmptinessMemo.AnswerSound formulas solver query true)
    (domain : request.domain = IntersectionEmptyDomain.emptyDomain)
    (left : request.left.free = []) (right : request.right.free = []) :
    ∀ ambient term, ¬(InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.left term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.right term) := by
  intro ambient term common
  exact sound.2 rfl ambient term ((produced.spec.2.2 domain left right ambient term).mpr common)

end MicroCFTA.SourceCurrentAllocatedQueryMemo
