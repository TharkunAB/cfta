import MicroCFTA.SourcePruningEnumerationPrefixLanguage
import MicroCFTA.SourceEqualityProjectionRead

/-!
# Accepted assignments through the actual selected prefix

Original annotation and symbol policies retain an accepted exposed edge.
The independent row-language law includes Mu and Union values.
The actual prefix retains that assignment in its parked or narrowed cache.
-/
namespace MicroCFTA.SourcePruningNativeView
open Language InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- The three actual policy tests retain an edge that accepts the chosen term. -/
theorem keeps_of_accepted
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (term : Term Symbol)
    (unary : ∀ symbol annotation child, term = .node symbol [child] →
      InternedGuardedLanguage.meaning holds ambient annotation child →
      admits key annotation = true ∧ fits key symbol = true)
    (application : ∀ annotation first second third fourth,
      term = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
      InternedGuardedLanguage.meaning holds ambient annotation first → admits key annotation = true)
    (filtered : ∀ annotation first second,
      term = .node ("filter", FullSyntax.Formula.top) [first, second] →
      InternedGuardedLanguage.meaning holds ambient annotation first → admits key annotation = true)
    (edge : EdgeValue Symbol Guard)
    (accepted : InternedGuardedLanguage.edgeMeaning holds ambient edge term) :
    keeps fits admits key edge = true := by
  obtain ⟨terms, shape, runs, _guard⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all holds ambient edge term).mp accepted
  obtain ⟨entry, children⟩ := edge
  change term = .node entry.key.symbol terms at shape
  change All₂ (InternedGuardedLanguage.meaning holds ambient) children terms at runs
  cases children with
  | nil => rfl
  | cons annotation rest =>
      cases runs with
      | cons childAccepted later =>
          cases rest with
          | nil =>
              cases later
              obtain ⟨admitted, fitted⟩ := unary entry.key.symbol annotation _ shape childAccepted
              simp only [keeps, EdgeValue.children, EdgeValue.entry, admitted, fitted, Bool.and_self]
          | cons second rest =>
              cases later with
              | cons _ later =>
                  cases rest with
                  | nil =>
                      cases later
                      by_cases label : entry.key.symbol = ("filter", FullSyntax.Formula.top)
                      · have admitted := filtered annotation _ _ (by simpa only [label] using shape) childAccepted
                        simp only [keeps, EdgeValue.children, EdgeValue.entry, label, ↓reduceIte, admitted]
                      · simp only [keeps, EdgeValue.children, EdgeValue.entry, label, ↓reduceIte]
                  | cons third rest =>
                      cases later with
                      | cons _ later =>
                          cases rest with
                          | nil => rfl
                          | cons fourth rest =>
                              cases later with
                              | cons _ later =>
                                  cases rest with
                                  | nil =>
                                      cases later
                                      by_cases label : entry.key.symbol = ("app", FullSyntax.Formula.top)
                                      · have admitted := application annotation _ _ _ _
                                          (by simpa only [label] using shape) childAccepted
                                        simp only [keeps, EdgeValue.children, EdgeValue.entry, label, ↓reduceIte, admitted]
                                      · simp only [keeps, EdgeValue.children, EdgeValue.entry, label, ↓reduceIte]
                                  | cons fifth rest => rfl

/-- Original policy and independent acceptance give acceptance of the actual narrowed value. -/
theorem narrowAt_accepting [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (fuel : Nat) (value result : Value Symbol Guard)
    (before after : State Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrowAt fits admits fuel key value before = .done result after)
    (term : Term Symbol) (accepted : InternedGuardedLanguage.meaning holds ambient value term)
    (unary : ∀ symbol annotation child, term = .node symbol [child] →
      InternedGuardedLanguage.meaning holds ambient annotation child →
      admits key annotation = true ∧ fits key symbol = true)
    (application : ∀ annotation first second third fourth,
      term = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
      InternedGuardedLanguage.meaning holds ambient annotation first → admits key annotation = true)
    (filtered : ∀ annotation first second,
      term = .node ("filter", FullSyntax.Formula.top) [first, second] →
      InternedGuardedLanguage.meaning holds ambient annotation first → admits key annotation = true) :
    InternedGuardedLanguage.meaning holds ambient result term := by
  obtain ⟨rows, middle, exposed, _built, exactResult⟩ := narrowAt_edges
    holds ambient fits admits key fuel value before result after semantic.ready available closed actual
  have read : SourceEqualityProjectionRead.Read value before rows middle := .done fuel exposed
  obtain ⟨edge, member, edgeAccepted⟩ :=
    (read.exact semantic available closed holds ambient term).mpr accepted
  have independent := (InternedGuardedLanguage.edgeMeaning_all holds ambient edge term).mpr edgeAccepted
  exact (exactResult term).mpr ⟨edge, member,
    keeps_of_accepted holds ambient fits admits key term unary application filtered edge independent, independent⟩

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningOuterNarrow
open Language InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Typing Key : Type}

/-- Actual outer narrowing retains the chosen model under its original policy tests. -/
theorem narrow_accepting [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (fuel uv : Nat) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrow holeKey fits admits metadata fuel uv value before = .done result after)
    (term : Term Symbol) (accepted : InternedGuardedLanguage.meaning holds ambient value term)
    (unary : ∀ symbol annotation child, term = .node symbol [child] →
      InternedGuardedLanguage.meaning holds ambient annotation child →
      admits (holeKey metadata.typing uv) annotation = true ∧ fits (holeKey metadata.typing uv) symbol = true)
    (application : ∀ annotation first second third fourth,
      term = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
      InternedGuardedLanguage.meaning holds ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true)
    (filtered : ∀ annotation first second,
      term = .node ("filter", FullSyntax.Formula.top) [first, second] →
      InternedGuardedLanguage.meaning holds ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true) :
    InternedGuardedLanguage.meaning holds ambient result term := by
  by_cases typed : uv ∈ metadata.types
  · have same := MergedSourceComparison.Result.done.inj
      ((narrow_type holeKey fits admits metadata fuel uv value before typed).symm.trans actual)
    simpa only [← same.1] using accepted
  · cases value with
    | mu => cases actual; exact accepted
    | empty | reference | node | union =>
        have narrowed := actual
        simp [narrow, typed] at narrowed
        exact SourcePruningNativeView.narrowAt_accepting holds ambient fits admits
          (holeKey metadata.typing uv) fuel _ result before after semantic available closed narrowed
          term accepted unary application filtered

end MicroCFTA.SourcePruningOuterNarrow

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

section Runtime
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem narrow_available
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before =
      .done result after) : Available after result ∧ result.free = [] := by
  have skipped (same : result = value ∧ after = before) : Available after result ∧ result.free = [] := by
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨available, closed⟩
  by_cases typed : uv ∈ metadata.types
  · have pureDone := SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed
    have same := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨same.1.symm, same.2.symm⟩
  · cases value with
    | mu =>
        have same := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨same.1.symm, same.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [SourcePruningOuterNarrow.narrow, typed] at narrowed
        obtain ⟨rows, middle, exposed, built, _meaning⟩ := SourcePruningNativeView.narrowAt_edges
          (fun _ _ => true) (fun _ _ => False) fits admits (holeKey metadata.typing uv) fuel _ before
          result after ready available closed narrowed
        have verified := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel _ before
          ready.semantic ready.covered available closed
        have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using verified.semantic
        have resident : InternedNestedProvenance.Edges middle
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.edges rows middle exposed edge (List.mem_filter.mp member).1
        have children : ∀ child ∈ (rows.filter
            (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))).flatMap EdgeValue.children,
            Available middle child := by
          intro child member
          obtain ⟨edge, member, included⟩ := List.mem_flatMap.mp member
          exact semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge member) child included
        have constructed := InternedProbeProvenance.makeNode_available
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts.coherent semantic.1.normal.facts.cached children
        have closedRows : MergedColdReaderClosedInputs.ClosedEdges
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.closed rows middle exposed edge (List.mem_filter.mp member).1
        have constructedClosed := MergedColdReaderClosedInputs.makeNode_closed
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts resident closedRows
        rw [built] at constructed constructedClosed
        exact ⟨constructed.2.2, constructedClosed⟩

private theorem retained_action
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (fuel uv oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
    (caller reached : Caller width) (before after : Cached) (queries : SourceEndpointMemo.Memos)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (selectedAction : EnumerateM Symbol Constraint Unit)
    (preparedField : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (ordinary : Option (List (Except Error ((Nat × Nat × List Suspended × Node) × Core)) ×
      Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel uv oldHandle
      scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = .narrowed checked preparedField reached queries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    Success selectedAction checked () after.core := by
  simp only [runPrefix, reading, checking, decoded, prepared] at actual
  cases rawEq : ExceptT.run (selectedAction checked) with
  | nil => simp only [rawEq] at actual; cases actual
  | cons first rest =>
      cases first with
      | error fault => simp only [rawEq] at actual; cases actual
      | ok pair =>
          obtain ⟨token, observed⟩ := pair
          cases token
          cases rest with
          | cons _ _ => simp only [rawEq] at actual; cases actual
          | nil =>
              simp only [rawEq] at actual
              cases encoded : encodeNode value with
              | none => simp only [encoded] at actual; cases actual
              | some newHandle =>
                  simp only [encoded] at actual
                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                      scs before observed with
                  | none => simp only [adapted] at actual; cases actual
                  | some attached =>
                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel
                          metadata uv (.inr newHandle) attached.core) = [.ok ((false, metadata), attached.core)] := by
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
                      simp only [adapted, recorded] at actual
                      have ⟨_checked, _prepared, _caller, _queries, actionSame, _candidate, _right, _ordinary⟩ :=
                        Result.narrowed.inj actual
                      have coreSame : observed = after.core := by
                        simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq,
                          true_and, and_true] using actionSame
                      rw [Success, ← coreSame, rawEq]
                      exact List.mem_singleton_self _

end Runtime

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩


/-- Original models and the concrete annotation policy reach an actual retained prefix model. -/
theorem prefix_accepting
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies (SourcePruningEnumerationNativeLanguage.handles
      (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
      residualMeaning assignment before.core)
    (unary : ∀ symbol annotation child, assignment uv = .node symbol [child] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
      admits (holeKey metadata.typing uv) annotation = true ∧ fits (holeKey metadata.typing uv) symbol = true)
    (application : ∀ annotation first second third fourth,
      assignment uv = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true)
    (filtered : ∀ annotation first second,
      assignment uv = .node ("filter", FullSyntax.Formula.top) [first, second] →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
      admits (holeKey metadata.typing uv) annotation = true) :
    match runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query with
    | .parked _ (some after) _ =>
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment after.core
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
          residualMeaning assignment after.core
    | _ => False := by
  have backward := prefix_semantics holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory fuel uv caller before memos initial ready realized valid
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at valid backward ⊢
  have full := valid.2.1
  cases observed with
  | stopped read checked => exact backward
  | parked checked candidate raw =>
      cases candidate with
      | none => exact backward
      | some after =>
          obtain ⟨_oldHandle, _scs, _readAfter, _stored, _reading, law⟩ := backward
          exact ((law ambient residualMeaning assignment).mp satisfied).1
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, nativeHeap, selectedAction,
        final, decoded, narrowed, selectedPrepared, _prepared, reachedSame, queriesSame,
        post, _saved, shape⟩ := full
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      have readFrame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
        caller.checked.native.machine.heap fuel uv oldHandle scs readAfter checked
        (readFrame.total ready.safe.1.total) checkSuccess
      have checkedFrame := readFrame.trans checkFrame
      have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
        ready.safe ready.inside ready.root readSuccess).2.2.2
      have stored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
        simpa only [readFrame.values] using readStored
      obtain ⟨old, oldLookup, oldAvailable, oldClosed⟩ := realized uv oldHandle scs stored
      have oldSame : old = oldValue := Option.some.inj (oldLookup.symm.trans decoded)
      subst old
      have slotModel := satisfied.1.2 uv
      simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
        List.forall_mem_map] at slotModel
      have oldAccepted := (SourcePruningEnumerationNativeLanguage.handles_lookup
        (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
        oldHandle oldValue (assignment uv) decoded).mp slotModel.1
      have valueAccepted := SourcePruningOuterNarrow.narrow_accepting
        (SourceEqualityPCSGuard.holds formulas solver) ambient holeKey fits admits metadata
        fuel uv oldValue value caller.checked.native.machine.heap nativeHeap initial.ready.semantic
        oldAvailable oldClosed narrowed (assignment uv) oldAccepted unary application filtered
      rcases shape with ⟨empty, _action, _candidate, _right, _ordinary⟩ |
        ⟨newHandle, after, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
          _pending, _ready, _stored, _waiting, _right, _rest⟩
      · rw [empty] at valueAccepted
        exact False.elim (by simpa only [InternedGuardedLanguage.meaning] using valueAccepted)
      · rw [cachedSame]
        have actionSuccess := retained_action holeKey fits admits graph templates stop order metadata
          fuel uv oldHandle scs oldValue value caller reached before after memos.query readAfter checked
          nativeHeap selectedAction prepared right ordinary reading checking decoded selectedPrepared
          (by simpa only [actionSame, queriesSame, cachedSame] using actual)
        have available := narrow_available holeKey fits admits metadata fuel uv oldValue value
          caller.checked.native.machine.heap nativeHeap initial.ready.semantic.ready oldAvailable oldClosed narrowed
        have reachedHeap : reached.checked.native.machine.heap = nativeHeap := by
          rw [reachedSame]
          rfl
        have valueAvailable : Available reached.checked.native.machine.heap value := by
          rw [reachedHeap]
          exact available.1
        obtain ⟨handle, encodedActual, newDecoded⟩ := available_readback reached.checked.native.machine.heap
          value post.context.ready.semantic.ready.semantic.1.normal.facts.coherent valueAvailable available.2
        have handleSame : handle = newHandle := Option.some.inj (encodedActual.symm.trans encoded)
        subst handle
        let language := SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap
        have newAccepted : language newHandle (assignment uv) :=
          (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ newDecoded).mpr valueAccepted
        have narrows : ∀ term, language newHandle term → language oldHandle term := by
          intro term accepted
          have narrowedAccepted := (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ newDecoded).mp accepted
          have previous := SourcePruningOuterNarrow.narrow_sound (SourceEqualityPCSGuard.holds formulas solver)
            ambient holeKey fits admits metadata fuel uv oldValue caller.checked.native.machine.heap value nativeHeap
            initial.ready.semantic.ready initial.ready.semantic.guarded oldAvailable oldClosed narrowed term narrowedAccepted
          exact (SourcePruningEnumerationNativeLanguage.handles_keeps _ _ _ _ _ _ _ decoded post.effects.keeps).mpr
            ⟨oldValue, decoded, previous⟩
        have actualAction := prepared_action holeKey fits admits metadata fuel fuel uv oldHandle newHandle
          scs oldValue value caller.checked.native.machine.heap nativeHeap narrowed nonempty encoded
        rw [selectedPrepared] at actualAction
        have selectedSame : selectedAction =
            (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
              else representative fuel uv >>= fun selected =>
                setValue selected (.unenumerated (some newHandle) scs)) :=
          Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actualAction).1).2
        rw [selectedSame] at actionSuccess
        by_cases equalHandle : newHandle = oldHandle
        · rw [ite_eq_left equalHandle] at actionSuccess
          have endpoint := (success_pure () () checked after.core).mp actionSuccess
          have checkedSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_keeps_frame
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
            reached.checked.native.machine.heap before.core checked residualMeaning assignment
            realized checkedFrame post.effects.keeps).mpr satisfied
          simpa only [endpoint.2] using checkedSatisfied
        · rw [ite_eq_right equalHandle] at actionSuccess
          obtain ⟨selected, resolved, readingRoot, written⟩ := (success_bind _ _ _ _ _).mp actionSuccess
          have resolvedFrame := representative_frame fuel uv selected checked resolved
            (checkedFrame.total ready.safe.1.total) readingRoot
          have checkedRoot : IsRoot checked.representatives uv :=
            ⟨ready.root.choose, (checkedFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
          obtain ⟨found, foundLookup, selectedRoot, _endpoint⟩ :=
            (representative_success fuel uv checked resolved selected).mp readingRoot
          have selectedIsUv : selected = uv := by
            rw [selectedRoot]
            exact (UnionFind.reaches_unique
              (UnionFind.findRoot_correct fuel checked.representatives uv found foundLookup).1
              checkedRoot.choose_spec).1
          rw [selectedIsUv] at written
          have wholeFrame := checkedFrame.trans resolvedFrame
          have resolvedStored : resolved.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
            simpa only [wholeFrame.values] using stored
          have resolvedSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_keeps_frame
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
            reached.checked.native.machine.heap before.core resolved residualMeaning assignment
            realized wholeFrame post.effects.keeps).mpr satisfied
          exact (EnumerationSemantics.pending_write_semantics language residualMeaning assignment
            resolved after.core uv oldHandle newHandle scs resolvedStored written narrows).mpr
            ⟨resolvedSatisfied, newAccepted⟩

end MicroCFTA.SourcePruningEnumerationSelectedStep
