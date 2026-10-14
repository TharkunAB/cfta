import MicroCFTA.SourceRecursiveIntersectionUnionReadback
import MicroCFTA.SourceRecursiveIntersectionMuReadback
import MicroCFTA.SourceRecursiveIntersectionNativeApi
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate
import MicroCFTA.SourceRecursiveIntersectionNativeGuardedHeap

/-!
# Actual native union and Mu branch representatives

Completed checked native calls supply allocation-free source branches at all
larger kernel bounds and later caches. Union branches retain ordered child
representatives and exact union normalization. Mu branches retain the actual
extended domain, body representative, and independent least language.
These witnesses do not assume the complete two-input product law.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)

/-- A completed checked native node exposes its actual allocation-free source branch in every later cache. -/
theorem native_node_branch_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (request : NodeRequest Symbol Guard)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : NodeReady state.machine request)
    (done : execute emptyGuard conjoin fuel (.node request .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node request .pure) state) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      ∃ bound, ∀ extra view, Extension after.machine view →
        onNode emptyGuard conjoin (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra))
          request.domain request.left request.right view = .done value view := by
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  obtain ⟨afterValid, earlier, _, bound, completed⟩ := native_node_correct emptyGuard conjoin fuel request state after value
    valid ready done (evaluated.bounds_of_ranges ranges)
  refine ⟨afterValid, earlier, bound, ?_⟩
  intro extra view growth
  have returned := SourceRecursiveIntersectionKernel.execute_larger_replay emptyGuard conjoin (bound + 1) extra
    request.domain request.left request.right state.machine view valid.machine ready.1 ready.2.1 ready.2.2
    value after.machine (completed 1) growth
  rw [Nat.add_right_comm bound 1 extra] at returned
  exact returned

/-- An actual checked left-union call retains every ordered child representative and its full normalized language. -/
theorem native_left_union_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, .union entry members depth free, other⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.union entry members depth free) other = .leftUnion)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, .union entry members depth free, other⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, .union entry members depth free, other⟩ .pure) state) :
    ∃ bound, ∀ extra, ∃ values,
      All₂ (fun member result => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)
        domain member other after.machine = .done result after.machine) members values ∧
      ∀ holds ambient term, InternedGuardedLanguage.meaning holds ambient value term ↔
        ∃ result ∈ values, InternedGuardedLanguage.meaning holds ambient result term := by
  obtain ⟨afterValid, growth, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  have known := ready.1.grows domain growth
  have available := growth.available other ready.2.2
  have source := growth.available (.union entry members depth free) ready.2.1
  have membersAvailable : ∀ member ∈ members, Available after.machine.heap member := fun member present =>
    source.children member (by simpa only [children] using present)
  refine ⟨bound, ?_⟩
  intro extra
  have returned := completed extra after.machine (.refl _)
  simp only [onNode, selected] at returned
  exact union_language _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain members other true after.machine after.machine afterValid.machine afterValid.machine known available membersAvailable
    value after.machine returned (.refl _)

/-- An actual checked right-union call retains ordered right operands and the same exact normalized language. -/
theorem native_right_union_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, other, .union entry members depth free⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.union entry members depth free) = .rightUnion)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, other, .union entry members depth free⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, other, .union entry members depth free⟩ .pure) state) :
    ∃ bound, ∀ extra, ∃ values,
      All₂ (fun member result => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)
        domain other member after.machine = .done result after.machine) members values ∧
      ∀ holds ambient term, InternedGuardedLanguage.meaning holds ambient value term ↔
        ∃ result ∈ values, InternedGuardedLanguage.meaning holds ambient result term := by
  obtain ⟨afterValid, growth, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  have known := ready.1.grows domain growth
  have available := growth.available other ready.2.1
  have source := growth.available (.union entry members depth free) ready.2.2
  have membersAvailable : ∀ member ∈ members, Available after.machine.heap member := fun member present =>
    source.children member (by simpa only [children] using present)
  refine ⟨bound, ?_⟩
  intro extra
  have returned := completed extra after.machine (.refl _)
  simp only [onNode, selected] at returned
  exact union_language _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain members other false after.machine after.machine afterValid.machine afterValid.machine known available membersAvailable
    value after.machine returned (.refl _)

/-- Actual checked native Mu completion supplies its original body, exact extended domain, and independent least language. -/
theorem native_mu_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : NodeReady state.machine ⟨domain, left, right⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key left right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision domain.key left right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision domain.key left right = .rightMu)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.machine.heap)
    (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, left, right⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, left, right⟩ .pure) state) :
    ∃ bound, ∀ extra, ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      Domain after.machine extended ∧ Available after.machine.heap bodyValue ∧
      SourceRecursiveIntersectionEnvironment.enter after.machine.domains domain.key left right first second = (extended, after.machine.domains) ∧
      SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) extended (body left) (body right) after.machine =
        .done bodyValue after.machine ∧
      ∀ holds ambient, InternedGuardedLanguage.meaning holds ambient value = BinderLanguage.least (fun candidate =>
        InternedGuardedLanguage.meaning holds (InternedGuardedLanguage.bind ambient
          (.intersection (pair first second).1 (pair first second).2) candidate) bodyValue) := by
  obtain ⟨afterValid, growth, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have retained := (evaluated.bounds_of_ranges ranges).guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode domain left right state.machine ready) valid
    (semantic_requestNode domain left right state.machine ready) semantic (by intro value; trivial) guarded
  refine ⟨bound, ?_⟩
  intro extra
  have returned := completed extra after.machine (.refl _)
  have muDone : mu (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)) domain left right after.machine =
      .done value after.machine := by
    rcases selected with selected | selected | selected <;> simpa only [onNode, selected] using returned
  exact mu_language _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain left right after.machine after.machine afterValid.machine (ready.1.grows domain growth)
    (growth.available left ready.2.1) (growth.available right ready.2.2) retained.1 retained.2 value after.machine muDone (.refl _)

end MicroCFTA.SourceRecursiveIntersectionNative
