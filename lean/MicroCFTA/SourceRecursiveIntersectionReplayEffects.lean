import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceRecursiveIntersectionKernelStability

/-!
# Replay of actual recursive caller effects

Completed physical constructor work and canonical domain allocation reuse
their exact original results after later table growth. Ordered successful
calls replay without another allocation in either source cache family.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- Completed ordinary source work reuses its exact result and leaves both later caches unchanged. -/
theorem work_replay [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (before after : Machine Symbol Guard) (value : A) (final : Machine Symbol Guard) (valid : Valid before)
    (done : work request before = .done value final) (growth : Extension final after) :
    work request after = .done value after := by
  obtain ⟨sameValue, sameState⟩ := work_done request before value final done
  have heapGrowth : Grows (run request before.heap).2 after.heap := by
    simpa only [sameState] using growth.heap
  have repeated := InternedConstructorTemplates.replay request before.heap after.heap valid.1.coherent.valid heapGrowth
  simp only [work, repeated, ← sameValue]

/-- Actual physical payload lookup retains the complete original value after later caller effects. -/
theorem read_grows (before after : Machine Symbol Guard) (growth : Extension before after) (name : Nat)
    (value : Value Symbol Guard) (read : SourcePreparedSharedRows.read before.heap name = some value) :
    SourcePreparedSharedRows.read after.heap name = some value := by
  unfold SourcePreparedSharedRows.read at read ⊢
  cases issued : before.heap.nodes.issued name with
  | none => simp only [issued, Option.bind_none] at read; cases read
  | some key =>
      have stored : before.heap.nodeRecords key = some value := by simpa only [issued, Option.bind_some] using read
      rw [growth.history _ _ issued]
      exact growth.heap.nodeRecords _ _ stored

/-- Canonical source domain allocation reuses its original shifted identity without changing the later cache. -/
theorem make_domain_replay (before after : Cache.State DomainKey) (key : DomainKey) (valid : Cache.Valid before)
    (growth : Extends (IntersectionEmptyDomain.make before key).2.table after.table) :
    IntersectionEmptyDomain.make after key = ((IntersectionEmptyDomain.make before key).1, after) := by
  by_cases empty : key = IntersectionEmptyDomain.emptyKey
  · simp only [IntersectionEmptyDomain.make, empty, ite_true]
  · have stored := (Cache.intern_correct before key valid).2.1
    have present : after.table key = some (Cache.intern before key).1 := by
      apply growth key (Cache.intern before key).1
      simpa only [IntersectionEmptyDomain.make, empty, ite_false] using stored
    simp only [IntersectionEmptyDomain.make, empty, ite_false, Cache.intern, present]

/-- Sequential successful source effects replay each original value in the unchanged later cache. -/
theorem bind_replay (first : Machine Symbol Guard → Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B) (before after : Machine Symbol Guard)
    (property : Machine Symbol Guard → A → Prop) (checked : Checked before (first before) property)
    (tailGrowth : ∀ head middle, first before = .done head middle → Valid middle → property middle head →
      Extension middle (next head middle).state)
    (firstReplay : ∀ head middle, first before = .done head middle → Extension middle after → first after = .done head after)
    (nextReplay : ∀ head middle, first before = .done head middle → Valid middle → property middle head →
      ∀ value final, next head middle = .done value final → Extension final after → next head after = .done value after)
    (value : B) (final : Machine Symbol Guard) (done : (first before).bind next = .done value final)
    (growth : Extension final after) : (first after).bind next = .done value after := by
  cases returned : first before with
  | failed failure state => simp only [returned, Result.bind] at done; cases done
  | done head middle =>
      have middleValid : Valid middle := by simpa only [returned, Result.state] using checked.valid
      have holds := checked.result head middle returned
      have tail : next head middle = .done value final := by simpa only [returned, Result.bind] using done
      have later : Extension middle final := by
        simpa only [tail, Result.state] using tailGrowth head middle returned middleValid holds
      rw [firstReplay head middle returned (later.trans growth)]
      exact nextReplay head middle returned middleValid holds value final tail growth

/-- Actual ordinary constructor work extends both source histories. -/
theorem work_extension [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (state : Machine Symbol Guard) (valid : Valid state) : Extension state (work request state).state := by
  exact ⟨(InternedConstructorTemplates.run_correct request state.heap valid.1.coherent.valid).2,
    run_issued_extends request state.heap valid.1.coherent.valid, extends_refl _⟩

/-- Reached prefixes and their actual ordinary constructors replay without new allocation. -/
theorem bind_work_replay [DecidableEq (EdgeKey Symbol Guard)] (first : Machine Symbol Guard → Result Symbol Guard A)
    (request : A → Work Symbol Guard B) (before after : Machine Symbol Guard)
    (property : Machine Symbol Guard → A → Prop) (checked : Checked before (first before) property)
    (firstReplay : ∀ head middle, first before = .done head middle → Extension middle after → first after = .done head after)
    (value : B) (final : Machine Symbol Guard)
    (done : (first before).bind (fun head current => work (request head) current) = .done value final)
    (growth : Extension final after) :
    (first after).bind (fun head current => work (request head) current) = .done value after :=
  bind_replay first (fun head current => work (request head) current) before after property checked
    (fun head middle _ valid _ => work_extension (request head) middle valid) firstReplay
    (fun head middle _ valid _ value final returned later => work_replay (request head) middle after value final valid returned later)
    value final done growth

/-- Ordered completed request lists replay all original values without new cache effects. -/
theorem walk_replay (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, Valid state → input state request → Checked state (call request state) output)
    (replay : ∀ request ∈ requests, ∀ before after value final, Valid before → input before request →
      call request before = .done value final → Extension final after → call request after = .done value after)
    (before after : Machine Symbol Guard) (values : List B) (final : Machine Symbol Guard)
    (valid : Valid before) (inputs : ∀ request ∈ requests, input before request)
    (done : walk call requests before = .done values final) (growth : Extension final after) :
    walk call requests after = .done values after := by
  induction requests generalizing before values final with
  | nil =>
      simp only [walk] at done ⊢
      cases done
      rfl
  | cons head tail ih =>
      have checked := calls head List.mem_cons_self before valid (inputs head List.mem_cons_self)
      cases first : call head before with
      | failed failure state => simp only [walk, first, Result.bind] at done; cases done
      | done value middle =>
          have middleValid : Valid middle := by simpa only [first, Result.state] using checked.valid
          have earlier : Extension before middle := by simpa only [first, Result.state] using checked.extension
          have tailInputs : ∀ request ∈ tail, input middle request := fun request member =>
            inputStable before middle earlier request (inputs request (List.mem_cons_of_mem _ member))
          have tailCalls := fun request member => calls request (List.mem_cons_of_mem head member)
          have tailReplay := fun request member => replay request (List.mem_cons_of_mem head member)
          have restChecked := walk_checked call tail input output inputStable outputStable tailCalls middle middleValid tailInputs
          cases rest : walk call tail middle with
          | failed failure state => simp only [walk, first, Result.bind, rest] at done; cases done
          | done results state =>
              simp only [walk, first, Result.bind, rest] at done
              cases done
              have later : Extension middle final := by simpa only [rest, Result.state] using restChecked.extension
              have firstAgain := replay head List.mem_cons_self before after value middle valid (inputs head List.mem_cons_self)
                first (later.trans growth)
              have restAgain := ih tailCalls tailReplay middle results final middleValid tailInputs rest growth
              simp only [walk, firstAgain, Result.bind, restAgain]

/-- Replay of actual recursive requests requires their original checked inputs and completed source execution. -/
def Replays
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right before after value final,
    Valid before → Domain before domain → Available before.heap left → Available before.heap right →
    call domain left right before = .done value final → Extension final after →
      call domain left right after = .done value after

end MicroCFTA.SourceRecursiveIntersectionKernel
