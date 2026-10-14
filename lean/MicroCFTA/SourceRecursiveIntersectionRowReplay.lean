import MicroCFTA.SourceRecursiveIntersectionReplayCalls
import MicroCFTA.SourceRecursiveIntersectionKernelReadback

/-!
# Individual results of replayed ordered requests

Each completed ordered walk replays every request in the same later cache.
The pointwise relation retains request order and duplicate occurrences.
Child and edge specialization uses actual checked recursive calls.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- Each original request replays its own exact result without allocation in a later cache. -/
theorem walk_pointwise_replay (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, Valid state → input state request → Checked state (call request state) output)
    (replay : ∀ request ∈ requests, ∀ before after value final, Valid before → input before request →
      call request before = .done value final → Extension final after → call request after = .done value after)
    (before after : Machine Symbol Guard) (values : List B) (final : Machine Symbol Guard)
    (valid : Valid before) (inputs : ∀ request ∈ requests, input before request)
    (done : walk call requests before = .done values final) (growth : Extension final after) :
    All₂ (fun request value => call request after = .done value after) requests values := by
  induction requests generalizing before values final with
  | nil => simp only [walk] at done; cases done; exact .nil
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
              exact .cons (replay head List.mem_cons_self before after value middle valid (inputs head List.mem_cons_self)
                first (later.trans growth)) (ih tailCalls tailReplay middle results final middleValid tailInputs rest growth)

/-- Pointwise exact replay identifies every returned occurrence with an actual request. -/
theorem pointwise_result_member (call : A → Result Symbol Guard B) (requests : List A) (values : List B)
    (state : Machine Symbol Guard) (related : All₂ (fun request value => call request = .done value state) requests values)
    (value : B) : value ∈ values ↔ ∃ request ∈ requests, call request = .done value state := by
  induction related with
  | nil => simp
  | @cons first output rest outputs head tail ih =>
      constructor
      · intro member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨first, List.mem_cons_self, head⟩
        · obtain ⟨request, present, done⟩ := ih.mp member
          exact ⟨request, List.mem_cons_of_mem _ present, done⟩
      · rintro ⟨request, member, done⟩
        rcases List.mem_cons.mp member with rfl | member
        · have same := (Result.done.inj (head.symm.trans done)).1
          exact same ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨request, member, done⟩)

/-- Ordered physical child pairs replay their exact values in one later cache. -/
theorem children_pointwise_replay
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (requests : List (Value Symbol Guard × Value Symbol Guard)) (before after : Machine Symbol Guard)
    (values : List (Value Symbol Guard)) (final : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (available : ∀ pair ∈ requests, Available before.heap pair.1 ∧ Available before.heap pair.2)
    (done : walk (fun pair => call domain pair.1 pair.2) requests before = .done values final) (growth : Extension final after) :
    All₂ (fun pair value => call domain pair.1 pair.2 after = .done value after) requests values := by
  let input := fun (state : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap pair.1 ∧ Available state.heap pair.2
  have stable : Stable input := fun before after extension pair known =>
    ⟨known.1.grows domain extension, extension.available _ known.2.1, extension.available _ known.2.2⟩
  exact walk_pointwise_replay (fun pair => call domain pair.1 pair.2) requests input _ stable available_stable
    (fun pair _ state valid known => calls domain pair.1 pair.2 state valid known.1 known.2.1 known.2.2)
    (fun pair _ before after value final valid known => replay domain pair.1 pair.2 before after value final valid known.1 known.2.1 known.2.2)
    before after values final valid (fun pair member => ⟨known, available pair member⟩) done growth

/-- Matched source edge occurrences replay their exact complete rows in one later cache. -/
theorem rows_pointwise_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (before after : Machine Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (final : Machine Symbol Guard)
    (valid : Valid before) (known : Domain before domain)
    (leftResident : ∀ edge ∈ left, EdgeResident before.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident before.heap edge)
    (done : walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) before = .done rows final)
    (growth : Extension final after) :
    All₂ (fun pair row => edge emptyGuard conjoin (call domain) pair.1 pair.2 after = .done row after) (pairs left right) rows := by
  let input := fun (state : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain state domain ∧ EdgeResident state.heap pair.1 ∧ EdgeResident state.heap pair.2
  have stable : Stable input := fun before after extension pair known =>
    ⟨known.1.grows domain extension, edge_grows _ _ extension.heap _ known.2.1, edge_grows _ _ extension.heap _ known.2.2⟩
  apply walk_pointwise_replay (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ state valid known => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2 state valid known.1 known.2.1 known.2.2)
    (fun pair _ before after value final valid known => edge_replay emptyGuard conjoin call calls replay domain pair.1 pair.2
      before after valid known.1 known.2.1 known.2.2 value final)
    before after rows final valid _ done growth
  intro pair member
  have selected := (pairs_member left right pair).mp member
  exact ⟨known, leftResident pair.1 selected.1, rightResident pair.2 selected.2.1⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
