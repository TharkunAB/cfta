import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.EnumerationRendering

/-!
# Complete native rendering of discharged graph carriers

Discharged storage excludes every pending branch that reads a graph handle.
The generic and native renderers then have the same successful executions.
The original carrier and reference predicates supply finite render bounds.
-/
namespace MicroCFTA.SourcePruningEnumerationRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationSemantics EnumerationExecution EnumerationCompressionFrame
open EnumerationOrder EnumerationCarriers EnumerationGraphReferences EnumerationRenderability
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

private theorem discharged_values (before after : State Symbol EnumGuard)
    (same : after.values = before.values) (discharged : Discharged before) : Discharged after := by
  intro uv node scs stored
  exact discharged uv node scs (by simpa only [same] using stored)

private theorem read_discharged (fuel uv : Nat) (before after : State Symbol EnumGuard)
    (value : UVarValue Symbol) (total : UnionFind.Total before.representatives)
    (discharged : Discharged before) (observed : Success (getValue fuel uv) before value after) :
    (UnionFind.Total after.representatives ∧ Discharged after) ∧
      ∀ node scs, value = .unenumerated node scs → node = none ∧ scs = [] := by
  obtain ⟨frame, root, _size, _path, _afterPath, stored⟩ :=
    EnumerationCompressionFrame.getValue_frame fuel uv before after value total observed
  refine ⟨⟨frame.total total, discharged_values before after frame.values discharged⟩, ?_⟩
  intro node scs equal
  exact discharged root node scs (by simpa only [equal] using stored)

private theorem mapM_transfer (source target : α → EnumerateM Symbol EnumGuard β)
    (invariant : State Symbol EnumGuard → Prop)
    (step : ∀ input before output after, invariant before → Success (source input) before output after →
      invariant after ∧ Success (target input) before output after)
    (inputs : List α) (before after : State Symbol EnumGuard) (outputs : List β)
    (valid : invariant before) (observed : Success (inputs.mapM source) before outputs after) :
    invariant after ∧ Success (inputs.mapM target) before outputs after := by
  induction inputs generalizing before after outputs with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] outputs before after).mp observed
      exact ⟨valid, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at observed ⊢
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨middleValid, firstTransferred⟩ := step input before output middle valid first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨lastValid, restTransferred⟩ := ih middle last tail middleValid remaining
      obtain ⟨rfl, rfl⟩ := (success_pure (output :: tail) outputs last after).mp final
      refine ⟨lastValid, (success_bind _ _ _ _ _).mpr ⟨output, middle, firstTransferred, ?_⟩⟩
      exact (success_bind _ _ _ _ _).mpr
        ⟨tail, after, restTransferred, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

private theorem fragment_transfers (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (graph : Graph Symbol EnumGuard) (marker : Symbol) (fuel : Nat) :
    ∀ fragment (before after : State Symbol EnumGuard) term,
      UnionFind.Total before.representatives → Discharged before →
      (Success (expandFragment heap marker fuel fragment) before term after →
        (UnionFind.Total after.representatives ∧ Discharged after) ∧
          Success (EnumerationState.expandFragment graph marker fuel fragment) before term after) ∧
      (Success (EnumerationState.expandFragment graph marker fuel fragment) before term after →
        (UnionFind.Total after.representatives ∧ Discharged after) ∧
          Success (expandFragment heap marker fuel fragment) before term after) := by
  induction fuel with
  | zero =>
      intro fragment before after term total discharged
      constructor <;> intro observed <;>
        exact (success_failure .fuelExhausted before after term observed).elim
  | succ fuel ih =>
      intro fragment before after term total discharged
      constructor
      · intro observed
        cases fragment with
        | node symbol children =>
            change Success (children.mapM (expandFragment heap marker fuel) >>= fun terms =>
              pure (.node symbol terms)) before term after at observed
            obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨middleValid, transferred⟩ := mapM_transfer _ _
              (fun state => UnionFind.Total state.representatives ∧ Discharged state)
              (fun child previous output next valid success =>
                (ih child previous next output valid.1 valid.2).1 success)
              children before middle terms ⟨total, discharged⟩ traversed
            obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) term middle after).mp final
            exact ⟨middleValid, (success_bind _ _ _ _ _).mpr
              ⟨terms, after, transferred, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩
        | hole uv =>
            change Success (getValue (fuel + 1) uv >>= fun value => match value with
              | .enumerated fragment => expandFragment heap marker fuel fragment
              | .unenumerated (some handle) _ => match lookupNode heap handle with
                | none => failure .unresolvedReference
                | some value => if MergedOrdinaryHeight.recursiveBoundary value then
                    pure (.node marker []) else failure .unfinishedFragment
              | _ => failure .unfinishedFragment) before term after at observed
            obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨middleValid, free⟩ := read_discharged (fuel + 1) uv before middle value total discharged reading
            cases value with
            | eliminated => exact (success_failure .unfinishedFragment middle after term continued).elim
            | unenumerated node scs =>
                obtain ⟨rfl, rfl⟩ := free node scs rfl
                exact (success_failure .unfinishedFragment middle after term continued).elim
            | enumerated fragment =>
                obtain ⟨afterValid, transferred⟩ :=
                  (ih fragment middle after term middleValid.1 middleValid.2).1 continued
                exact ⟨afterValid, (success_bind _ _ _ _ _).mpr
                  ⟨.enumerated fragment, middle, reading, transferred⟩⟩
      · intro observed
        cases fragment with
        | node symbol children =>
            change Success (children.mapM (EnumerationState.expandFragment graph marker fuel) >>= fun terms =>
              pure (.node symbol terms)) before term after at observed
            obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨middleValid, transferred⟩ := mapM_transfer _ _
              (fun state => UnionFind.Total state.representatives ∧ Discharged state)
              (fun child previous output next valid success =>
                (ih child previous next output valid.1 valid.2).2 success)
              children before middle terms ⟨total, discharged⟩ traversed
            obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) term middle after).mp final
            exact ⟨middleValid, (success_bind _ _ _ _ _).mpr
              ⟨terms, after, transferred, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩
        | hole uv =>
            simp only [EnumerationState.expandFragment] at observed
            obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨middleValid, free⟩ := read_discharged (fuel + 1) uv before middle value total discharged reading
            cases value with
            | eliminated => exact (success_failure .unfinishedFragment middle after term continued).elim
            | unenumerated node scs =>
                obtain ⟨rfl, rfl⟩ := free node scs rfl
                exact (success_failure .unfinishedFragment middle after term continued).elim
            | enumerated fragment =>
                obtain ⟨afterValid, transferred⟩ :=
                  (ih fragment middle after term middleValid.1 middleValid.2).2 continued
                exact ⟨afterValid, (success_bind _ _ _ _ _).mpr
                  ⟨.enumerated fragment, middle, reading, transferred⟩⟩

/-- Discharged storage gives the same successful fragment trace in both renderers. -/
theorem expandFragment_bridge (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (graph : Graph Symbol EnumGuard) (marker : Symbol) (fuel : Nat) (fragment : Fragment Symbol)
    (before after : State Symbol EnumGuard) (term : Term Symbol)
    (total : UnionFind.Total before.representatives) (discharged : Discharged before) :
    Success (expandFragment heap marker fuel fragment) before term after ↔
      Success (EnumerationState.expandFragment graph marker fuel fragment) before term after := by
  constructor
  · intro observed
    exact ((fragment_transfers heap graph marker fuel fragment before after term total discharged).1 observed).2
  · intro observed
    exact ((fragment_transfers heap graph marker fuel fragment before after term total discharged).2 observed).2

/-- Discharged storage gives the same successful root trace in both renderers. -/
theorem expandUVar_bridge (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (graph : Graph Symbol EnumGuard) (marker : Symbol) (fuel uv : Nat)
    (before after : State Symbol EnumGuard) (term : Term Symbol)
    (total : UnionFind.Total before.representatives) (discharged : Discharged before) :
    Success (expandUVar heap marker fuel uv) before term after ↔
      Success (EnumerationState.expandUVar graph marker fuel uv) before term after := by
  constructor
  · intro observed
    unfold expandUVar at observed
    obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨middleValid, free⟩ := read_discharged (fuel + 1) uv before middle value total discharged reading
    cases value with
    | eliminated => exact (reject_unsuccessful middle after term continued).elim
    | unenumerated node scs =>
        obtain ⟨rfl, rfl⟩ := free node scs rfl
        exact (reject_unsuccessful middle after term continued).elim
    | enumerated fragment =>
        exact (success_bind _ _ _ _ _).mpr ⟨.enumerated fragment, middle, reading,
          (expandFragment_bridge heap graph marker fuel fragment middle after term middleValid.1 middleValid.2).mp continued⟩
  · intro observed
    unfold EnumerationState.expandUVar at observed
    obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨middleValid, free⟩ := read_discharged (fuel + 1) uv before middle value total discharged reading
    cases value with
    | eliminated => exact (reject_unsuccessful middle after term continued).elim
    | unenumerated node scs =>
        obtain ⟨rfl, rfl⟩ := free node scs rfl
        exact (reject_unsuccessful middle after term continued).elim
    | enumerated fragment =>
        exact (success_bind _ _ _ _ _).mpr ⟨.enumerated fragment, middle, reading,
          (expandFragment_bridge heap graph marker fuel fragment middle after term middleValid.1 middleValid.2).mpr continued⟩

private def proofGraph : Graph Symbol EnumGuard := ⟨fun _ => .empty, fun _ _ => 0⟩

private theorem proofGraph_complete : CompleteGraph (proofGraph : Graph Symbol EnumGuard) := by
  constructor
  · intro node body equal
    change (.empty : Node Symbol EnumGuard) = .recursive body at equal
    cases equal
  · intro node edges equal
    change (.empty : Node Symbol EnumGuard) = .alternatives edges at equal
    cases equal

private theorem discharged_finished (graph : Graph Symbol EnumGuard) (before : State Symbol EnumGuard)
    (discharged : Discharged before) : Finished graph before := by
  intro value member
  cases value with
  | eliminated | enumerated _ => rfl
  | unenumerated node scs =>
      obtain ⟨uv, stored⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨rfl, rfl⟩ := discharged uv node scs stored
      rfl

/-- Original carrier provenance gives a finite native fragment rendering. -/
theorem expandFragment_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier : Nat) (fragment : Fragment Symbol)
    (before : State Symbol EnumGuard) (safe : Safe before)
    (ordered : Stratified before level frontier) (discharged : Discharged before)
    (references : ReferencesCarry before) (carried : FragmentCarries before fragment) :
    ∃ fuel term after, Success (expandFragment heap marker fuel fragment) before term after ∧
      RenderStable before after := by
  let graph : Graph Symbol EnumGuard := proofGraph
  have ready : EnumerationRendering.RenderReady graph level frontier before :=
    ⟨safe, discharged_finished graph before discharged, references, ordered⟩
  obtain ⟨fuel, term, after, observed, stable⟩ := EnumerationRendering.expandFragment_complete
    graph proofGraph_complete marker level frontier fragment before ready carried
  exact ⟨fuel, term, after,
    (expandFragment_bridge heap graph marker fuel fragment before after term safe.1.total discharged).mpr observed,
    stable⟩

/-- Original root and stored-reference provenance give a finite native root rendering. -/
theorem expandUVar_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier uv : Nat)
    (before : State Symbol EnumGuard) (safe : Safe before)
    (ordered : Stratified before level frontier) (discharged : Discharged before)
    (references : ReferencesCarry before) (carried : CarriesGraph before uv) :
    ∃ fuel term after, Success (expandUVar heap marker fuel uv) before term after ∧
      RenderStable before after := by
  let graph : Graph Symbol EnumGuard := proofGraph
  have ready : EnumerationRendering.RenderReady graph level frontier before :=
    ⟨safe, discharged_finished graph before discharged, references, ordered⟩
  obtain ⟨fuel, term, after, observed, stable⟩ := EnumerationRendering.expandUVar_complete
    graph proofGraph_complete marker level frontier uv before ready carried
  exact ⟨fuel, term, after,
    (expandUVar_bridge heap graph marker fuel uv before after term safe.1.total discharged).mpr observed,
    stable⟩

/-- Original carrier provenance gives one finite bound for the root and all residuals. -/
theorem render_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier uv : Nat)
    (before : State Symbol EnumGuard) (safe : Safe before)
    (ordered : Stratified before level frontier) (discharged : Discharged before)
    (references : ReferencesCarry before) (carried : CarriesGraph before uv) :
    ∃ fuel term pending after, Success (render heap marker fuel uv) before (term, pending) after ∧
      RenderStable before after := by
  let graph : Graph Symbol EnumGuard := proofGraph
  have ready : EnumerationRendering.RenderReady graph level frontier before :=
    ⟨safe, discharged_finished graph before discharged, references, ordered⟩
  obtain ⟨rootFuel, term, middle, rootRun, rootStable⟩ := EnumerationRendering.expandUVar_complete
    graph proofGraph_complete marker level frontier uv before ready carried
  have middleReady := EnumerationRendering.ready_read graph level frontier before middle ready rootStable
  have middleDischarged := discharged_values before middle rootStable.values discharged
  obtain ⟨pendingFuel, pending, after, pendingRun, pendingStable⟩ :=
    EnumerationRendering.renderObligations_complete graph proofGraph_complete marker level frontier
      middle.obligations middle middleReady middleReady.references.2
  let fuel := rootFuel + pendingFuel
  have rootRaised : Success (EnumerationState.expandUVar graph marker fuel uv) before term middle :=
    EnumerationExecution.expandUVar_moreFuel graph marker rootFuel pendingFuel uv before term middle rootRun
  have pendingRaised : Success (middle.obligations.mapM fun obligation => do
      pure (obligation.1, ← EnumerationState.expandFragment graph marker fuel obligation.2))
      middle pending after := by
    have raised := retains_mapM _ _ (fun (obligation : EnumGuard × Fragment Symbol) => retains_bind _ _ _ _
      (EnumerationExecution.expandFragment_moreFuel graph marker pendingFuel rootFuel obligation.2)
      (fun _ => retains_refl _)) middle.obligations middle pending after pendingRun
    simpa only [fuel, Nat.add_comm] using raised
  have nativeRoot := (expandUVar_bridge heap graph marker fuel uv before middle term safe.1.total discharged).mpr rootRaised
  have pendingTransferred := mapM_transfer
    (fun (obligation : EnumGuard × Fragment Symbol) => do
      pure (obligation.1, ← EnumerationState.expandFragment graph marker fuel obligation.2))
    (fun (obligation : EnumGuard × Fragment Symbol) => do
      pure (obligation.1, ← expandFragment heap marker fuel obligation.2))
    (fun state => UnionFind.Total state.representatives ∧ Discharged state)
    (by
      intro obligation previous output next valid observed
      obtain ⟨term, expanded, expansion, final⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨expandedValid, transferred⟩ :=
        (fragment_transfers heap graph marker fuel obligation.2 previous expanded term valid.1 valid.2).2 expansion
      obtain ⟨rfl, rfl⟩ := (success_pure (obligation.1, term) output expanded next).mp final
      exact ⟨expandedValid, (success_bind _ _ _ _ _).mpr
        ⟨term, next, transferred, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩)
    middle.obligations middle after pending ⟨rootStable.safe.1.total, middleDischarged⟩ pendingRaised
  refine ⟨fuel, term, pending, after, ?_, rootStable.trans pendingStable⟩
  unfold render
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨term, middle, nativeRoot, ?_⟩
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨middle, middle, (get_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact (success_bind _ _ _ _ _).mpr
    ⟨pending, after, pendingTransferred.2, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

end MicroCFTA.SourcePruningEnumerationRendering
