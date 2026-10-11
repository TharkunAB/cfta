import MicroCFTA.SymbolicMerge

/-!
# Live-variable scope in normalized symbolic problems

Successful renaming rejects every variable absent from the live-domain map.
These proofs establish that fresh child variables cannot affect constraints
that were already present before expansion.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation instantiate instantiateMany Satisfies)

/-- Every variable read by the actual occurrence test belongs to the allowed set. -/
def InScope (allowed : Nat → Prop) (fragment : Fragment Symbol) : Prop :=
  ∀ name, occurs name fragment = true → allowed name

/-- Every context in an existence or equality requirement uses allowed live variables. -/
def ObligationInScope (allowed : Nat → Prop) : Obligation Symbol → Prop
  | .exists target => InScope allowed target.fragment
  | .equal left right => InScope allowed left.fragment ∧ InScope allowed right.fragment

/-- All pending requirements refer only to the problem's current live-domain names. -/
def ProblemScoped (problem : Problem Symbol) : Prop :=
  ∀ obligation ∈ problem.obligations, ObligationInScope (fun name => name ∈ problem.domains.map Prod.fst) obligation

/-- Successful executable renaming introduces only names from its supplied map. -/
theorem rename_scope (names : List (Nat × Nat)) (fuel : Nat) :
    (∀ fragment output, rename (Symbol := Symbol) names fuel fragment = .ok output →
      InScope (fun name => name ∈ names.map Prod.snd) output) ∧
    (∀ children output, renameMany (Symbol := Symbol) names fuel children = .ok output →
      ∀ name, occursMany name output = true → name ∈ names.map Prod.snd) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro children output success
        cases children with
        | nil => cases success; intro name impossible; cases impossible
        | cons first rest => cases success
  | succ fuel ih =>
      constructor
      · intro fragment output success
        cases fragment with
        | var name =>
            cases found : lookup names name with
            | none => simp only [rename, found] at success; cases success
            | some new =>
                simp only [rename, found] at success
                cases success
                intro variableName occurrence
                have same : variableName = new := by simpa only [occurs, beq_iff_eq] using occurrence
                subst variableName
                exact List.mem_map.mpr ⟨(name, new), lookup_member names name new found, rfl⟩
        | constructor symbol children =>
            cases renamed : renameMany names fuel children with
            | error error => simp only [rename, renamed] at success; cases success
            | ok children' =>
                simp only [rename, renamed] at success
                cases success
                exact ih.2 children children' renamed
      · intro children output success
        cases children with
        | nil => cases success; intro name impossible; cases impossible
        | cons first rest =>
            cases headResult : rename names fuel first with
            | error error => simp only [renameMany, headResult] at success; cases success
            | ok first' =>
                cases tailResult : renameMany names fuel rest with
                | error error => simp only [renameMany, headResult, tailResult] at success; cases success
                | ok rest' =>
                    simp only [renameMany, headResult, tailResult] at success
                    cases success
                    intro name occurrence
                    have either : occurs name first' = true ∨ occursMany name rest' = true := by
                      simpa only [occursMany, Bool.or_eq_true] using occurrence
                    rcases either with head | tail
                    · exact ih.1 first first' headResult name head
                    · exact ih.2 rest rest' tailResult name tail

/-- A normalized target mentions only mapped live-domain names. -/
theorem normalizeTarget_scope (fuel : Nat) (problem : Problem Symbol) (names : List (Nat × Nat))
    (target output : Symbolic.Target Symbol) (success : normalizeTarget fuel problem names target = .ok (some output)) :
    InScope (fun name => name ∈ names.map Prod.snd) output.fragment := by
  unfold normalizeTarget at success
  cases followed : follow problem.bindings fuel target.fragment target.path with
  | error error => simp only [followed] at success; cases success
  | ok result =>
      simp only [followed] at success
      cases result with
      | none => cases success
      | some reached =>
          change Except.bind (rename names fuel reached.fragment)
            (fun fragment => .ok (some ⟨fragment, reached.path⟩)) = .ok (some output) at success
          cases renamed : rename names fuel reached.fragment with
          | error error => simp only [renamed] at success; cases success
          | ok fragment =>
              simp only [renamed] at success
              cases success
              exact (rename_scope names fuel).1 reached.fragment fragment renamed

/-- A remaining existence requirement has the same variable scope as its target. -/
theorem required_scope (allowed : Nat → Prop) (target : Symbolic.Target Symbol)
    (within : InScope allowed target.fragment) :
    ∀ obligation ∈ required target, ObligationInScope allowed obligation := by
  unfold required
  split
  · simp
  · intro obligation member
    have same : obligation = .exists target := by simpa only [List.mem_singleton] using member
    subst obligation
    exact within

/-- Every successful normalized requirement uses only the compact domain names. -/
theorem normalizeObligation_scope [DecidableEq Symbol] [Ord Symbol] (fuel : Nat)
    (problem : Problem Symbol) (names : List (Nat × Nat)) (obligation : Obligation Symbol)
    (output : List (Obligation Symbol))
    (success : normalizeObligation fuel problem names obligation = .ok (some output)) :
    ∀ requirement ∈ output, ObligationInScope (fun name => name ∈ names.map Prod.snd) requirement := by
  cases obligation with
  | «exists» target =>
      cases normalized : normalizeTarget fuel problem names target with
      | error error => simp only [normalizeObligation, normalized] at success; cases success
      | ok result =>
          simp only [normalizeObligation, normalized] at success
          cases result with
          | none => cases success
          | some target' =>
              cases success
              exact required_scope _ target' (normalizeTarget_scope fuel problem names target target' normalized)
  | equal left right =>
      cases normalizedLeft : normalizeTarget fuel problem names left with
      | error error => simp only [normalizeObligation, normalizedLeft] at success; cases success
      | ok leftResult =>
          cases normalizedRight : normalizeTarget fuel problem names right with
          | error error => simp only [normalizeObligation, normalizedLeft, normalizedRight] at success; cases success
          | ok rightResult =>
              simp only [normalizeObligation, normalizedLeft, normalizedRight] at success
              cases leftResult with
              | none => cases success
              | some first =>
                  cases rightResult with
                  | none => cases success
                  | some second =>
                      have firstScoped := normalizeTarget_scope fuel problem names left first normalizedLeft
                      have secondScoped := normalizeTarget_scope fuel problem names right second normalizedRight
                      change (if targetEq first second then Except.ok (some (required first))
                        else if compareTarget first second == .gt then Except.ok (some [.equal second first])
                        else Except.ok (some [.equal first second])) = (Except.ok (some output) : Except Error _) at success
                      split at success
                      · cases success; exact required_scope _ first firstScoped
                      · split at success
                        · cases success
                          simpa only [List.forall_mem_singleton, ObligationInScope] using And.intro secondScoped firstScoped
                        · cases success
                          simpa only [List.forall_mem_singleton, ObligationInScope] using And.intro firstScoped secondScoped

/-- A pointwise traversal property holds for every returned list member. -/
theorem all₂_right_forall (relation : Input → Output → Prop) (property : Output → Prop)
    (inputs : List Input) (outputs : List Output) (related : All₂ relation inputs outputs)
    (holds : ∀ input output, relation input output → property output) : ∀ output ∈ outputs, property output := by
  induction related with
  | nil => simp
  | cons head tail ih => simp only [List.forall_mem_cons]; exact ⟨holds _ _ head, ih⟩

/-- The complete normalizer establishes the live-variable scope needed by fresh expansion. -/
theorem normalize_scoped [DecidableEq Symbol] [Ord Symbol] (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) : ProblemScoped normalized := by
  let names := problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)
  have nameRange : names.map Prod.snd = normalized.domains.map Prod.fst := by
    rw [normalize_domain_names fuel problem normalized success]
    simpa only [names, List.map_map, Function.comp_def] using List.zipIdx_map_snd 0 problem.domains
  cases outputs : problem.obligations.mapM (normalizeObligation fuel problem names) with
  | error error => dsimp only [names] at outputs; simp only [normalize, outputs] at success; cases success
  | ok pending =>
      have related := mapM_success_all₂ (normalizeObligation fuel problem names) problem.obligations pending outputs
      have allScoped : ∀ result ∈ pending, ∀ requirement ∈ result.getD [],
          ObligationInScope (fun name => name ∈ names.map Prod.snd) requirement := by
        refine all₂_right_forall _ (fun result => ∀ requirement ∈ result.getD [],
          ObligationInScope (fun name => name ∈ names.map Prod.snd) requirement) _ _ related ?_
        intro obligation result succeeds requirement present
        cases result with
        | none => cases present
        | some requirements => exact normalizeObligation_scope fuel problem names obligation requirements succeeds requirement present
      dsimp only [names] at outputs
      simp only [normalize, outputs] at success
      change (if pending.any Option.isNone then Except.ok none else
        Except.ok (some ⟨problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)), [],
          problem.domains.length, (uniqueBy obligationEq (pending.flatMap fun entry => entry.getD [])).mergeSort
            (fun left right => compareObligation left right != .gt)⟩)) = (Except.ok (some normalized) : Except Error _) at success
      split at success
      · cases success
      · cases success
        intro requirement member
        have flattened : requirement ∈ pending.flatMap (fun entry => entry.getD []) := by
          simpa only [List.mem_mergeSort, mem_uniqueBy obligationEq obligationEq_correct] using member
        obtain ⟨entry, entryMember, requirementMember⟩ := List.mem_flatMap.mp flattened
        simpa only [nameRange] using allScoped entry entryMember requirement requirementMember

/-- Agreement on every occurring variable preserves context instantiation. -/
theorem instantiate_congr_occurs (left right : Nat → Term Symbol) (fragment : Fragment Symbol)
    (agree : ∀ name, occurs name fragment = true → left name = right name) :
    instantiate left fragment = instantiate right fragment := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => (∀ name, occursMany name children = true → left name = right name) →
      instantiateMany left children = instantiateMany right children) with
  | var name => exact agree name (by simp [occurs])
  | constructor symbol children ih => exact congrArg (Term.node symbol) (ih agree)
  | nil _ => rfl
  | cons first rest ihfirst ihrest agreement =>
      have firstSame := ihfirst (fun name occurrence => agreement name (by simp [occursMany, occurrence]))
      have restSame := ihrest (fun name occurrence => agreement name (by simp [occursMany, occurrence]))
      simp only [instantiateMany, firstSame, restSame]

/-- Fresh-name changes cannot alter a scoped pending requirement. -/
theorem obligation_scoped_congr (allowed : Nat → Prop) (left right : Nat → Term Symbol)
    (agree : ∀ name, allowed name → left name = right name) (obligation : Obligation Symbol)
    (within : ObligationInScope allowed obligation) : Satisfies left obligation ↔ Satisfies right obligation := by
  cases obligation with
  | «exists» target =>
      simp only [Satisfies, Symbolic.targetValue,
        instantiate_congr_occurs left right target.fragment (fun name occurrence => agree name (within name occurrence))]
  | equal first second =>
      simp only [Satisfies, Symbolic.targetValue,
        instantiate_congr_occurs left right first.fragment (fun name occurrence => agree name (within.1 name occurrence)),
        instantiate_congr_occurs left right second.fragment (fun name occurrence => agree name (within.2 name occurrence))]

end MicroCFTA.SymbolicDriver
