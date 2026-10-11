import MicroCFTA.SymbolicDriver

/-!
# Semantic preservation by the executable symbolic normalizer

These proofs use the actual binding follower and renamer from SymbolicDriver.
Fuel exhaustion remains an error. Successful normalization preserves the
meaning of pending equality and existence requirements.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Target Obligation instantiate instantiateMany targetValue Satisfies)

/-- An assignment respects every substitution stored in the live problem. -/
def BindingsHold (assignment : Nat → Term Symbol) (bindings : List (Nat × Fragment Symbol)) : Prop :=
  ∀ entry ∈ bindings, assignment entry.1 = instantiate assignment entry.2

/-- A successful lookup returns an entry from the finite map. -/
theorem lookup_member (entries : List (Nat × Value)) (key : Nat) (value : Value)
    (found : lookup entries key = some value) : (key, value) ∈ entries := by
  unfold lookup at found
  cases selected : entries.find? (fun entry => entry.1 == key) with
  | none => simp [selected] at found
  | some entry =>
      have member := List.mem_of_find?_eq_some selected
      have keySame := List.find?_some selected
      simp only [beq_iff_eq] at keySame
      simp only [selected, Option.map_some, Option.some.injEq] at found
      have same : entry = (key, value) := Prod.ext keySame found
      simpa only [same] using member

/-- Successful binding inlining preserves the instantiated context and its ordered children. -/
theorem inline_semantics (assignment : Nat → Term Symbol) (bindings : List (Nat × Fragment Symbol))
    (holds : BindingsHold assignment bindings) (fuel : Nat) :
    (∀ fragment output, inline bindings fuel fragment = .ok output →
      instantiate assignment fragment = instantiate assignment output) ∧
    (∀ fragments output, inlineMany bindings fuel fragments = .ok output →
      instantiateMany assignment fragments = instantiateMany assignment output) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output success
        cases success
      · intro fragments output success
        cases fragments with
        | nil => cases success; rfl
        | cons first rest => cases success
  | succ fuel ih =>
      constructor
      · intro fragment output success
        cases fragment with
        | var name =>
            cases found : lookup bindings name with
            | none => simp only [inline, found] at success; cases success; rfl
            | some replacement =>
                simp only [inline, found] at success
                exact (holds (name, replacement) (lookup_member bindings name replacement found)).trans
                  (ih.1 replacement output success)
        | constructor symbol children =>
            cases result : inlineMany bindings fuel children with
            | error error => simp only [inline, result] at success; cases success
            | ok children' =>
                simp only [inline, result] at success
                cases success
                exact congrArg (Term.node symbol) (ih.2 children children' result)
      · intro fragments output success
        cases fragments with
        | nil => cases success; rfl
        | cons first rest =>
            cases headResult : inline bindings fuel first with
            | error error => simp only [inlineMany, headResult] at success; cases success
            | ok first' =>
                cases tailResult : inlineMany bindings fuel rest with
                | error error => simp only [inlineMany, headResult, tailResult] at success; cases success
                | ok rest' =>
                    simp only [inlineMany, headResult, tailResult] at success
                    cases success
                    simp only [instantiateMany, ih.1 first first' headResult, ih.2 rest rest' tailResult]

/-- A followed target denotes the original selected subtree, including a missing path. -/
theorem follow_semantics (assignment : Nat → Term Symbol) (bindings : List (Nat × Fragment Symbol))
    (holds : BindingsHold assignment bindings) (fuel : Nat) (fragment : Fragment Symbol)
    (path : List Nat) (output : Option (Target Symbol))
    (success : follow bindings fuel fragment path = .ok output) :
    (instantiate assignment fragment).atPath path = output.bind (targetValue assignment) := by
  induction fuel generalizing fragment path output with
  | zero => cases success
  | succ fuel ih =>
      cases fragment with
      | var name =>
          cases found : lookup bindings name with
          | none => simp only [follow, found] at success; cases success; rfl
          | some replacement =>
              simp only [follow, found] at success
              simpa only [instantiate, holds (name, replacement) (lookup_member bindings name replacement found)]
                using ih replacement path output success
      | constructor symbol children =>
          cases path with
          | nil =>
              cases inlined : inline bindings fuel (.constructor symbol children) with
              | error error => simp only [follow, inlined] at success; cases success
              | ok fragment' =>
                  simp only [follow, inlined] at success
                  cases success
                  simpa only [Term.atPath, Option.bind_some, targetValue] using
                    congrArg some ((inline_semantics assignment bindings holds fuel).1 _ _ inlined)
          | cons index rest =>
              cases child : children[index]? with
              | none =>
                  simp only [follow, child] at success
                  cases success
                  simp [instantiate, Term.atPath, Symbolic.instantiateMany_lookup, child]
              | some nested =>
                  simp only [follow, child] at success
                  simpa [instantiate, Term.atPath, Symbolic.instantiateMany_lookup, child] using
                    ih nested rest output success

/-- Old and compact variable names denote the same assigned term. -/
def NamesAgree (old compact : Nat → Term Symbol) (names : List (Nat × Nat)) : Prop :=
  ∀ before after, lookup names before = some after → old before = compact after

/-- The executable compact renamer preserves every successful context interpretation. -/
theorem rename_semantics (old compact : Nat → Term Symbol) (names : List (Nat × Nat))
    (agree : NamesAgree old compact names) (fuel : Nat) :
    (∀ fragment output, rename names fuel fragment = .ok output →
      instantiate old fragment = instantiate compact output) ∧
    (∀ fragments output, renameMany names fuel fragments = .ok output →
      instantiateMany old fragments = instantiateMany compact output) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro fragments output success
        cases fragments with
        | nil => cases success; rfl
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
                exact agree name new found
        | constructor symbol children =>
            cases result : renameMany names fuel children with
            | error error => simp only [rename, result] at success; cases success
            | ok children' =>
                simp only [rename, result] at success
                cases success
                exact congrArg (Term.node symbol) (ih.2 children children' result)
      · intro fragments output success
        cases fragments with
        | nil => cases success; rfl
        | cons first rest =>
            cases headResult : rename names fuel first with
            | error error => simp only [renameMany, headResult] at success; cases success
            | ok first' =>
                cases tailResult : renameMany names fuel rest with
                | error error => simp only [renameMany, headResult, tailResult] at success; cases success
                | ok rest' =>
                    simp only [renameMany, headResult, tailResult] at success
                    cases success
                    simp only [instantiateMany, ih.1 first first' headResult, ih.2 rest rest' tailResult]

/-- Following substitutions and renaming preserve a selected target's exact optional value. -/
theorem normalizeTarget_semantics (old compact : Nat → Term Symbol) (problem : Problem Symbol)
    (names : List (Nat × Nat)) (holds : BindingsHold old problem.bindings)
    (agree : NamesAgree old compact names) (fuel : Nat) (target : Target Symbol)
    (output : Option (Target Symbol)) (success : normalizeTarget fuel problem names target = .ok output) :
    targetValue old target = output.bind (targetValue compact) := by
  unfold normalizeTarget at success
  cases followed : follow problem.bindings fuel target.fragment target.path with
  | error error => simp only [followed] at success; cases success
  | ok result =>
      simp only [followed] at success
      have value := follow_semantics old problem.bindings holds fuel target.fragment target.path result followed
      cases result with
      | none => cases success; exact value
      | some reached =>
          change Except.bind (rename names fuel reached.fragment)
            (fun fragment => .ok (some ⟨fragment, reached.path⟩)) = .ok output at success
          cases renamed : rename names fuel reached.fragment with
          | error error => simp only [renamed] at success; cases success
          | ok fragment =>
              simp only [renamed] at success
              cases success
              unfold targetValue
              rw [value]
              simp only [Option.bind_some, targetValue,
                (rename_semantics old compact names agree fuel).1 reached.fragment fragment renamed]

/-- A failed path is false. A normalized list denotes the conjunction of its obligations. -/
def ObligationResultHolds (assignment : Nat → Term Symbol) : Option (List (Obligation Symbol)) → Prop
  | none => False
  | some obligations => ∀ obligation ∈ obligations, Satisfies assignment obligation

/-- Removing an empty-path existence test does not change its truth. -/
theorem required_semantics (assignment : Nat → Term Symbol) (target : Target Symbol) :
    (∀ obligation ∈ required target, Satisfies assignment obligation) ↔
      Satisfies assignment (.exists target) := by
  rcases target with ⟨fragment, path⟩
  cases path <;> simp [required, Satisfies, targetValue, Term.atPath]

/-- The actual normalizer preserves each equality, including missing self-equality paths. -/
theorem normalizeObligation_semantics [DecidableEq Symbol] [Ord Symbol]
    (old compact : Nat → Term Symbol) (problem : Problem Symbol) (names : List (Nat × Nat))
    (holds : BindingsHold old problem.bindings) (agree : NamesAgree old compact names)
    (fuel : Nat) (obligation : Obligation Symbol) (output : Option (List (Obligation Symbol)))
    (success : normalizeObligation fuel problem names obligation = .ok output) :
    Satisfies old obligation ↔ ObligationResultHolds compact output := by
  cases obligation with
  | «exists» target =>
      cases normalized : normalizeTarget fuel problem names target with
      | error error => simp only [normalizeObligation, normalized] at success; cases success
      | ok result =>
          simp only [normalizeObligation, normalized] at success
          have value := normalizeTarget_semantics old compact problem names holds agree fuel target result normalized
          cases result with
          | none => cases success; simp [Satisfies, ObligationResultHolds, value]
          | some target' =>
              cases success
              simp only [Option.map_some, ObligationResultHolds]
              rw [required_semantics]
              simp only [Satisfies, value, Option.bind_some]
  | equal left right =>
      cases normalizedLeft : normalizeTarget fuel problem names left with
      | error error => simp only [normalizeObligation, normalizedLeft] at success; cases success
      | ok leftResult =>
          cases normalizedRight : normalizeTarget fuel problem names right with
          | error error =>
              simp only [normalizeObligation, normalizedLeft, normalizedRight] at success
              cases success
          | ok rightResult =>
              have leftValue := normalizeTarget_semantics old compact problem names holds agree fuel left leftResult normalizedLeft
              have rightValue := normalizeTarget_semantics old compact problem names holds agree fuel right rightResult normalizedRight
              simp only [normalizeObligation, normalizedLeft, normalizedRight] at success
              cases leftResult with
              | none => cases success; simp [Satisfies, ObligationResultHolds, leftValue]
              | some first =>
                  cases rightResult with
                  | none => cases success; simp [Satisfies, ObligationResultHolds, rightValue]
                  | some second =>
                      change (if targetEq first second then Except.ok (some (required first))
                        else if compareTarget first second == .gt then Except.ok (some [.equal second first])
                        else Except.ok (some [.equal first second])) = (Except.ok output : Except Error _) at success
                      split at success
                      · rename_i same
                        have identical := (targetEq_correct first second).mp same
                        subst second
                        cases success
                        simp only [ObligationResultHolds]
                        rw [required_semantics]
                        simp only [Satisfies, leftValue, rightValue, Option.bind_some, and_self]
                      · split at success <;> cases success <;>
                          simp [ObligationResultHolds, Satisfies, leftValue, rightValue, and_comm]

/-- Executable obligation deduplication preserves membership. -/
theorem mem_uniqueBy (same : Value → Value → Bool)
    (correct : ∀ left right, same left right = true ↔ left = right)
    (value : Value) (values : List Value) : value ∈ uniqueBy same values ↔ value ∈ values := by
  cases values with
  | nil => simp [uniqueBy]
  | cons first rest =>
      simp only [uniqueBy, List.mem_cons]
      rw [mem_uniqueBy same correct value (rest.filter fun other => !same first other)]
      by_cases equal : first = value
      · simp [equal]
      · have different : same first value = false := by
          cases result : same first value
          · rfl
          · exact False.elim (equal ((correct first value).mp result))
        simp [List.mem_filter, different, Ne.symm equal]
termination_by values.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- A successful exception traversal records one successful result for each input. -/
theorem mapM_success_all₂ (action : Input → Except Failure Output) (inputs : List Input)
    (outputs : List Output) (success : inputs.mapM action = .ok outputs) :
    All₂ (fun input output => action input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases success; exact .nil
  | cons first rest ih =>
      cases headResult : action first with
      | error error => simp only [List.mapM_cons, headResult] at success; cases success
      | ok head =>
          cases tailResult : rest.mapM action with
          | error error => simp only [List.mapM_cons, headResult, tailResult] at success; cases success
          | ok tail =>
              simp only [List.mapM_cons, headResult, tailResult] at success
              cases success
              exact .cons headResult (ih tail tailResult)

/-- Pointwise equivalence preserves the conjunction over two ordered lists. -/
theorem all₂_forall_iff (left : Input → Prop) (right : Output → Prop)
    (inputs : List Input) (outputs : List Output)
    (related : All₂ (fun input output => left input ↔ right output) inputs outputs) :
    (∀ input ∈ inputs, left input) ↔ (∀ output ∈ outputs, right output) := by
  induction related with
  | nil => simp
  | cons head tail ih => simp only [List.forall_mem_cons, head, ih]

/-- Flatten successful normalized obligations without discarding a failed position. -/
theorem pending_semantics (assignment : Nat → Term Symbol)
    (pending : List (Option (List (Obligation Symbol)))) (present : none ∉ pending) :
    (∀ entry ∈ pending, ObligationResultHolds assignment entry) ↔
      ∀ obligation ∈ pending.flatMap (fun entry => entry.getD []), Satisfies assignment obligation := by
  induction pending with
  | nil => simp
  | cons entry rest ih =>
      have tail : none ∉ rest := fun member => present (by simp [member])
      cases entry with
      | none => exact False.elim (present (by simp))
      | some obligations =>
          simp only [List.forall_mem_cons, List.flatMap_cons, Option.getD_some, List.forall_mem_append]
          exact and_congr Iff.rfl (ih tail)

/-- The semantic result of normalization concerns every pending obligation. -/
def NormalizedHolds (assignment : Nat → Term Symbol) : Option (Problem Symbol) → Prop
  | none => False
  | some problem => ∀ obligation ∈ problem.obligations, Satisfies assignment obligation

/-- The complete executable normalizer preserves all constraints under the compact naming map. -/
theorem normalize_semantics [DecidableEq Symbol] [Ord Symbol]
    (old compact : Nat → Term Symbol) (problem : Problem Symbol)
    (holds : BindingsHold old problem.bindings)
    (agree : NamesAgree old compact (problem.domains.zipIdx.map fun (entry, new) => (entry.1, new)))
    (fuel : Nat) (output : Option (Problem Symbol))
    (success : normalize fuel problem = .ok output) :
    (∀ obligation ∈ problem.obligations, Satisfies old obligation) ↔ NormalizedHolds compact output := by
  let names := problem.domains.zipIdx.map fun (entry, new) => (entry.1, new)
  cases results : problem.obligations.mapM (normalizeObligation fuel problem names) with
  | error error =>
      dsimp only [names] at results
      simp only [normalize, results] at success
      cases success
  | ok pending =>
      dsimp only [names] at results
      have related := mapM_success_all₂ (normalizeObligation fuel problem names) problem.obligations pending results
      have semantics := all₂_forall_iff (Satisfies old) (ObligationResultHolds compact)
        problem.obligations pending
        (related.imp fun obligation normalized success =>
          normalizeObligation_semantics old compact problem names holds agree fuel obligation normalized success)
      simp only [normalize, results] at success
      change (if pending.any Option.isNone then Except.ok none else
        Except.ok (some ⟨problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)), [],
          problem.domains.length, (uniqueBy obligationEq (pending.flatMap fun entry => entry.getD [])).mergeSort
            (fun left right => compareObligation left right != .gt)⟩)) = (Except.ok output : Except Error _) at success
      split at success
      · rename_i missing
        cases success
        obtain ⟨entry, member, absent⟩ := List.any_eq_true.mp missing
        cases entry with
        | some obligations => cases absent
        | none =>
            exact ⟨fun constraints => semantics.mp constraints none member, False.elim⟩
      · rename_i noMissing
        cases success
        have present : none ∉ pending := fun member =>
          noMissing (List.any_eq_true.mpr ⟨none, member, rfl⟩)
        rw [semantics, pending_semantics compact pending present]
        simp only [NormalizedHolds, List.mem_mergeSort, mem_uniqueBy obligationEq obligationEq_correct]

/-- Normalization retains every live graph domain and resets only names, bindings, and the fresh supply. -/
theorem normalize_shape [DecidableEq Symbol] [Ord Symbol] (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    normalized.domains = problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)) ∧
    normalized.bindings = [] ∧ normalized.nextVariable = problem.domains.length := by
  unfold normalize at success
  cases results : problem.obligations.mapM
      (normalizeObligation fuel problem (problem.domains.zipIdx.map fun (entry, new) => (entry.1, new))) with
  | error error => simp only [results] at success; cases success
  | ok pending =>
      simp only [results] at success
      change (if pending.any Option.isNone then Except.ok none else
        Except.ok (some ⟨problem.domains.zipIdx.map (fun (entry, new) => (new, entry.2)), [],
          problem.domains.length, (uniqueBy obligationEq (pending.flatMap fun entry => entry.getD [])).mergeSort
            (fun left right => compareObligation left right != .gt)⟩)) =
        (Except.ok (some normalized) : Except Error _) at success
      split at success
      · cases success
      · cases success; exact ⟨rfl, rfl, rfl⟩

/-- No independent variable domain disappears merely because no remaining constraint mentions it. -/
theorem normalize_preserves_domain_count [DecidableEq Symbol] [Ord Symbol]
    (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    normalized.domains.length = problem.domains.length := by
  rw [(normalize_shape fuel problem normalized success).1]
  simp

/-- Every graph-domain identity remains in the same position after normalization. -/
theorem normalize_preserves_graph_domains [DecidableEq Symbol] [Ord Symbol]
    (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    normalized.domains.map Prod.snd = problem.domains.map Prod.snd := by
  rw [(normalize_shape fuel problem normalized success).1]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map Prod.snd) (List.zipIdx_map_fst 0 problem.domains)

/-- Compact names are exactly the finite range reserved by the next-variable supply. -/
theorem normalize_domain_names [DecidableEq Symbol] [Ord Symbol]
    (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    normalized.domains.map Prod.fst = List.range' 0 problem.domains.length := by
  rw [(normalize_shape fuel problem normalized success).1]
  simpa only [List.map_map, Function.comp_def] using List.zipIdx_map_snd 0 problem.domains

/-- A normalized context has distinct live names and a fresh next-variable supply. -/
theorem normalize_fresh [DecidableEq Symbol] [Ord Symbol]
    (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    (normalized.domains.map Prod.fst).Nodup ∧
      ∀ entry ∈ normalized.domains, entry.1 < normalized.nextVariable := by
  have names := normalize_domain_names fuel problem normalized success
  constructor
  · rw [names]; exact List.nodup_range'
  · intro entry member
    have present : entry.1 ∈ normalized.domains.map Prod.fst := List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [names] at present
    rw [(normalize_shape fuel problem normalized success).2.2]
    obtain ⟨offset, bound, equal⟩ := List.mem_range'.mp present
    omega

/-- The executable occurrence test bounds the assigned variable's height by its enclosing context. -/
theorem occurs_height (assignment : Nat → Term Symbol) (name : Nat) (fragment : Fragment Symbol) :
    occurs name fragment = true → (assignment name).height ≤ (instantiate assignment fragment).height := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => occursMany name children = true →
      (assignment name).height ≤ forestHeight (instantiateMany assignment children)) with
  | var other =>
      intro occurrence
      have equal : name = other := by simpa [occurs] using occurrence
      simp only [instantiate, equal, Nat.le_refl]
  | constructor symbol children ih =>
      intro occurrence
      have bound := ih occurrence
      simp only [instantiate, Term.height, forestHeight] at bound ⊢
      exact Nat.le_trans bound (Nat.le_add_right _ 1)
  | nil occurrence => cases occurrence
  | cons first rest ihfirst ihrest occurrence =>
      have either : occurs name first = true ∨ occursMany name rest = true := by
        simpa only [occursMany, Bool.or_eq_true] using occurrence
      rcases either with head | tail
      · exact Nat.le_trans (ihfirst head) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihrest tail) (Nat.le_max_right _ _)

/-- The actual occurs check cannot reject a satisfiable finite variable-constructor equality. -/
theorem occurs_constructor_reject (assignment : Nat → Term Symbol) (name : Nat)
    (symbol : Symbol) (children : List (Fragment Symbol))
    (occurrence : occurs name (.constructor symbol children) = true) :
    assignment name ≠ instantiate assignment (.constructor symbol children) := by
  have childBound : (assignment name).height ≤ forestHeight (instantiateMany assignment children) := by
    induction children with
    | nil => cases occurrence
    | cons first rest ih =>
        have either : occurs name first = true ∨ occursMany name rest = true := by
          simpa only [occurs, occursMany, Bool.or_eq_true] using occurrence
        rcases either with head | tail
        · exact Nat.le_trans (occurs_height assignment name first head) (Nat.le_max_left _ _)
        · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)
  intro same
  rw [same] at childBound
  simp only [instantiate, Term.height, forestHeight] at childBound
  omega

/-- Decomposing matching constructors into child equalities preserves the complete requirement. -/
theorem constructor_obligations_semantics (assignment : Nat → Term Symbol)
    (symbol : Symbol) (children others : List (Fragment Symbol))
    (arity : children.length = others.length) :
    instantiate assignment (.constructor symbol children) = instantiate assignment (.constructor symbol others) ↔
      ∀ obligation ∈ List.zipWith (fun left right => Obligation.equal ⟨left, []⟩ ⟨right, []⟩) children others,
        Satisfies assignment obligation := by
  simp only [instantiate, Term.node.injEq, true_and]
  induction children generalizing others with
  | nil =>
      have empty : others = [] := by simpa using arity.symm
      subst others
      simp [instantiateMany]
  | cons first rest ih =>
      cases others with
      | nil => simp at arity
      | cons other tail =>
          have tailArity : rest.length = tail.length := by simpa using arity
          simp [instantiateMany, Satisfies, targetValue, Term.atPath, ih tail tailArity, eq_comm]

/-- Compact valuations agree with the original valuation at every live domain position. -/
def CompactAgreement (old compact : Nat → Term Symbol) (domains : List (Nat × Nat)) : Prop :=
  ∀ entry index, (entry, index) ∈ domains.zipIdx → old entry.1 = compact index

/-- Agreement on all indexed domains supplies the actual renamer's lookup contract. -/
theorem compact_names_agree (old compact : Nat → Term Symbol) (domains : List (Nat × Nat))
    (agree : CompactAgreement old compact domains) :
    NamesAgree old compact (domains.zipIdx.map fun (entry, new) => (entry.1, new)) := by
  intro before after found
  obtain ⟨⟨entry, index⟩, member, equal⟩ := List.mem_map.mp (lookup_member _ before after found)
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨rfl, rfl⟩
  exact agree entry index member

/-- Domain tests use an independent semantic graph language. -/
def DomainsHold (language : Nat → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (domains : List (Nat × Nat)) : Prop :=
  ∀ entry ∈ domains, language entry.2 (assignment entry.1)

/-- Compact renaming preserves every live graph-language requirement. -/
theorem domain_renaming_semantics (language : Nat → Term Symbol → Prop)
    (old compact : Nat → Term Symbol) (domains : List (Nat × Nat))
    (agree : CompactAgreement old compact domains) :
    DomainsHold language old domains ↔
      DomainsHold language compact (domains.zipIdx.map fun (entry, new) => (new, entry.2)) := by
  constructor
  · intro holds entry member
    obtain ⟨⟨original, index⟩, indexed, same⟩ := List.mem_map.mp member
    subst entry
    rw [← agree original index indexed]
    apply holds original
    have member : original ∈ domains.zipIdx.map Prod.fst := List.mem_map.mpr ⟨(original, index), indexed, rfl⟩
    simpa only [List.zipIdx_map_fst] using member
  · intro holds entry member
    have indexedMember : entry ∈ domains.zipIdx.map Prod.fst := by simpa using member
    obtain ⟨⟨original, index⟩, indexed, same⟩ := List.mem_map.mp indexedMember
    subst entry
    rw [agree original index indexed]
    exact holds (index, original.2) (List.mem_map.mpr ⟨(original, index), indexed, rfl⟩)

/-- A live symbolic problem denotes assignments satisfying domains, bindings, and obligations. -/
def ProblemHolds (language : Nat → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (problem : Problem Symbol) : Prop :=
  DomainsHold language assignment problem.domains ∧ BindingsHold assignment problem.bindings ∧
    ∀ obligation ∈ problem.obligations, Satisfies assignment obligation

/-- The full source normalizer preserves symbolic solutions under compact variable renaming. -/
theorem normalize_solution_iff [DecidableEq Symbol] [Ord Symbol]
    (language : Nat → Term Symbol → Prop) (old compact : Nat → Term Symbol)
    (problem normalized : Problem Symbol) (bindings : BindingsHold old problem.bindings)
    (agreement : CompactAgreement old compact problem.domains) (fuel : Nat)
    (success : normalize fuel problem = .ok (some normalized)) :
    ProblemHolds language old problem ↔ ProblemHolds language compact normalized := by
  have shape := normalize_shape fuel problem normalized success
  have constraints := normalize_semantics old compact problem bindings
    (compact_names_agree old compact problem.domains agreement) fuel (some normalized) success
  have domains := domain_renaming_semantics language old compact problem.domains agreement
  constructor
  · rintro ⟨oldDomains, _, oldConstraints⟩
    refine ⟨?_, ?_, constraints.mp oldConstraints⟩
    · rw [shape.1]; exact domains.mp oldDomains
    · simp [BindingsHold, shape.2.1]
  · rintro ⟨newDomains, _, newConstraints⟩
    refine ⟨?_, bindings, constraints.mpr newConstraints⟩
    rw [shape.1] at newDomains
    exact domains.mpr newDomains

/-- Returning no normalized problem proves that the old constraints have no satisfying assignment. -/
theorem normalize_none_rejects [DecidableEq Symbol] [Ord Symbol]
    (language : Nat → Term Symbol → Prop) (old compact : Nat → Term Symbol)
    (problem : Problem Symbol) (bindings : BindingsHold old problem.bindings)
    (agreement : CompactAgreement old compact problem.domains) (fuel : Nat)
    (success : normalize fuel problem = .ok none) : ¬ ProblemHolds language old problem := by
  intro solution
  exact (normalize_semantics old compact problem bindings
    (compact_names_agree old compact problem.domains agreement) fuel none success).mp solution.2.2

end MicroCFTA.SymbolicDriver
