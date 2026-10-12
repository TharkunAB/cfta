import MicroCFTA.RecursiveCheckedRanks
import MicroCFTA.SourcePlanPartition

/-!
# Finite queries of arbitrary recursive callback bodies

The callback follows `staticTerms`, `productTerms`, `choiceTerms`,
`labelRecursive`, `payRecursive`, and `tiedPositions`. It reads the requested
view. It does not enumerate a class. The private recursion node makes every
return to the body consume one term node, including labelled and spine views.

Finite leaves supply their existing callbacks and size counts. True flags
correspond exactly to finite forward rank derivations. The source count
equation also gives bounds for unchecked rows. Every callback preserves the
source order. The static producer proofs establish the finite leaf laws.
-/
namespace MicroCFTA.RecursiveCallbackTermination
open Language GeneratorCombinators IntegerTermViews SizedRank

abbrev EngineTerm (Symbol : Type) := Term (Label Symbol)
abbrev Checked := RecursiveCheckedRanks.Checked
abbrev Callback (Symbol : Type) := View → List (EngineTerm Symbol) → List Checked

/-- A finite source retains its own size counts and checked callback. -/
structure Finite (Symbol : Type) where
  counts : Nat → Nat
  select : Position → Option (EngineTerm Symbol)
  positions : Callback Symbol

/-- The term operations of one recursive source body. -/
inductive Recipe (Symbol : Type) where
  | finite (source : Finite Symbol)
  | occurrence
  | map (inner : Recipe Symbol)
  | pay (inner : Recipe Symbol)
  | choice (left right : Recipe Symbol)
  | ap (functions arguments : Recipe Symbol)
  | label (symbol : Symbol) (inner : Recipe Symbol)

/-- Count each class with the same source sum and convolution. -/
def counts (self : Nat → Nat) : Recipe Symbol → Nat → Nat
  | .finite source => source.counts
  | .occurrence => self
  | .map inner => counts self inner
  | .pay inner | .label _ inner => fun size => match size with
      | 0 => 0
      | size + 1 => counts self inner size
  | .choice left right => fun size => counts self left size + counts self right size
  | .ap left right => fun size =>
      ((List.range (size + 1)).map fun split => counts self left split * counts self right (size - split)).sum

/-- Compare the source's size, class rank, and checked flag in that order. -/
def before (first second : Checked) : Bool :=
  decide (first.1.size < second.1.size ∨
    (first.1.size = second.1.size ∧ (first.1.rank < second.1.rank ∨
      (first.1.rank = second.1.rank ∧ (first.2 = false ∨ second.2 = true)))))

/-- Source products and choices sort their complete checked rows. -/
def sorted (rows : List Checked) : List Checked := rows.mergeSort before

/-- A finite syntax measure resolves calls that preserve the requested view. -/
def depth : Recipe Symbol → Nat
  | .finite _ | .occurrence => 0
  | .map inner | .pay inner | .label _ inner => depth inner + 1
  | .choice left right | .ap left right => depth left + depth right + 1

/-- Taking a subset of a forest cannot increase its maximum term height. -/
theorem forest_subset (first second : List (Term Symbol))
    (subset : ∀ term ∈ first, term ∈ second) : forestHeight first ≤ forestHeight second := by
  induction first with
  | nil => simp [forestHeight]
  | cons term rest ih =>
      simp only [forestHeight, List.foldr_cons, Nat.max_le]
      exact ⟨height_le_forestHeight second term (subset term (by simp)),
        ih (fun child member => subset child (by simp [member]))⟩

/-- The function prefix of an application view is no taller than the complete view. -/
theorem dropLast_height (terms : List (Term Symbol)) :
    forestHeight terms.dropLast ≤ forestHeight terms :=
  forest_subset _ _ (fun _ member => (List.dropLast_sublist terms).subset member)

/-- The final application argument is no taller than the complete view. -/
theorem last_height (terms : List (Term Symbol)) (term : Term Symbol)
    (found : terms.getLast? = some term) : term.height ≤ forestHeight terms :=
  height_le_forestHeight terms term (List.mem_of_getLast? found)

/-- Execute all source callback branches with one arbitrary recursive body. -/
def positions [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (recipe : Recipe Symbol) (view : View) (wanted : List (EngineTerm Symbol)) : List Checked :=
  match recipe with
  | .finite source => source.positions view wanted
  | .occurrence => match wanted with
      | [.node .recursion [child]] => positions self body body .whole [child]
      | _ => []
  | .map inner => positions self body inner view wanted
  | .pay inner => RecursiveCheckedRanks.payRows (positions self body inner view wanted)
  | .choice left right => sorted <| match view with
      | .labelled => positions self body left view wanted ++
          (positions self body right view wanted).map
            (RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1)
      | .whole | .spine => match wanted with
          | [.node (.choice 0) [child]] => positions self body left .whole [child]
          | [.node (.choice 1) [child]] => (positions self body right .whole [child]).map
              (RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1)
          | _ => []
  | .ap functions arguments => sorted <| match view with
      | .whole => match wanted with
          | [.node .apply [function, argument]] =>
              RecursiveCheckedRanks.productRows (counts self functions) (counts self arguments)
                (positions self body functions .whole [function])
                (positions self body arguments .whole [argument])
          | _ => []
      | .spine | .labelled => match _found : wanted.getLast? with
          | none => []
          | some argument => RecursiveCheckedRanks.productRows (counts self functions) (counts self arguments)
              (positions self body functions .spine wanted.dropLast)
              (positions self body arguments .whole [argument])
  | .label symbol inner => match wanted with
      | [.node (.user found) children] =>
          if found = symbol then RecursiveCheckedRanks.payRows (positions self body inner .labelled children) else []
      | _ => []
termination_by (forestHeight wanted, depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [depth, forestHeight, Term.height, List.foldr_cons, List.foldr_nil,
    Nat.max_zero]
  all_goals first
    | omega
    | have h := dropLast_height wanted; simp only [forestHeight] at h; omega
    | have h := last_height _ _ (by assumption); simp only [forestHeight] at h; omega

/-- The source knot preserves all three leaf views and consumes its private root. -/
def tied [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol) : Callback Symbol :=
  positions self body .occurrence

/-- Every view of a recursive term passes exactly its body to the body callback. -/
theorem tied_unfold [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (view : View) (term : EngineTerm Symbol) :
    tied self body view [.node .recursion [term]] = positions self body body .whole [term] := by
  simp [tied, positions]

/-- The private root is required even in a labelled or spine request. -/
theorem tied_rejects [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (view : View) (wanted : List (EngineTerm Symbol))
    (absent : ∀ term, wanted ≠ [.node .recursion [term]]) :
    tied self body view wanted = [] := by
  simp only [tied, positions]

/-- Map changes neither the callback positions nor their source checked flags. -/
theorem map_exact [DecidableEq Symbol] (self : Nat → Nat) (body inner : Recipe Symbol)
    (view : View) (wanted : List (EngineTerm Symbol)) :
    positions self body (.map inner) view wanted = positions self body inner view wanted := by
  rw [positions]

/-- Pay changes only the size field and retains the complete checked row list. -/
theorem pay_exact [DecidableEq Symbol] (self : Nat → Nat) (body inner : Recipe Symbol)
    (view : View) (wanted : List (EngineTerm Symbol)) :
    positions self body (.pay inner) view wanted =
      RecursiveCheckedRanks.payRows (positions self body inner view wanted) := by
  rw [positions]

/-- Forward rank derivations use each source constructor's position arithmetic. -/
inductive Selects (self : Nat → Nat) (body : Recipe Symbol) :
    Recipe Symbol → Position → EngineTerm Symbol → Prop where
  | finite (source : Finite Symbol) (position : Position) (term : EngineTerm Symbol)
      (selected : source.select position = some term) : Selects self body (.finite source) position term
  | occurrence (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body body position term) :
      Selects self body .occurrence position (.node .recursion [term])
  | map (inner : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body inner position term) : Selects self body (.map inner) position term
  | pay (inner : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body inner position term) :
      Selects self body (.pay inner) ⟨position.size + 1, position.rank⟩ term
  | left (left right : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body left position term) :
      Selects self body (.choice left right) position (.node (.choice 0) [term])
  | right (left right : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body right position term) :
      Selects self body (.choice left right)
        (RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1 (position, true)).1
        (.node (.choice 1) [term])
  | ap (functions arguments : Recipe Symbol) (first second : Position)
      (function argument : EngineTerm Symbol)
      (functionSelected : Selects self body functions first function)
      (argumentSelected : Selects self body arguments second argument) :
      Selects self body (.ap functions arguments)
        (productPosition (counts self functions) (counts self arguments) first second)
        (.node .apply [function, argument])
  | label (symbol : Symbol) (inner : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
      (child : Selects self body inner position term) :
      Selects self body (.label symbol inner) ⟨position.size + 1, position.rank⟩
        (SupportTerms.labelTerm symbol term)

/-- A local finite callback law mentions only that leaf's own direct selector. -/
def FiniteExact (source : Finite Symbol) : Prop :=
  ∀ view wanted position, (position, true) ∈ source.positions view wanted ↔
    ∃ term, source.select position = some term ∧ project view term = wanted

/-- Check finite leaves independently, before tying any recursive occurrence. -/
def LeavesExact : Recipe Symbol → Prop
  | .finite source => FiniteExact source
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesExact inner
  | .choice left right | .ap left right => LeavesExact left ∧ LeavesExact right

/-- Sorting does not add or remove any complete checked row. -/
theorem mem_sorted (rows : List Checked) (row : Checked) : row ∈ sorted rows ↔ row ∈ rows := by
  simp [sorted]

/-- A checked product row retains two checked component positions. -/
theorem product_origin (left right : Nat → Nat) (first second : List Checked) (position : Position)
    (member : (position, true) ∈ RecursiveCheckedRanks.productRows left right first second) :
    ∃ p q, (p, true) ∈ first ∧ (q, true) ∈ second ∧ position = productPosition left right p q := by
  obtain ⟨p, pm, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨q, qm, same⟩ := List.mem_map.mp mapped
  have flags : p.2 = true ∧ q.2 = true := by
    have h := congrArg Prod.snd same
    simpa only [Bool.and_eq_true] using h
  exact ⟨p.1, q.1, by rw [← flags.1]; exact pm, by rw [← flags.2]; exact qm,
    (congrArg Prod.fst same).symm⟩

/-- A paid checked row retains its original position and its true flag. -/
theorem pay_origin (rows : List Checked) (position : Position)
    (member : (position, true) ∈ RecursiveCheckedRanks.payRows rows) :
    ∃ original, (original, true) ∈ rows ∧ position = ⟨original.size + 1, original.rank⟩ := by
  obtain ⟨⟨original, flag⟩, present, same⟩ := List.mem_map.mp member
  have flags : flag = true := congrArg Prod.snd same
  subst flag
  exact ⟨original, present, (congrArg Prod.fst same).symm⟩

/-- A choice offset retains its original position and true flag. -/
theorem choice_origin (left right : Nat → Nat) (rows : List Checked) (position : Position)
    (member : (position, true) ∈ rows.map (RecursiveCheckedRanks.choiceRow [left, right] 1)) :
    ∃ original, (original, true) ∈ rows ∧
      position = (RecursiveCheckedRanks.choiceRow [left, right] 1 (original, true)).1 := by
  obtain ⟨⟨original, flag⟩, present, same⟩ := List.mem_map.mp member
  have flags : flag = true := congrArg Prod.snd same
  subst flag
  exact ⟨original, present, (congrArg Prod.fst same).symm⟩

/-- Every forward rank derivation appears with a true certificate in every view. -/
theorem certified_complete [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyExact : LeavesExact body) (recipe : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
    (selected : Selects self body recipe position term) (leaves : LeavesExact recipe) (view : View) :
    (position, true) ∈ positions self body recipe view (project view term) := by
  induction selected generalizing view with
  | finite source position term selected =>
      rw [positions]
      exact (leaves view (project view term) position).mpr ⟨term, selected, rfl⟩
  | occurrence position term child ih =>
      cases view <;> simpa [positions, project, labelled, spine, SupportTerms.applicationLeftChildren,
        SupportTerms.applicationTermChildren] using ih bodyExact .whole
  | map inner position term child ih => rw [positions]; exact ih leaves view
  | pay inner position term child ih =>
      rw [positions]
      exact List.mem_map.mpr ⟨(position, true), ih leaves view, rfl⟩
  | left left right position term child ih =>
      cases view with
      | whole | spine =>
          simpa [positions, project, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, mem_sorted] using ih leaves.1 .whole
      | labelled =>
          rw [positions, mem_sorted]
          exact List.mem_append_left _ (ih leaves.1 .labelled)
  | right left right position term child ih =>
      have offsetMember :
          (RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1 (position, true)) ∈
            (positions self body right .whole [term]).map
              (RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1) :=
        List.mem_map.mpr ⟨(position, true), ih leaves.2 .whole, rfl⟩
      cases view with
      | whole | spine =>
          simpa [positions, project, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, mem_sorted, RecursiveCheckedRanks.choiceRow] using offsetMember
      | labelled =>
          rw [positions, mem_sorted]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨(position, true), ih leaves.2 .labelled, rfl⟩)
  | ap functions arguments first second function argument hf hx ihf ihx =>
      have childProduct := RecursiveCheckedRanks.product_complete (counts self functions) (counts self arguments)
      cases view with
      | whole =>
          simp only [project, positions, mem_sorted]
          exact childProduct _ _ _ _ (ihf leaves.1 .whole) (ihx leaves.2 .whole)
      | spine | labelled =>
          simp only [project, labelled, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, Option.getD_some]
          rw [positions.eq_def]
          dsimp only
          rw [mem_sorted]
          split
          · rename_i found
            simp only [List.getLast?_concat] at found
            contradiction
          · rename_i last found
            have lastEq : argument = last := by simpa only [List.getLast?_concat, Option.some.injEq] using found
            subst last
            simpa only [List.dropLast_concat, project, spine] using
              childProduct _ _ _ _ (ihf leaves.1 .spine) (ihx leaves.2 .whole)
  | label symbol inner position term child ih =>
      rw [labelled_source, StaticCandidateRanks.project_user, positions]
      simp only [↓reduceIte]
      exact List.mem_map.mpr ⟨(position, true), ih leaves .labelled, rfl⟩

/-- True source certificates recover a finite forward rank derivation in every view. -/
theorem checked_sound [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyExact : LeavesExact body) (recipe : Recipe Symbol) (leaves : LeavesExact recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position)
    (member : (position, true) ∈ positions self body recipe view wanted) :
    ∃ term, Selects self body recipe position term ∧ project view term = wanted := by
  cases recipe with
  | finite source =>
      rw [positions] at member
      obtain ⟨term, selected, same⟩ := (leaves view wanted position).mp member
      exact ⟨term, .finite source position term selected, same⟩
  | occurrence =>
      rw [positions.eq_def] at member
      dsimp only at member
      split at member
      · rename_i child
        obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact body bodyExact .whole [child] position member
        have termEq := StaticCheckedRanks.whole_eq term child same
        subst term
        refine ⟨.node .recursion [child], .occurrence position child selected, ?_⟩
        cases view <;> simp [project, labelled, spine, SupportTerms.applicationLeftChildren,
          SupportTerms.applicationTermChildren]
      · simp at member
  | map inner =>
      rw [positions] at member
      obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact inner leaves view wanted position member
      exact ⟨term, .map inner position term selected, same⟩
  | pay inner =>
      rw [positions] at member
      obtain ⟨original, present, rfl⟩ := pay_origin _ _ member
      obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact inner leaves view wanted original present
      exact ⟨term, .pay inner original term selected, same⟩
  | choice left right =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | labelled =>
          dsimp only at member
          rcases List.mem_append.mp member with first | second
          · obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact left leaves.1 .labelled wanted position first
            exact ⟨.node (.choice 0) [term], .left left right position term selected, same⟩
          · obtain ⟨original, present, rfl⟩ := choice_origin _ _ _ _ second
            obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact right leaves.2 .labelled wanted original present
            exact ⟨.node (.choice 1) [term], .right left right original term selected, same⟩
      | whole | spine =>
          dsimp only at member
          split at member
          · rename_i child
            obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact left leaves.1 .whole [child] position member
            have termEq := StaticCheckedRanks.whole_eq term child same
            subst term
            exact ⟨.node (.choice 0) [child], .left left right position child selected, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
          · rename_i child
            obtain ⟨original, present, rfl⟩ := choice_origin _ _ _ _ member
            obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact right leaves.2 .whole [child] original present
            have termEq := StaticCheckedRanks.whole_eq term child same
            subst term
            exact ⟨.node (.choice 1) [child], .right left right original child selected, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
          · simp at member
  | ap functions arguments =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | whole =>
          dsimp only at member
          split at member
          · rename_i function argument
            obtain ⟨p, q, pm, qm, rfl⟩ := product_origin _ _ _ _ _ member
            obtain ⟨f, fs, fv⟩ := checked_sound self body bodyExact functions leaves.1 .whole [function] p pm
            obtain ⟨x, xs, xv⟩ := checked_sound self body bodyExact arguments leaves.2 .whole [argument] q qm
            have feq := StaticCheckedRanks.whole_eq f function fv
            have xeq := StaticCheckedRanks.whole_eq x argument xv
            subst f; subst x
            exact ⟨.node .apply [function, argument], .ap functions arguments p q function argument fs xs, rfl⟩
          · simp at member
      | spine | labelled =>
          dsimp only at member
          split at member
          · simp at member
          · rename_i argument found
            obtain ⟨p, q, pm, qm, rfl⟩ := product_origin _ _ _ _ _ member
            obtain ⟨f, fs, fv⟩ := checked_sound self body bodyExact functions leaves.1 .spine wanted.dropLast p pm
            obtain ⟨x, xs, xv⟩ := checked_sound self body bodyExact arguments leaves.2 .whole [argument] q qm
            have xeq := StaticCheckedRanks.whole_eq x argument xv
            subst x
            refine ⟨.node .apply [f, argument], .ap functions arguments p q f argument fs xs, ?_⟩
            simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, ← fv] using StaticCheckedRanks.spine_split wanted argument found
  | label symbol inner =>
      rw [positions.eq_def] at member
      dsimp only at member
      split at member
      · rename_i found children
        split at member
        · rename_i labelEq
          subst found
          obtain ⟨original, present, rfl⟩ := pay_origin _ _ member
          obtain ⟨term, selected, same⟩ := checked_sound self body bodyExact inner leaves .labelled children original present
          refine ⟨SupportTerms.labelTerm symbol term, .label symbol inner original term selected, ?_⟩
          rw [labelled_source, StaticCandidateRanks.project_user]
          exact congrArg (fun terms => [Term.node (Label.user symbol) terms]) same
        · simp at member
      · simp at member
termination_by (forestHeight wanted, depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [depth, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals first
    | omega
    | have h := dropLast_height wanted; simp only [forestHeight] at h; omega
    | have h := last_height _ _ (by assumption); simp only [forestHeight] at h; omega

/-- The actual recursive callback has exactly the certified forward positions. -/
theorem certified_exact [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyExact : LeavesExact body) (recipe : Recipe Symbol) (leaves : LeavesExact recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ positions self body recipe view wanted ↔
      ∃ term, Selects self body recipe position term ∧ project view term = wanted := by
  constructor
  · exact checked_sound self body bodyExact recipe leaves view wanted position
  · rintro ⟨term, selected, rfl⟩
    exact certified_complete self body bodyExact recipe position term selected leaves view

/-- The finite source operations retain their actual size-plan constructors. -/
def staticPlan : StaticCandidateRanks.Source Symbol → SourcePlanPositions.Plan
  | .pure => .pure
  | .hole => .select 1
  | .indexed count => .select count
  | .map inner => .map (staticPlan inner)
  | .pay inner | .label _ _ inner => .pay (staticPlan inner)
  | .choice left right => .choice (staticPlan left) (staticPlan right)
  | .app functions arguments => .ap (staticPlan functions) (staticPlan arguments)

/-- The derived finite plan contains exactly the original number of outcomes. -/
theorem static_plan_count (source : StaticCandidateRanks.Source Symbol) :
    SourcePlanPositions.count (staticPlan source) = StaticCandidateRanks.cardinality source := by
  induction source <;> simp_all [staticPlan, SourcePlanPositions.count, StaticCandidateRanks.cardinality]

/-- `staticTerms` converts each original callback rank through the actual finite plan. -/
def staticTerms [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (plan : SourcePlanPositions.Plan) : Finite Symbol where
  counts := fun size => (SourcePlanPositions.classRanks plan size).length
  select := SourcePlanPositions.selectClass plan (StaticCandidateRanks.select source)
  positions := fun view wanted => SourcePlanPositions.sorted plan (StaticCheckedRanks.ranks source view wanted)

/-- Existing finite callback and plan-position proofs establish the local leaf contract. -/
theorem static_terms_exact [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (compatible : StaticRankQueryExact.MatchesSelf source) (plan : SourcePlanPositions.Plan) :
    FiniteExact (staticTerms source plan) := by
  intro view wanted position
  constructor
  · intro member
    obtain ⟨rank, original, converted⟩ := (SourcePlanPositions.sorted_member plan _ position true).mp member
    obtain ⟨term, selected, same⟩ := StaticCheckedRanks.checked_sound source view wanted (rank, true) original rfl
    refine ⟨term, ?_, same⟩
    simp [staticTerms, SourcePlanPositions.selectClass, SourcePlanPositions.position_replay plan rank position converted,
      StaticCandidateRanks.select_complete selected]
  · rintro ⟨term, selected, same⟩
    change ((SourcePlanPositions.classRanks plan position.size)[position.rank]?).bind
      (StaticCandidateRanks.select source) = some term at selected
    obtain ⟨rank, rankFound, termFound⟩ := Option.bind_eq_some_iff.mp selected
    have original := StaticRankQueryExact.certified_complete
      (StaticCandidateRanks.select_sound source rank term termFound) compatible view
    rw [same] at original
    exact (SourcePlanPositions.sorted_member plan _ position true).mpr
      ⟨rank, original, SourcePlanPartition.position_class_lookup plan position rank rankFound⟩

/-- Ordinary finite leaves satisfy the local callback law with the derived source size plan. -/
theorem finite_static_exact [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (compatible : StaticRankQueryExact.MatchesSelf source) :
    FiniteExact (staticTerms source (staticPlan source)) := static_terms_exact source compatible _

/-- `atomicStatic` retains the original callback and moves every original rank to size one. -/
theorem atomic_static_exact [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (compatible : StaticRankQueryExact.MatchesSelf source) :
    FiniteExact (staticTerms source (.select (StaticCandidateRanks.cardinality source))) :=
  static_terms_exact source compatible _

/-- The source order is transitive, including the final checked-flag comparison. -/
theorem before_trans (a b c : Checked) (first : before a b) (second : before b c) : before a c := by
  rcases a with ⟨⟨as, ar⟩, af⟩
  rcases b with ⟨⟨bs, br⟩, bf⟩
  rcases c with ⟨⟨cs, cr⟩, cf⟩
  cases af <;> cases bf <;> cases cf <;> simp_all [before] <;> omega

/-- Every two source rows can be compared. -/
theorem before_total (a b : Checked) : before a b || before b a := by
  rcases a with ⟨⟨as, ar⟩, af⟩
  rcases b with ⟨⟨bs, br⟩, bf⟩
  cases af <;> cases bf <;> simp_all [before] <;> omega

/-- Source sorting gives ascending checked rows without changing multiplicity. -/
theorem sorted_ordered (rows : List Checked) : (sorted rows).Pairwise (fun a b => before a b) :=
  List.pairwise_mergeSort before_trans before_total rows

/-- Pay preserves the source comparison of complete rows. -/
theorem before_pay (a b : Checked) (ordered : before a b) :
    before (⟨a.1.size + 1, a.1.rank⟩, a.2) (⟨b.1.size + 1, b.1.rank⟩, b.2) := by
  simpa [before] using ordered

/-- Pay preserves ascending order. -/
theorem pay_ordered (rows : List Checked) (ordered : rows.Pairwise (fun a b => before a b)) :
    (RecursiveCheckedRanks.payRows rows).Pairwise (fun a b => before a b) := by
  rw [RecursiveCheckedRanks.payRows, List.pairwise_map]
  exact ordered.imp (fun h => before_pay _ _ h)

/-- Source finite callbacks establish order before they become recursive leaves. -/
def LeavesOrdered : Recipe Symbol → Prop
  | .finite source => ∀ view wanted, (source.positions view wanted).Pairwise (fun a b => before a b)
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesOrdered inner
  | .choice left right | .ap left right => LeavesOrdered left ∧ LeavesOrdered right

/-- All three source callback views return ascending rows for arbitrary recursive bodies. -/
theorem positions_ordered [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyOrdered : LeavesOrdered body) (recipe : Recipe Symbol) (leaves : LeavesOrdered recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) :
    (positions self body recipe view wanted).Pairwise (fun a b => before a b) := by
  cases recipe with
  | finite source => rw [positions]; exact leaves view wanted
  | occurrence =>
      rw [positions.eq_def]
      dsimp only
      split
      · rename_i term
        exact positions_ordered self body bodyOrdered body bodyOrdered .whole [term]
      · exact .nil
  | map inner => rw [positions]; exact positions_ordered self body bodyOrdered inner leaves view wanted
  | pay inner =>
      rw [positions]
      exact pay_ordered _ (positions_ordered self body bodyOrdered inner leaves view wanted)
  | choice left right | ap left right =>
      rw [positions.eq_def]
      exact sorted_ordered _
  | label symbol inner =>
      rw [positions.eq_def]
      dsimp only
      split
      · rename_i found children
        split
        · exact pay_ordered _ (positions_ordered self body bodyOrdered inner leaves .labelled children)
        · exact .nil
      · exact .nil
termination_by (forestHeight wanted, depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [depth, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals omega

attribute [local instance] lexOrd

/-- The numerical comparison is exactly the source's lexicographic checked-row sort. -/
theorem source_comparison (a b : Checked) :
    (compare (a.1.size, a.1.rank, if a.2 then (1 : Nat) else 0)
      (b.1.size, b.1.rank, if b.2 then (1 : Nat) else 0) != .gt) = before a b := by
  change ((compare a.1.size b.1.size).then
    ((compare a.1.rank b.1.rank).then
      (compare (if a.2 then (1 : Nat) else 0) (if b.2 then (1 : Nat) else 0))) != .gt) = _
  rcases a with ⟨⟨as, ar⟩, af⟩
  rcases b with ⟨⟨bs, br⟩, bf⟩
  cases af <;> cases bf <;> simp only [Nat.compare_eq_ite_lt]
  all_goals simp only [before]
  all_goals (repeat' split) <;> simp_all [Ordering.then] <;> try omega
  all_goals change true = _
  all_goals symm
  all_goals simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  all_goals omega

/-- `staticTerms` supplies the order premise through its own actual sort. -/
theorem static_terms_ordered [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (plan : SourcePlanPositions.Plan) (view : View) (wanted : List (EngineTerm Symbol)) :
    ((staticTerms source plan).positions view wanted).Pairwise (fun a b => before a b) := by
  change ((SourcePlanPositions.convert plan (StaticCheckedRanks.ranks source view wanted)).mergeSort _).Pairwise _
  simpa only [source_comparison, sorted] using
    sorted_ordered (SourcePlanPositions.convert plan (StaticCheckedRanks.ranks source view wanted))

/-- Every finite callback row has a valid class position, including unchecked rows. -/
theorem static_terms_bound [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (plan : SourcePlanPositions.Plan) (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked)
    (member : row ∈ (staticTerms source plan).positions view wanted) :
    row.1.rank < (staticTerms source plan).counts row.1.size := by
  obtain ⟨rank, _, _, _, within⟩ := SourcePlanPositions.sorted_valid plan _ row.1 row.2 member
  exact within

/-- A valid Cartesian rank lies inside the source's complete size convolution. -/
theorem product_rank_bound (left right : Nat → Nat) (first second : Position)
    (firstValid : first.rank < left first.size) (secondValid : second.rank < right second.size) :
    (productPosition left right first second).rank <
      ((List.range (first.size + second.size + 1)).map fun split =>
        left split * right (first.size + second.size - split)).sum := by
  have pairBound := Probability.pairRank_lt firstValid secondValid
  rw [show first.size + second.size + 1 = first.size + (second.size + 1) by omega,
    List.range_add, List.map_append, List.sum_append, List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, Nat.add_zero, Nat.add_sub_cancel_left]
  dsimp only [productPosition]
  omega

/-- Finite candidate bounds include rows that still need replay. -/
def LeavesBounded : Recipe Symbol → Prop
  | .finite source => ∀ view wanted row, row ∈ source.positions view wanted → row.1.rank < source.counts row.1.size
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesBounded inner
  | .choice left right | .ap left right => LeavesBounded left ∧ LeavesBounded right

/-- Every recursive candidate is in range when the source class counts satisfy their knot. -/
theorem positions_bound [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyCounts : ∀ size, self size = counts self body size) (bodyBounded : LeavesBounded body)
    (recipe : Recipe Symbol) (leaves : LeavesBounded recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked)
    (member : row ∈ positions self body recipe view wanted) : row.1.rank < counts self recipe row.1.size := by
  cases recipe with
  | finite source => rw [positions] at member; exact leaves view wanted row member
  | occurrence =>
      rw [positions.eq_def] at member
      dsimp only at member
      split at member
      · rename_i term
        have within := positions_bound self body bodyCounts bodyBounded body bodyBounded .whole [term] row member
        simpa only [counts, bodyCounts] using within
      · simp at member
  | map inner =>
      rw [positions] at member
      exact positions_bound self body bodyCounts bodyBounded inner leaves view wanted row member
  | pay inner =>
      rw [positions] at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact positions_bound self body bodyCounts bodyBounded inner leaves view wanted original present
  | choice left right =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | labelled =>
          rcases List.mem_append.mp member with first | second
          · have within := positions_bound self body bodyCounts bodyBounded left leaves.1 .labelled wanted row first
            simp only [counts]; omega
          · obtain ⟨original, present, rfl⟩ := List.mem_map.mp second
            have within := positions_bound self body bodyCounts bodyBounded right leaves.2 .labelled wanted original present
            simpa [RecursiveCheckedRanks.choiceRow, choicePosition, counts] using Nat.add_lt_add_left within (counts self left original.1.size)
      | whole | spine =>
          dsimp only at member
          split at member
          · rename_i child
            have within := positions_bound self body bodyCounts bodyBounded left leaves.1 .whole [child] row member
            simp only [counts]; omega
          · rename_i child
            obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
            have within := positions_bound self body bodyCounts bodyBounded right leaves.2 .whole [child] original present
            simpa [RecursiveCheckedRanks.choiceRow, choicePosition, counts] using Nat.add_lt_add_left within (counts self left original.1.size)
          · simp at member
  | ap functions arguments =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | whole =>
          dsimp only at member
          split at member
          · rename_i function argument
            obtain ⟨first, fm, mapped⟩ := List.mem_flatMap.mp member
            obtain ⟨second, xm, rfl⟩ := List.mem_map.mp mapped
            exact product_rank_bound _ _ _ _
              (positions_bound self body bodyCounts bodyBounded functions leaves.1 .whole [function] first fm)
              (positions_bound self body bodyCounts bodyBounded arguments leaves.2 .whole [argument] second xm)
          · simp at member
      | spine | labelled =>
          dsimp only at member
          split at member
          · simp at member
          · rename_i argument found
            obtain ⟨first, fm, mapped⟩ := List.mem_flatMap.mp member
            obtain ⟨second, xm, rfl⟩ := List.mem_map.mp mapped
            exact product_rank_bound _ _ _ _
              (positions_bound self body bodyCounts bodyBounded functions leaves.1 .spine wanted.dropLast first fm)
              (positions_bound self body bodyCounts bodyBounded arguments leaves.2 .whole [argument] second xm)
  | label symbol inner =>
      rw [positions.eq_def] at member
      dsimp only at member
      split at member
      · rename_i found children
        split at member
        · obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          exact positions_bound self body bodyCounts bodyBounded inner leaves .labelled children original present
        · simp at member
      · simp at member
termination_by (forestHeight wanted, depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [depth, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals first
    | omega
    | have h := dropLast_height wanted; simp only [forestHeight] at h; omega
    | have h := last_height _ _ (by assumption); simp only [forestHeight] at h; omega

end MicroCFTA.RecursiveCallbackTermination
