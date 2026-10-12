import MicroCFTA.StaticCandidateRanks
import MicroCFTA.CheckedRankQueries

/-!
# Checked-symbol certificates from finite static callbacks

A candidate's flag follows the source callback. It is not recomputed by
replaying the candidate. The proof derives replay from that flag in every
whole, spine, and labelled request view.

`erasure` connects these callbacks to StaticCandidateRanks.
`public_checked_sound` supplies CheckedRankQueries.CheckedSound for whole
terms. Signed replay retains success exactly and maps each failure to Unit.
Callback completeness, ascending order, and composite or recursive flag
producers remain separate obligations.
-/
namespace MicroCFTA.StaticCheckedRanks
open Language GeneratorCombinators IntegerTermViews StaticCandidateRanks

/-- Finite callback ranks are nonnegative and retain the source Boolean certificate. -/
abbrev Checked := Nat × Bool

/-- Product rank order has the argument varying fastest; both certificates are required. -/
def product (radix : Nat) (functions arguments : List Checked) : List Checked :=
  functions.flatMap fun function => arguments.map fun argument =>
    (Probability.pairRank radix function.1 argument.1, function.2 && argument.2)

/-- Choice offsets change the rank and retain its certificate. -/
def offset (start : Nat) (rows : List Checked) : List Checked :=
  rows.map fun entry => (start + entry.1, entry.2)

/-- The source splits the final spine argument from its complete function prefix. -/
def spineRanks (functions : List (Term (Label Symbol)) → List Checked)
    (arguments : Term (Label Symbol) → List Checked) (radix : Nat)
    (wanted : List (Term (Label Symbol))) : List Checked :=
  match wanted.getLast? with
  | none => []
  | some argument => product radix (functions wanted.dropLast) (arguments argument)

/-- Exact finite outcomeRanks dispatch, including the source checked flags. -/
def ranks [DecidableEq Symbol] : Source Symbol → View → List (Term (Label Symbol)) → List Checked
  | .pure => fun view wanted => match view, wanted with
      | .whole, [.node .pure []] => [(0, true)]
      | .spine, [] | .labelled, [] => [(0, true)]
      | _, _ => []
  | .hole => fun _ wanted => match wanted with
      | [.node label []] => [(0, decide (label = .placeholder))]
      | _ => []
  | .indexed count => fun _ wanted => match wanted with
      | [.node (.index rank) []] => if rank < count then [(rank, true)] else []
      | _ => []
  | .map inner | .pay inner => ranks inner
  | .app functions arguments => fun view wanted => match view with
      | .whole => match wanted with
          | [.node .apply [function, argument]] =>
              product (cardinality arguments) (ranks functions .whole [function]) (ranks arguments .whole [argument])
          | _ => []
      | .spine | .labelled =>
          spineRanks (ranks functions .spine) (fun term => ranks arguments .whole [term]) (cardinality arguments) wanted
  | .choice left right => fun view wanted => match view with
      | .labelled => ranks left .labelled wanted ++ offset (cardinality left) (ranks right .labelled wanted)
      | .whole | .spine => match wanted with
          | [.node (.choice 0) [term]] => ranks left .whole [term]
          | [.node (.choice 1) [term]] => offset (cardinality left) (ranks right .whole [term])
          | _ => []
  | .label symbol acceptsLabel inner => fun _ wanted => match wanted with
      | [.node (.user found) children] =>
          if acceptsLabel found then (ranks inner .labelled children).map (fun entry => (entry.1, entry.2 && decide (found = symbol)))
          else []
      | _ => []

/-- A true product certificate originates from two true child certificates. -/
theorem product_checked (radix : Nat) (functions arguments : List Checked) (candidate : Checked)
    (member : candidate ∈ product radix functions arguments) (checked : candidate.2 = true) :
    ∃ function ∈ functions, ∃ argument ∈ arguments, function.2 = true ∧ argument.2 = true ∧
      candidate.1 = Probability.pairRank radix function.1 argument.1 := by
  obtain ⟨function, functionMember, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨argument, argumentMember, same⟩ := List.mem_map.mp mapped
  have equal : candidate = (Probability.pairRank radix function.1 argument.1, function.2 && argument.2) := same.symm
  subst candidate
  have flags : function.2 = true ∧ argument.2 = true := by simpa only [Bool.and_eq_true] using checked
  exact ⟨function, functionMember, argument, argumentMember, flags.1, flags.2, rfl⟩

/-- A true offset certificate retains its child's true flag and original rank. -/
theorem offset_checked (start : Nat) (rows : List Checked) (candidate : Checked)
    (member : candidate ∈ offset start rows) (checked : candidate.2 = true) :
    ∃ original ∈ rows, original.2 = true ∧ candidate.1 = start + original.1 := by
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  subst candidate
  exact ⟨original, present, checked, rfl⟩

/-- The singleton whole view determines its complete term. -/
theorem whole_eq (term wanted : Term (Label Symbol)) (same : project .whole term = [wanted]) : term = wanted :=
  (List.cons.inj same).1

/-- A nonempty source spine consists of its prefix and the final selected argument. -/
theorem spine_split (wanted : List (Term (Label Symbol))) (argument : Term (Label Symbol))
    (found : wanted.getLast? = some argument) : wanted.dropLast ++ [argument] = wanted := by
  obtain ⟨front, same⟩ := List.getLast?_eq_some_iff.mp found
  rw [same]
  simp

/-- True callback flags derive an original selected term and its exact requested view. -/
theorem checked_sound [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ ranks source view wanted) (checked : candidate.2 = true) :
    ∃ term, Selected source candidate.1 term ∧ project view term = wanted := by
  induction source generalizing view wanted candidate with
  | pure =>
      simp only [ranks] at member
      split at member
      all_goals simp only [List.mem_singleton, List.not_mem_nil] at member
      all_goals try contradiction
      all_goals have same : candidate = (0, true) := member
      all_goals subst candidate
      all_goals exact ⟨.node .pure [], .pure, by simp [project, labelled, spine, SupportTerms.applicationLeftChildren]⟩
  | hole =>
      simp only [ranks] at member
      split at member
      · rename_i label
        have same : candidate = (0, decide (label = .placeholder)) := List.mem_singleton.mp member
        subst candidate
        have labelEq : label = .placeholder := by simpa using checked
        subst label
        refine ⟨.node .placeholder [], .hole, ?_⟩
        cases view <;> simp [project, labelled, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
      · simp at member
  | indexed count =>
      simp only [ranks] at member
      split at member
      · rename_i rank
        split at member
        · next valid =>
          have same : candidate = (rank, true) := List.mem_singleton.mp member
          subst candidate
          refine ⟨.node (.index rank) [], .indexed count rank valid, ?_⟩
          cases view <;> simp [project, labelled, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
        · simp at member
      · simp at member
  | map inner ih =>
      obtain ⟨term, selected, exact⟩ := ih view wanted candidate member checked
      exact ⟨term, .map selected, exact⟩
  | pay inner ih =>
      obtain ⟨term, selected, exact⟩ := ih view wanted candidate member checked
      exact ⟨term, .pay selected, exact⟩
  | app functions arguments ihf iha =>
      cases view with
      | whole =>
          simp only [ranks] at member
          split at member
          · rename_i function argument
            obtain ⟨left, leftMember, right, rightMember, leftChecked, rightChecked, same⟩ :=
              product_checked _ _ _ candidate member checked
            obtain ⟨functionTerm, functionSelected, functionView⟩ := ihf .whole [function] left leftMember leftChecked
            obtain ⟨argumentTerm, argumentSelected, argumentView⟩ := iha .whole [argument] right rightMember rightChecked
            have functionEq := whole_eq functionTerm function functionView
            have argumentEq := whole_eq argumentTerm argument argumentView
            refine ⟨.node .apply [functionTerm, argumentTerm], ?_, ?_⟩
            · rw [same]; exact .app functionSelected argumentSelected
            · simp [project, functionEq, argumentEq]
          · simp at member
      | spine | labelled =>
          simp only [ranks, spineRanks] at member
          split at member
          · simp at member
          · rename_i argument found
            obtain ⟨left, leftMember, right, rightMember, leftChecked, rightChecked, same⟩ :=
              product_checked _ _ _ candidate member checked
            obtain ⟨functionTerm, functionSelected, functionView⟩ := ihf .spine wanted.dropLast left leftMember leftChecked
            obtain ⟨argumentTerm, argumentSelected, argumentView⟩ := iha .whole [argument] right rightMember rightChecked
            have argumentEq := whole_eq argumentTerm argument argumentView
            refine ⟨.node .apply [functionTerm, argumentTerm], ?_, ?_⟩
            · rw [same]; exact .app functionSelected argumentSelected
            · simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
                SupportTerms.applicationTermChildren, argumentEq, ← functionView] using spine_split wanted argument found
  | choice left right ihl ihr =>
      cases view with
      | labelled =>
          rcases List.mem_append.mp member with leftMember | rightMember
          · obtain ⟨term, selected, same⟩ := ihl .labelled wanted candidate leftMember checked
            exact ⟨.node (.choice 0) [term], .left selected, same⟩
          · obtain ⟨child, childMember, childChecked, rankEq⟩ := offset_checked _ _ candidate rightMember checked
            obtain ⟨term, selected, same⟩ := ihr .labelled wanted child childMember childChecked
            refine ⟨.node (.choice 1) [term], ?_, same⟩
            rw [rankEq]; exact .right selected
      | whole | spine =>
          simp only [ranks] at member
          split at member
          · rename_i term
            obtain ⟨child, selected, same⟩ := ihl .whole [term] candidate member checked
            have termEq := whole_eq child term same
            refine ⟨.node (.choice 0) [child], .left selected, ?_⟩
            simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, termEq]
          · rename_i term
            obtain ⟨childCandidate, childMember, childChecked, rankEq⟩ := offset_checked _ _ candidate member checked
            obtain ⟨child, selected, same⟩ := ihr .whole [term] childCandidate childMember childChecked
            have termEq := whole_eq child term same
            refine ⟨.node (.choice 1) [child], ?_, ?_⟩
            · rw [rankEq]; exact .right selected
            · simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, termEq]
          · simp at member
  | label symbol acceptsLabel inner ih =>
      simp only [ranks] at member
      split at member
      · rename_i found children
        split at member
        · obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
          subst candidate
          have flags : child.2 = true ∧ decide (found = symbol) = true := by simpa only [Bool.and_eq_true] using checked
          obtain ⟨childChecked, labelEq⟩ := flags
          have labelEq : found = symbol := by simpa using labelEq
          obtain ⟨term, selected, sameView⟩ := ih .labelled children child childMember childChecked
          refine ⟨SupportTerms.labelTerm symbol term, .label symbol acceptsLabel selected, ?_⟩
          rw [labelled_source, project_user]
          simp only [project] at sameView
          rw [sameView, labelEq]
        · simp at member
      · simp at member

/-- Erasing certificates leaves the existing Cartesian rank loop unchanged. -/
theorem product_erasure (radix : Nat) (functions arguments : List Checked) :
    (product radix functions arguments).map Prod.fst =
      productCandidates radix (functions.map Prod.fst) (arguments.map Prod.fst) := by
  simp [product, productCandidates, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- Erasing an offset certificate retains the exact source choice order. -/
theorem offset_erasure (start : Nat) (rows : List Checked) :
    (offset start rows).map Prod.fst = (rows.map Prod.fst).map (start + ·) := by
  simp [offset, List.map_map, Function.comp_def]

/-- Erasing flags reproduces the already modeled original candidate callback exactly. -/
theorem erasure [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) :
    (ranks source view wanted).map Prod.fst = candidates source view wanted := by
  induction source generalizing view wanted with
  | pure =>
      simp only [ranks]
      split <;> simp_all [candidates]
  | hole =>
      simp only [ranks]
      split <;> simp_all [candidates]
  | indexed count =>
      simp only [ranks]
      split
      · split <;> simp_all [candidates]
      · simp_all [candidates]
  | map inner ih | pay inner ih => exact ih view wanted
  | app functions arguments ihf iha =>
      cases view with
      | whole =>
          simp only [ranks]
          split <;> simp_all [candidates, product_erasure]
      | spine | labelled =>
          simp only [ranks, spineRanks]
          split <;> simp_all [candidates, spineCandidates, product_erasure]
  | choice left right ihl ihr =>
      cases view with
      | labelled => simp [ranks, candidates, offset_erasure, ihl, ihr]
      | whole | spine =>
          simp only [ranks]
          split <;> simp_all [candidates, offset_erasure]
  | label symbol acceptsLabel inner ih =>
      simp only [ranks]
      split
      · split <;> simp_all [candidates, List.map_map, Function.comp_def]
      · simp_all [candidates]

/-- Public signed rank replay rejects negatives and projects finite selection errors to failure. -/
def decode (source : Source Symbol) (rank : Int) : Except Unit (Term (Label Symbol)) :=
  if rank < 0 then .error () else
    match StaticCandidateRanks.select source rank.toNat with
    | none => .error ()
    | some term => .ok term

/-- Convert finite rank candidates to the exact public signed rank and flag representation. -/
def publicRows [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) : List CheckedRankQueries.Candidate :=
  (ranks source view wanted).map fun entry => ⟨entry.1, entry.2⟩

/-- A true flag also certifies that its rank is inside the actual finite source cardinality. -/
theorem checked_bound [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ ranks source view wanted) (checked : candidate.2 = true) :
    candidate.1 < cardinality source := by
  obtain ⟨term, selected, _⟩ := checked_sound source view wanted candidate member checked
  exact selected_bound selected

/-- The whole-term producer contract required by the public shortcut follows from the actual callbacks. -/
theorem public_checked_sound [DecidableEq Symbol] (source : Source Symbol)
    (wanted : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (decode source) wanted (publicRows source .whole [wanted]) := by
  intro candidate member checked
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  subst candidate
  obtain ⟨term, selected, exactView⟩ := checked_sound source .whole [wanted] original present checked
  have same := whole_eq term wanted exactView
  subst term
  simp [decode, select_complete selected]

/-- Every true flag is safe under every request projection, not just the public whole-term view. -/
theorem public_view_checked_sound [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) :
    CheckedRankQueries.CheckedSound (fun rank => (decode source rank).map (project view))
      wanted (publicRows source view wanted) := by
  intro candidate member checked
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  subst candidate
  obtain ⟨term, selected, exactView⟩ := checked_sound source view wanted original present checked
  have nonnegative : ¬(original.1 : Int) < 0 := by omega
  simp [decode, nonnegative, select_complete selected, Except.map, exactView]

/-- The actual finite producer makes the public flag shortcut equivalent to exact term replay. -/
theorem public_keep_exact [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (wanted : Term (Label Symbol)) (candidate : CheckedRankQueries.Candidate)
    (member : candidate ∈ publicRows source .whole [wanted]) :
    CheckedRankQueries.keep (decode source) wanted candidate = true ↔ decode source candidate.rank = .ok wanted :=
  CheckedRankQueries.keep_exact _ _ _ (public_checked_sound source wanted) candidate member

/-- A filled-looking leaf remains a candidate but is not certified as the original placeholder. -/
theorem other_leaf_unchecked :
    ranks (.hole : Source Nat) .whole [.node (.user 7) []] = [(0, false)] := rfl

/-- A flexible label match cannot certify a different selected user symbol. -/
theorem flexible_label_unchecked :
    ranks (.label 0 (fun _ => true) .pure : Source Nat) .whole [.node (.user 1) []] = [(0, false)] := rfl

/-- Product callbacks transmit an unchecked argument even when the function prefix is fully checked. -/
theorem product_unchecked_argument :
    ranks (.app .pure .hole : Source Nat) .spine [.node (.user 7) []] = [(0, false)] := rfl

/-- A closed label can expose both correctly certified ranks of duplicate member terms. -/
theorem choice_preserves_certificates :
    ranks (.label 7 (fun _ => true) (.choice .pure .pure) : Source Nat)
      .whole [.node (.user 7) []] = [(0, true), (1, true)] := rfl

end MicroCFTA.StaticCheckedRanks
