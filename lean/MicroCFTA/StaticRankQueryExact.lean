import MicroCFTA.StaticCheckedRanks

/-!
# Complete finite public inverse-rank queries

Each label matcher must accept its own stored symbol. The concrete callback
construction then supplies certified completeness, strict rank order, and
bounds. Public inversion needs no separate callback correctness contract.
-/
namespace MicroCFTA.StaticRankQueryExact
open Language GeneratorCombinators IntegerTermViews StaticCandidateRanks StaticCheckedRanks

/-- Each local flexible matcher accepts the symbol selected by its own label constructor. -/
def MatchesSelf : Source Symbol → Prop
  | .pure | .hole | .indexed _ => True
  | .map inner | .pay inner => MatchesSelf inner
  | .app left right | .choice left right => MatchesSelf left ∧ MatchesSelf right
  | .label symbol acceptsLabel inner => acceptsLabel symbol = true ∧ MatchesSelf inner

/-- Two certified child candidates produce the certified Cartesian rank. -/
theorem product_member_true (radix : Nat) (functions arguments : List Checked) (left right : Nat)
    (leftMember : (left, true) ∈ functions) (rightMember : (right, true) ∈ arguments) :
    (Probability.pairRank radix left right, true) ∈ product radix functions arguments := by
  exact List.mem_flatMap.mpr ⟨(left, true), leftMember, List.mem_map.mpr ⟨(right, true), rightMember, rfl⟩⟩

/-- Splitting the source spine recovers its original prefix and final argument. -/
theorem spine_append (functions : List (Term (Label Symbol)) → List Checked)
    (arguments : Term (Label Symbol) → List Checked) (radix : Nat)
    (front : List (Term (Label Symbol))) (last : Term (Label Symbol)) :
    spineRanks functions arguments radix (front ++ [last]) = product radix (functions front) (arguments last) := by
  simp [spineRanks]

/-- Every actual selected outcome is offered with a true certificate in each source view. -/
theorem certified_complete [DecidableEq Symbol] {source : Source Symbol} {rank : Nat}
    {term : Term (Label Symbol)} (selected : Selected source rank term) (compatible : MatchesSelf source) (view : View) :
    (rank, true) ∈ ranks source view (project view term) := by
  induction selected generalizing view with
  | pure => cases view <;> simp [ranks, project, labelled, spine, SupportTerms.applicationLeftChildren]
  | hole => cases view <;> simp [ranks, project, labelled, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
  | indexed count rank valid => cases view <;> simp [ranks, project, labelled, spine, SupportTerms.applicationLeftChildren,
      SupportTerms.applicationTermChildren, valid]
  | map selected ih | pay selected ih => exact ih compatible view
  | @app functions arguments functionRank argumentRank functionTerm argumentTerm left right ihl ihr =>
      cases view with
      | whole =>
          exact product_member_true _ _ _ _ _ (ihl compatible.1 .whole) (ihr compatible.2 .whole)
      | spine | labelled =>
          simpa [ranks, project, labelled, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, spine_append] using
              product_member_true (cardinality arguments) _ _ functionRank argumentRank
                (ihl compatible.1 .spine) (ihr compatible.2 .whole)
  | @left left right rank term selected ih =>
      cases view with
      | whole | spine => simpa [ranks, project, spine, SupportTerms.applicationLeftChildren,
          SupportTerms.applicationTermChildren] using ih compatible.1 .whole
      | labelled => exact List.mem_append_left _ (ih compatible.1 .labelled)
  | @right left right rank term selected ih =>
      have offsetMember : (cardinality left + rank, true) ∈ offset (cardinality left) (ranks right .whole [term]) :=
        List.mem_map.mpr ⟨(rank, true), ih compatible.2 .whole, rfl⟩
      cases view with
      | whole | spine => simpa [ranks, project, spine, SupportTerms.applicationLeftChildren,
          SupportTerms.applicationTermChildren] using offsetMember
      | labelled =>
          exact List.mem_append_right _ (List.mem_map.mpr ⟨(rank, true), ih compatible.2 .labelled, rfl⟩)
  | @label inner rank term symbol acceptsLabel selected ih =>
      rw [labelled_source, project_user]
      simp only [ranks, compatible.1, ↓reduceIte]
      exact List.mem_map.mpr ⟨(rank, true), ih compatible.2 .labelled, by simp⟩

/-- Source callback ranks are strictly increasing and remain inside the finite cardinality. -/
def ValidRanks (total : Nat) (indices : List Nat) : Prop :=
  indices.Pairwise (· < ·) ∧ ∀ rank ∈ indices, rank < total

/-- An empty callback has no rank or order obligation. -/
theorem valid_nil (total : Nat) : ValidRanks total [] := by simp [ValidRanks]

/-- Enlarging the cardinality does not change existing rank order. -/
theorem valid_weaken (first second : Nat) (indices : List Nat) (valid : ValidRanks first indices)
    (included : first ≤ second) : ValidRanks second indices :=
  ⟨valid.1, fun rank member => Nat.lt_of_lt_of_le (valid.2 rank member) included⟩

/-- Offsets preserve strict order and put each rank inside the shifted bound. -/
theorem valid_offset (start total : Nat) (indices : List Nat) (valid : ValidRanks total indices) :
    ValidRanks (start + total) (indices.map (start + ·)) := by
  constructor
  · exact valid.1.map _ (fun _ _ before => by omega)
  · intro rank member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    have bounded := valid.2 original present
    omega

/-- Complete choice blocks are ordered because every left rank precedes every shifted right rank. -/
theorem valid_choice (leftCount rightCount : Nat) (left right : List Nat)
    (leftValid : ValidRanks leftCount left) (rightValid : ValidRanks rightCount right) :
    ValidRanks (leftCount + rightCount) (left ++ right.map (leftCount + ·)) := by
  have shifted := valid_offset leftCount rightCount right rightValid
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨leftValid.1, shifted.1, ?_⟩
    intro first firstMember second secondMember
    have before := leftValid.2 first firstMember
    obtain ⟨original, _, same⟩ := List.mem_map.mp secondMember
    omega
  · intro rank member
    rcases List.mem_append.mp member with first | second
    · have bounded := leftValid.2 rank first; omega
    · exact shifted.2 rank second

/-- Source Cartesian blocks have strict mixed-radix order and valid product ranks. -/
theorem valid_product (leftCount rightCount : Nat) (left right : List Nat)
    (leftValid : ValidRanks leftCount left) (rightValid : ValidRanks rightCount right) :
    ValidRanks (leftCount * rightCount) (productCandidates rightCount left right) := by
  constructor
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro first member
      exact rightValid.1.map _ (fun _ _ before => by simp only [Probability.pairRank]; omega)
    · apply leftValid.1.imp
      intro first second before firstRank firstMember secondRank secondMember
      obtain ⟨firstArg, firstArgMember, rfl⟩ := List.mem_map.mp firstMember
      obtain ⟨secondArg, secondArgMember, rfl⟩ := List.mem_map.mp secondMember
      have firstBound := Probability.pairRank_lt (leftCount := first + 1) (left := first) (by omega) (rightValid.2 firstArg firstArgMember)
      have blocks := Nat.mul_le_mul_right rightCount (show first + 1 ≤ second by omega)
      simp only [Probability.pairRank] at *
      omega
  · intro rank member
    obtain ⟨first, firstMember, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp mapped
    exact Probability.pairRank_lt (leftValid.2 first firstMember) (rightValid.2 second secondMember)

/-- The actual flag-carrying callbacks derive strict order and bounds in every view. -/
theorem callbacks_valid [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) :
    ValidRanks (cardinality source) ((ranks source view wanted).map Prod.fst) := by
  induction source generalizing view wanted with
  | pure =>
      simp only [ranks]
      split <;> simp [ValidRanks, cardinality]
  | hole =>
      simp only [ranks]
      split <;> simp [ValidRanks, cardinality]
  | indexed count =>
      simp only [ranks]
      split
      · split <;> simp_all [ValidRanks, cardinality]
      · exact valid_nil _
  | map inner ih | pay inner ih => exact ih view wanted
  | app functions arguments ihf iha =>
      cases view with
      | whole =>
          simp only [ranks]
          split
          · rw [product_erasure]
            exact valid_product _ _ _ _ (ihf _ _) (iha _ _)
          · exact valid_nil _
      | spine | labelled =>
          simp only [ranks, spineRanks]
          split
          · exact valid_nil _
          · rw [product_erasure]
            exact valid_product _ _ _ _ (ihf _ _) (iha _ _)
  | choice left right ihl ihr =>
      cases view with
      | labelled =>
          simp only [ranks, List.map_append, offset_erasure]
          exact valid_choice _ _ _ _ (ihl _ _) (ihr _ _)
      | whole | spine =>
          simp only [ranks]
          split
          · exact valid_weaken _ _ _ (ihl _ _) (by simp [cardinality])
          · rw [offset_erasure]
            exact valid_offset _ _ _ (ihr _ _)
          · exact valid_nil _
  | label symbol acceptsLabel inner ih =>
      simp only [ranks]
      split
      · split
        · simpa only [List.map_map, Function.comp_def, cardinality] using ih .labelled _
        · exact valid_nil _
      · exact valid_nil _

/-- Every candidate, including an unchecked one, lies in the source rank interval. -/
theorem candidate_bound [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ ranks source view wanted) : candidate.1 < cardinality source :=
  (callbacks_valid source view wanted).2 candidate.1 (List.mem_map.mpr ⟨candidate, member, rfl⟩)

/-- Signed public candidates retain the strict increasing order of their finite source ranks. -/
theorem public_strict [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) :
    ((publicRows source view wanted).map CheckedRankQueries.Candidate.rank).Pairwise (· < ·) := by
  have mapped : (((ranks source view wanted).map Prod.fst).map (fun rank : Nat => (rank : Int))).Pairwise (· < ·) :=
    (callbacks_valid source view wanted).1.map (fun rank : Nat => (rank : Int))
      (fun first second before => by omega)
  simpa only [publicRows, List.map_map, Function.comp_def] using mapped

/-- The public order contract follows from strict callback order. -/
theorem public_ordered [DecidableEq Symbol] (source : Source Symbol) (view : View)
    (wanted : List (Term (Label Symbol))) :
    ((publicRows source view wanted).map CheckedRankQueries.Candidate.rank).Pairwise (· ≤ ·) :=
  (public_strict source view wanted).imp (fun before => Int.le_of_lt before)

/-- Successful signed replay is exactly a nonnegative constructor-selected original outcome. -/
theorem decode_exact (source : Source Symbol) (rank : Int) (term : Term (Label Symbol)) :
    decode source rank = .ok term ↔ ∃ original : Nat, rank = (original : Int) ∧ Selected source original term := by
  constructor
  · intro decoded
    unfold decode at decoded
    split at decoded
    · cases decoded
    · next nonnegative =>
      cases found : StaticCandidateRanks.select source rank.toNat with
      | none => simp [found] at decoded
      | some value =>
          have same : value = term := by simpa [found] using decoded
          subst value
          exact ⟨rank.toNat, by omega, select_sound source rank.toNat term found⟩
  · rintro ⟨original, rfl, selected⟩
    simp [decode, select_complete selected]

/-- The public completeness contract follows from each actual selected member's true candidate. -/
theorem public_complete [DecidableEq Symbol] (source : Source Symbol) (compatible : MatchesSelf source)
    (wanted : Term (Label Symbol)) :
    CheckedRankQueries.Complete (decode source) wanted (publicRows source .whole [wanted]) := by
  intro rank decoded
  obtain ⟨original, rfl, selected⟩ := (decode_exact source rank wanted).mp decoded
  exact ⟨⟨original, true⟩, List.mem_map.mpr
    ⟨(original, true), certified_complete selected compatible .whole, rfl⟩, rfl⟩

/-- The public result contains every matching rank and no nonmatching rank. -/
theorem public_ranks_exact [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (compatible : MatchesSelf source) (wanted : Term (Label Symbol)) (rank : Int) :
    rank ∈ CheckedRankQueries.retained (decode source) wanted (publicRows source .whole [wanted]) ↔
      decode source rank = .ok wanted :=
  CheckedRankQueries.retained_exact _ _ _ (public_checked_sound source wanted)
    (public_complete source compatible wanted) rank

/-- Candidate enumeration and public filtering never duplicate a replay rank. -/
theorem public_ranks_distinct [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (wanted : Term (Label Symbol)) :
    (CheckedRankQueries.retained (decode source) wanted (publicRows source .whole [wanted])).Nodup := by
  have unique : ((publicRows source .whole [wanted]).map CheckedRankQueries.Candidate.rank).Nodup :=
    (public_strict source .whole [wanted]).imp (fun before => Int.ne_of_lt before)
  exact unique.sublist (CheckedRankQueries.retained_sublist _ _ _)

/-- The exact finite callback supplied to the public query entry point. -/
def querySource [DecidableEq Symbol] (source : Source Symbol) :
    CheckedRankQueries.Source Unit (Term (Label Symbol)) :=
  .finite (.ok (fun term => publicRows source .whole [term]))

/-- Public finite rank lookup returns precisely the least rank that replays the requested term. -/
theorem rank_query_exact [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (compatible : MatchesSelf source) (wanted : Term (Label Symbol)) (rank : Int) :
    CheckedRankQueries.rankOf (decode source) (querySource source) wanted = .ok rank ↔
      decode source rank = .ok wanted ∧ ∀ other, decode source other = .ok wanted → rank ≤ other := by
  apply CheckedRankQueries.rankOf_exact (decode source) (querySource source) wanted
    (publicRows source .whole [wanted]) rfl (public_checked_sound source wanted)
    (public_complete source compatible wanted) (public_ordered source .whole [wanted]) rank

/-- The source finite query rejects exactly the terms absent from all selected outcomes. -/
theorem rank_query_rejected [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (compatible : MatchesSelf source) (wanted : Term (Label Symbol)) :
    CheckedRankQueries.rankOf (decode source) (querySource source) wanted = .error .termNotInLanguage ↔
      ∀ original, ¬Selected source original wanted := by
  rw [CheckedRankQueries.rankOf_rejected (decode source) (querySource source) wanted
    (publicRows source .whole [wanted]) rfl (public_checked_sound source wanted)
    (public_complete source compatible wanted)]
  constructor
  · intro absent original selected
    exact absent original ((decode_exact source original wanted).mpr ⟨original, rfl, selected⟩)
  · intro absent rank decoded
    obtain ⟨original, _, selected⟩ := (decode_exact source rank wanted).mp decoded
    exact absent original selected

/-- An existing finite member always has a successful public inverse, even when other members have the same term. -/
theorem selected_query_succeeds [DecidableEq Symbol] [DecidableEq (Term (Label Symbol))]
    (source : Source Symbol) (compatible : MatchesSelf source) (original : Nat) (wanted : Term (Label Symbol))
    (selected : Selected source original wanted) :
    ∃ rank, CheckedRankQueries.rankOf (decode source) (querySource source) wanted = .ok rank ∧
      0 ≤ rank ∧ rank < (cardinality source : Int) ∧ rank ≤ (original : Int) := by
  have decoded := (decode_exact source original wanted).mpr ⟨original, rfl, selected⟩
  have member := (CheckedRankQueries.retained_exact (decode source) wanted (publicRows source .whole [wanted])
    (public_checked_sound source wanted) (public_complete source compatible wanted) original).mpr decoded
  cases found : CheckedRankQueries.retained (decode source) wanted (publicRows source .whole [wanted]) with
  | nil => simp [found] at member
  | cons first rest =>
      have queried : CheckedRankQueries.rankOf (decode source) (querySource source) wanted = .ok first := by
        simp [CheckedRankQueries.rankOf, CheckedRankQueries.ranksOf, CheckedRankQueries.candidates,
          querySource, Except.map, Bind.bind, Except.bind, found]
      obtain ⟨replayed, minimum⟩ := (rank_query_exact source compatible wanted first).mp queried
      obtain ⟨natural, same, chosen⟩ := (decode_exact source first wanted).mp replayed
      have bounded := selected_bound chosen
      exact ⟨first, queried, by omega, by omega, minimum original decoded⟩

/-- A local matcher that rejects its selected symbol can omit a real term; the local condition is necessary. -/
theorem rejecting_own_label_omits :
    let source : Source Nat := .label 0 (fun _ => false) .pure
    Selected source 0 (.node (.user 0) []) ∧ ranks source .whole [.node (.user 0) []] = [] := by
  constructor
  · exact Selected.label 0 (fun _ => false) Selected.pure
  · rfl

end MicroCFTA.StaticRankQueryExact
