import MicroCFTA.SymbolicSolutions

/-!
# Finite solution-count bijections

The proofs count distinct live tuples. A relation between tuples can preserve
their count even when a rewrite removes one live variable. The relation must
be total and unique in both directions.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Mapping the input domain names does not change the Cartesian product. -/
theorem products_map (choices : Middle → List Output) (names : Input → Middle) (inputs : List Input) :
    products choices (inputs.map names) = products (fun input => choices (names input)) inputs := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih => simp only [List.map_cons, products, ih]

/-- Distinct choices in each coordinate produce distinct ordered tuples. -/
theorem products_nodup (choices : Input → List Output) (inputs : List Input)
    (distinct : ∀ input ∈ inputs, (choices input).Nodup) : (products choices inputs).Nodup := by
  induction inputs with
  | nil => simp [products]
  | cons input inputs ih =>
      have tail := ih (fun other member => distinct other (by simp [member]))
      change List.Pairwise (· ≠ ·) ((choices input).flatMap fun value => (products choices inputs).map (value :: ·))
      apply List.pairwise_flatMap.mpr
      constructor
      · intro value _
        apply List.pairwise_map.mpr
        exact tail.imp (fun different same => different (List.cons.inj same).2)
      · apply (distinct input (by simp)).imp
        intro left right different first firstMember second secondMember same
        obtain ⟨leftTail, _, leftSame⟩ := List.mem_map.mp firstMember
        obtain ⟨rightTail, _, rightSame⟩ := List.mem_map.mp secondMember
        exact different (List.cons.inj (leftSame.trans (same.trans rightSame.symm))).1

/-- A domain tuple uses exactly the semantic language of each corresponding graph. -/
theorem candidateTuples_spec (language : Nat → List (Term Symbol)) (domains : List (Nat × Nat))
    (values : List (Term Symbol)) : values ∈ candidateTuples language domains ↔
      All₂ (fun entry value => value ∈ language entry.2) domains values := by
  rw [candidateTuples, products_map]
  exact mem_products _ domains values

/-- For a matching tuple, candidate membership is exactly the valuation's domain requirement. -/
theorem matching_candidate_iff (language : Nat → List (Term Symbol)) (assignment : Nat → Term Symbol)
    (domains : List (Nat × Nat)) (values : List (Term Symbol)) (matching : TupleMatches assignment domains values) :
    values ∈ candidateTuples language domains ↔ DomainsHold (fun node term => term ∈ language node) assignment domains := by
  rw [candidateTuples_spec]
  induction matching with
  | nil =>
      constructor
      · intro _ _ member; cases member
      · intro _; exact .nil
  | @cons entry value entries values same tailMatch ih =>
      constructor
      · intro choices
        cases choices with
        | cons first rest =>
            intro candidate member
            rcases List.mem_cons.mp member with rfl | member
            · simpa only [same] using first
            · exact ih.mp rest candidate member
      · intro holds
        apply All₂.cons
        · simpa only [same] using holds entry (by simp)
        · exact ih.mpr (fun candidate member => holds candidate (by simp [member]))

/-- The finite solution list is exactly the valid live valuations projected to ordered tuples. -/
theorem solutionTuples_spec (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (values : List (Term Symbol)) : values ∈ solutionTuples language problem ↔
      ∃ assignment, TupleMatches assignment problem.domains values ∧
        ProblemHolds (fun node term => term ∈ language node) assignment problem := by
  classical
  simp only [solutionTuples, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, assignment, matching, bindings, constraints⟩
    exact ⟨assignment, matching, (matching_candidate_iff language assignment problem.domains values matching).mp candidate,
      bindings, constraints⟩
  · rintro ⟨assignment, matching, domains, bindings, constraints⟩
    exact ⟨(matching_candidate_iff language assignment problem.domains values matching).mpr domains,
      assignment, matching, bindings, constraints⟩

/-- Filtering independent distinct graph languages cannot create repeated solution tuples. -/
theorem solutionTuples_nodup (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (problem : Problem Symbol) :
    (solutionTuples language problem).Nodup := by
  classical
  unfold solutionTuples
  exact (products_nodup language (problem.domains.map Prod.snd) (fun node _ => distinct node)).filter _

/-- A total injective relation into a finite list bounds the number of distinct source values. -/
theorem relation_cardinality_le (left : List Input) (right : List Output) (fallback : Output)
    (distinct : left.Nodup) (relation : Input → Output → Prop)
    (total : ∀ input ∈ left, ∃ output ∈ right, relation input output)
    (injective : ∀ first ∈ left, ∀ second ∈ left, ∀ output ∈ right,
      relation first output → relation second output → first = second) : left.length ≤ right.length := by
  classical
  let choose := fun input => if member : input ∈ left then Classical.choose (total input member) else fallback
  have selected : ∀ input ∈ left, choose input ∈ right ∧ relation input (choose input) := by
    intro input member
    simpa only [choose, dite_eq_left member] using Classical.choose_spec (total input member)
  have mappedDistinct : (left.map choose).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro first second firstBound secondBound same
    have firstBound' : first < left.length := by simpa only [List.length_map] using firstBound
    have secondBound' : second < left.length := by simpa only [List.length_map] using secondBound
    have firstMember := List.getElem_mem firstBound'
    have secondMember := List.getElem_mem secondBound'
    have outputSame : choose left[first] = choose left[second] := by simpa only [List.getElem_map] using same
    have valuesSame := injective left[first] firstMember left[second] secondMember (choose left[first])
      (selected left[first] firstMember).1 (selected left[first] firstMember).2
      (by simpa only [outputSame] using (selected left[second] secondMember).2)
    exact distinct.eq_of_getElem_eq firstBound' secondBound' valuesSame
  have subset : left.map choose ⊆ right := by
    intro output member
    obtain ⟨input, inputMember, same⟩ := List.mem_map.mp member
    subst output
    exact (selected input inputMember).1
  simpa only [List.length_map] using List.Nodup.length_le_of_subset mappedDistinct subset

/-- Equal live tuples force the same valuation at each live name. -/
theorem matching_same_values (left right : Nat → Term Symbol) (domains : List (Nat × Nat))
    (values : List (Term Symbol)) (first : TupleMatches left domains values) (second : TupleMatches right domains values) :
    ∀ entry ∈ domains, left entry.1 = right entry.1 := by
  have first := (tupleMatches_iff left domains values).mp first
  have second := (tupleMatches_iff right domains values).mp second
  exact List.map_inj_left.mp (first.symm.trans second)

/-- Equivalent solution valuations with mutually determined live coordinates have equal finite counts. -/
theorem solutionCount_equivalent (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (left right : Problem Symbol)
    (equivalent : ∀ assignment,
      ProblemHolds (fun node term => term ∈ language node) assignment left ↔
        ProblemHolds (fun node term => term ∈ language node) assignment right)
    (leftDetermined : ∀ first second,
      ProblemHolds (fun node term => term ∈ language node) first left →
      ProblemHolds (fun node term => term ∈ language node) second left →
      (∀ entry ∈ right.domains, first entry.1 = second entry.1) →
      ∀ entry ∈ left.domains, first entry.1 = second entry.1)
    (rightDetermined : ∀ first second,
      ProblemHolds (fun node term => term ∈ language node) first right →
      ProblemHolds (fun node term => term ∈ language node) second right →
      (∀ entry ∈ left.domains, first entry.1 = second entry.1) →
      ∀ entry ∈ right.domains, first entry.1 = second entry.1) :
    solutionCount language left = solutionCount language right := by
  let relation := fun old new => ∃ assignment,
    TupleMatches assignment left.domains old ∧ TupleMatches assignment right.domains new ∧
      ProblemHolds (fun node term => term ∈ language node) assignment left
  have forward : ∀ old ∈ solutionTuples language left, ∃ new ∈ solutionTuples language right, relation old new := by
    intro old member
    obtain ⟨assignment, matching, valid⟩ := (solutionTuples_spec language left old).mp member
    let new := right.domains.map fun entry => assignment entry.1
    have matchingNew : TupleMatches assignment right.domains new := (tupleMatches_iff ..).mpr rfl
    exact ⟨new, (solutionTuples_spec language right new).mpr ⟨assignment, matchingNew, (equivalent assignment).mp valid⟩,
      assignment, matching, matchingNew, valid⟩
  have backward : ∀ new ∈ solutionTuples language right, ∃ old ∈ solutionTuples language left, relation old new := by
    intro new member
    obtain ⟨assignment, matching, valid⟩ := (solutionTuples_spec language right new).mp member
    let old := left.domains.map fun entry => assignment entry.1
    have matchingOld : TupleMatches assignment left.domains old := (tupleMatches_iff ..).mpr rfl
    have validOld := (equivalent assignment).mpr valid
    exact ⟨old, (solutionTuples_spec language left old).mpr ⟨assignment, matchingOld, validOld⟩,
      assignment, matchingOld, matching, validOld⟩
  have leftUnique : ∀ first ∈ solutionTuples language left, ∀ second ∈ solutionTuples language left,
      ∀ new ∈ solutionTuples language right, relation first new → relation second new → first = second := by
    intro first _ second _ new _ ⟨a, am, an, av⟩ ⟨b, bm, bn, bv⟩
    have same := leftDetermined a b av bv (matching_same_values a b right.domains new an bn)
    exact ((tupleMatches_iff ..).mp am).trans ((List.map_inj_left.mpr same).trans ((tupleMatches_iff ..).mp bm).symm)
  have rightUnique : ∀ first ∈ solutionTuples language right, ∀ second ∈ solutionTuples language right,
      ∀ old ∈ solutionTuples language left, relation old first → relation old second → first = second := by
    intro first _ second _ old _ ⟨a, am, an, av⟩ ⟨b, bm, bn, bv⟩
    have same := rightDetermined a b ((equivalent a).mp av) ((equivalent b).mp bv)
      (matching_same_values a b left.domains old am bm)
    exact ((tupleMatches_iff ..).mp an).trans ((List.map_inj_left.mpr same).trans ((tupleMatches_iff ..).mp bn).symm)
  apply Nat.le_antisymm
  · exact relation_cardinality_le _ _ [] (solutionTuples_nodup language distinct left) relation forward leftUnique
  · exact relation_cardinality_le _ _ [] (solutionTuples_nodup language distinct right) (fun new old => relation old new) backward rightUnique

end MicroCFTA.SymbolicDriver
