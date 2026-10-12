import MicroCFTA.StaticCandidateRanks
import MicroCFTA.SupportJoin

/-!
# Candidate callbacks for finite source composites

N-way joins retain every child term under its private key wrapper.
Frequency choices use cumulative cardinalities in source branch order.
Closed enumerated terms remain exact while neighboring integer holes fill.
-/
namespace MicroCFTA.StaticCompositeCandidateRanks
open Language GeneratorCombinators IntegerTermViews StaticCandidateRanks

/-- The source argument chain has the product of its argument cardinalities. -/
def chainCount (sources : List (Source Symbol)) : Nat := (sources.map cardinality).prod

/-- The source chain rank uses each remaining chain cardinality as its radix. -/
def chainRank : List (Source Symbol) → List Nat → Nat
  | _ :: rest, rank :: ranks => Probability.pairRank (chainCount rest) rank (chainRank rest ranks)
  | _, _ => 0

/-- Execute chainRanks with the source key checks erased, as pointsStatic erases checked flags. -/
def chainCandidates : List (Source Symbol) → List (Term (Label Symbol)) → List Nat
  | [], [] => [0]
  | source :: rest, .node .argKeyed [_, term] :: terms =>
      productCandidates (chainCount rest) (candidates source .whole [term]) (chainCandidates rest terms)
  | _, _ => []

/-- The finite join reads its operation before the wrapped argument chain. -/
def joinChildren (operation : Source Symbol) (arguments : List (Source Symbol)) :
    List (Term (Label Symbol)) → List Nat
  | .node .centerKeyed (term :: _) :: terms =>
      productCandidates (chainCount arguments) (candidates operation .whole [term]) (chainCandidates arguments terms)
  | _ => []

/-- Execute the source n-way join callback for all three term views. -/
def joinCandidates (operation : Source Symbol) (arguments : List (Source Symbol)) :
    View → List (Term (Label Symbol)) → List Nat
  | .whole, [.node .joinN children] | .spine, [.node .joinN children] => joinChildren operation arguments children
  | .labelled, children => joinChildren operation arguments children
  | _, _ => []

/-- Private key leaves neither consume coordinates nor change under filling. -/
theorem fill_keys (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (component first count : Nat) :
    fillForest literal exactLabel point (SupportJoin.keys component first count) =
      (point, SupportJoin.keys component first count) := by
  induction count generalizing first with
  | zero => simp [SupportJoin.keys, fillForest]
  | succ count ih => simp [SupportJoin.keys, fillForest, fill, ih]

/-- Filling an argument wrapper changes only its selected argument term. -/
theorem fill_arguments (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (component first : Nat) (terms : List (Term (Label Symbol))) :
    fillForest literal exactLabel point (SupportJoin.arguments component first terms) =
      let filled := fillForest literal exactLabel point terms
      (filled.1, SupportJoin.arguments component first filled.2) := by
  induction terms generalizing point first with
  | nil => simp [SupportJoin.arguments, fillForest]
  | cons term terms ih => simp [SupportJoin.arguments, fillForest, fill, ih]

/-- Filling retains the number of terms in a forest. -/
theorem fill_length (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Term (Label Symbol))) :
    (fillForest literal exactLabel point terms).2.length = terms.length := by
  induction terms generalizing point with
  | nil => simp [fillForest]
  | cons term terms ih => simp [fillForest, ih]

/-- Source filling retains the n-way constructor, component keys, and argument order. -/
theorem fill_join (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (component : Nat) (operation : Term (Label Symbol))
    (arguments : List (Term (Label Symbol))) :
    fill literal exactLabel point (SupportJoin.joinTerm component operation arguments) =
      let first := fill literal exactLabel point operation
      let rest := fillForest literal exactLabel first.1 arguments
      (rest.1, SupportJoin.joinTerm component first.2 rest.2) := by
  simp [SupportJoin.joinTerm, fill, fillForest, fill_keys, fill_arguments, fill_length]

/-- Each selected argument survives its own callback at the correct coordinate suffix. -/
theorem chain_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (sources : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) sources chosen)
    (compatible : ∀ source ∈ sources, Compatible exactLabel source)
    (point : List Int) (component first : Nat) :
    chainRank sources (chosen.map Prod.fst) ∈
      chainCandidates sources (SupportJoin.arguments component first
        (fillForest literal exactLabel point (chosen.map Prod.snd)).2) := by
  induction selected generalizing point first with
  | nil => simp [chainRank, chainCandidates, fillForest, SupportJoin.arguments]
  | @cons source entry sources chosen selected rest ih =>
      simp only [List.map_cons, fillForest, SupportJoin.arguments, chainCandidates, chainRank]
      exact product_member _ _ _ _ _
        (candidate_complete literal exactLabel selected (compatible source (by simp)) point .whole)
        (ih (fun source member => compatible source (by simp [member])) _ (first + 1))

/-- The source chain radices place the selected arguments inside their product cardinality. -/
theorem chain_rank_bound (sources : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) sources chosen) :
    chainRank sources (chosen.map Prod.fst) < chainCount sources := by
  induction selected with
  | nil => simp [chainRank, chainCount]
  | cons selected rest ih =>
      simpa [chainRank, chainCount] using Probability.pairRank_lt (selected_bound selected) ih

/-- The selected operation and arguments remain a candidate at the actual mixed-radix join rank. -/
theorem join_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (operation : Source Symbol) (operationRank : Nat) (operationTerm : Term (Label Symbol))
    (operationSelected : Selected operation operationRank operationTerm)
    (operationCompatible : Compatible exactLabel operation)
    (arguments : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) arguments chosen)
    (compatible : ∀ source ∈ arguments, Compatible exactLabel source)
    (point : List Int) (component : Nat) (view : View) :
    Probability.pairRank (chainCount arguments) operationRank (chainRank arguments (chosen.map Prod.fst)) ∈
      joinCandidates operation arguments view
        (project view (fill literal exactLabel point
          (SupportJoin.joinTerm component operationTerm (chosen.map Prod.snd))).2) := by
  rw [fill_join]
  have included := product_member (chainCount arguments) _ _ operationRank _
    (candidate_complete literal exactLabel operationSelected operationCompatible point .whole)
    (chain_complete literal exactLabel arguments chosen selected compatible
      (fill literal exactLabel point operationTerm).1 component 0)
  cases view <;> simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren, SupportJoin.joinTerm, joinCandidates, joinChildren] using included

/-- One frequency branch reads the private choice wrapper except in labelled views. -/
def branchCandidates (source : Source Symbol) (branch offset : Nat) :
    View → List (Term (Label Symbol)) → List Nat
  | .labelled, wanted => (candidates source .labelled wanted).map (offset + ·)
  | _, [.node (.choice found) [term]] =>
      if found = branch then (candidates source .whole [term]).map (offset + ·) else []
  | _, _ => []

/-- Source branch order supplies both choice indices and cumulative cardinality offsets. -/
def frequencyCandidates (first offset : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  match sources with
  | [] => []
  | source :: rest => branchCandidates source first offset view wanted ++
      frequencyCandidates (first + 1) (offset + cardinality source) rest view wanted

/-- One selected frequency alternative retains its original rank with the branch offset. -/
theorem branch_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (source : Source Symbol) (rank : Nat) (term : Term (Label Symbol))
    (selected : Selected source rank term) (compatible : Compatible exactLabel source)
    (point : List Int) (view : View) (branch offset : Nat) :
    offset + rank ∈ branchCandidates source branch offset view
      (project view (fill literal exactLabel point (.node (.choice branch) [term])).2) := by
  have whole := candidate_complete literal exactLabel selected compatible point .whole
  have closed := candidate_complete literal exactLabel selected compatible point .labelled
  simp only [project] at whole closed
  cases view <;> simp [branchCandidates, project, fill, fillForest, labelled, spine,
    SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, whole, closed]

/-- Every alternative in an arbitrary-length choice retains the sum of all preceding cardinalities. -/
theorem frequency_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (before after : List (Source Symbol)) (source : Source Symbol)
    (rank : Nat) (term : Term (Label Symbol))
    (selected : Selected source rank term) (compatible : Compatible exactLabel source)
    (point : List Int) (view : View) (first offset : Nat) :
    offset + (before.map cardinality).sum + rank ∈
      frequencyCandidates first offset (before ++ source :: after) view
        (project view (fill literal exactLabel point
          (.node (.choice (first + before.length)) [term])).2) := by
  induction before generalizing first offset with
  | nil =>
      simpa [frequencyCandidates] using List.mem_append_left
        (frequencyCandidates (first + 1) (offset + cardinality source) after view
          (project view (fill literal exactLabel point (.node (.choice first) [term])).2))
        (branch_complete literal exactLabel source rank term selected compatible point view first offset)
  | cons head rest ih =>
      have member := ih (first + 1) (offset + cardinality head)
      apply List.mem_append_right
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member

/-- Closed components have no placeholders and their primitive user labels cannot specialize. -/
def Inert (exactLabel : List Int → Symbol → Symbol) : Term (Label Symbol) → Prop
  | .node label children =>
      label ≠ .placeholder ∧
      (∀ symbol, label = .user symbol → ∀ point, exactLabel point symbol = symbol) ∧
      ∀ child ∈ children, Inert exactLabel child

mutual
/-- Filling a closed component consumes no neighboring coordinates and changes no term. -/
theorem fill_inert (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (Label Symbol)) (inert : Inert exactLabel term) :
    fill literal exactLabel point term = (point, term) := by
  cases term with
  | node label children =>
      simp only [Inert] at inert
      have childrenFixed := fillForest_inert literal exactLabel point children inert.2.2
      cases label with
      | placeholder => exact False.elim (inert.1 rfl)
      | user symbol => simp [fill, childrenFixed, inert.2.1 symbol rfl point]
      | _ => simp [fill, childrenFixed]
termination_by sizeOf term

/-- A closed forest also leaves the coordinate suffix unchanged. -/
theorem fillForest_inert (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Term (Label Symbol)))
    (inert : ∀ term ∈ terms, Inert exactLabel term) :
    fillForest literal exactLabel point terms = (point, terms) := by
  cases terms with
  | nil => simp [fillForest]
  | cons term terms =>
      simp [fillForest, fill_inert literal exactLabel point term (inert term (by simp)),
        fillForest_inert literal exactLabel point terms (fun term member => inert term (by simp [member]))]
termination_by sizeOf terms
end

/-- The actual enumerated callback scans every stored term in its retained rank order. -/
def enumeratedCandidates [DecidableEq Symbol] (terms : List (Term (Label Symbol)))
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (List.range terms.length).filter fun rank =>
    ((terms[rank]?).map (fun term => decide (project view term = wanted))).getD false

/-- A closed enumerated outcome retains its rank after any neighboring point is filled. -/
theorem enumerated_complete [DecidableEq Symbol]
    (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (terms : List (Term (Label Symbol))) (rank : Nat) (term : Term (Label Symbol))
    (selected : terms[rank]? = some term) (inert : Inert exactLabel term)
    (point : List Int) (view : View) :
    rank ∈ enumeratedCandidates terms view (project view (fill literal exactLabel point term).2) := by
  have bounded := (List.getElem?_eq_some_iff.mp selected).1
  simp only [enumeratedCandidates, List.mem_filter, List.mem_range]
  refine ⟨bounded, ?_⟩
  rw [selected]
  simp [fill_inert literal exactLabel point term inert]

/-- The imported source passes a singleton opaque root to its retained term inverse. -/
def opaqueCandidates (rankTerm : Term (Label Symbol) → List Nat)
    (_view : View) : List (Term (Label Symbol)) → List Nat
  | [term] => rankTerm term
  | _ => []

/-- Closed imported roots keep every rank provided by the underlying exact term inverse. -/
theorem opaque_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (rankTerm : Term (Label Symbol) → List Nat) (symbol : Symbol)
    (children : List (Term (Label Symbol))) (rank : Nat)
    (selected : rank ∈ rankTerm (.node (.user symbol) children))
    (inert : Inert exactLabel (.node (.user symbol) children)) (point : List Int) (view : View) :
    rank ∈ opaqueCandidates rankTerm view
      (project view (fill literal exactLabel point (.node (.user symbol) children)).2) := by
  rw [fill_inert literal exactLabel point _ inert]
  simpa [project_user, opaqueCandidates] using selected

/-- Arbitrary open enumerated terms do not have the closed-source guarantee. -/
theorem open_enumerated_counterexample :
    let hole : Term (Label Int) := .node .placeholder []
    enumeratedCandidates [hole] .whole
      (project .whole (fill id (fun _ symbol => symbol) [0] hole).2) = [] := by
  decide +kernel

end MicroCFTA.StaticCompositeCandidateRanks
