import MicroCFTA.StaticRankQueryExact
import MicroCFTA.StaticCompositeCandidateRanks
import MicroCFTA.SymbolRelabel

/-!
# Checked certificates for finite joins and frequency choices

Chain callbacks check argument payloads but do not check keys. The join's
separate source key checker supplies the complete canonical wrapper shape.
-/
namespace MicroCFTA.CompositeCheckedRanks
open Language GeneratorCombinators IntegerTermViews StaticCandidateRanks StaticCheckedRanks
open StaticCompositeCandidateRanks StaticRankQueryExact

/-- The source isKey checks the component, argument position, and leaf arity. -/
def isKey (component position : Nat) : Term (Label Symbol) → Bool
  | .node (.argKey foundComponent foundPosition) [] =>
      decide (foundComponent = component) && decide (foundPosition = position)
  | _ => false

/-- The source isArgument requires two children and checks the first as a key. -/
def isArgument (component position : Nat) : Term (Label Symbol) → Bool
  | .node .argKeyed [key, _] => isKey component position key
  | _ => false

/-- Zip with consecutive argument positions and require every source check to pass. -/
def allAt (check : Nat → Item → Bool) : Nat → List Item → Bool
  | _, [] => true
  | first, item :: rest => check first item && allAt check (first + 1) rest

/-- Exact joinKeysMatch dispatch, including the independent center and argument checks. -/
def joinKeysMatch (component : Nat) (keys nodes : List (Term (Label Symbol))) : Bool :=
  decide (keys.length = nodes.length) && allAt (isKey component) 0 keys && allAt (isArgument component) 0 nodes

/-- A successful key test reads the precise private leaf, not just a matching name. -/
theorem isKey_exact (component position : Nat) (term : Term (Label Symbol)) :
    isKey component position term = true ↔ term = .node (.argKey component position) [] := by
  unfold isKey
  split
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Term.node.injEq, Label.argKey.injEq, and_true]
  · rename_i absent
    constructor
    · intro impossible; cases impossible
    · intro same; subst term; exact False.elim (absent component position rfl)

/-- A successful argument test fixes its wrapper and key while retaining its payload. -/
theorem isArgument_exact (component position : Nat) (term : Term (Label Symbol)) :
    isArgument component position term = true ↔
      ∃ payload, term = .node .argKeyed [.node (.argKey component position) [], payload] := by
  unfold isArgument
  split
  · rename_i key payload
    rw [isKey_exact]
    constructor
    · intro same; exact ⟨payload, by rw [same]⟩
    · rintro ⟨other, same⟩
      exact (List.cons.inj (Term.node.inj same).2).1
  · rename_i absent
    constructor
    · intro impossible; cases impossible
    · rintro ⟨payload, same⟩
      subst term
      exact False.elim (absent _ payload rfl)

/-- The complete center-key sequence is exactly the constructor's positional key sequence. -/
theorem keys_exact (component first : Nat) (keys : List (Term (Label Symbol))) :
    allAt (isKey component) first keys = true ↔ keys = SupportJoin.keys component first keys.length := by
  induction keys generalizing first with
  | nil => simp [allAt, SupportJoin.keys]
  | cons key rest ih =>
      simp only [allAt, Bool.and_eq_true, isKey_exact, ih, List.length_cons, SupportJoin.keys, List.cons.injEq]

/-- Argument wrapper checks recover every payload and its exact positional wrapper. -/
theorem arguments_exact (component first : Nat) (nodes : List (Term (Label Symbol))) :
    allAt (isArgument component) first nodes = true ↔
      ∃ terms, nodes = SupportJoin.arguments component first terms := by
  induction nodes generalizing first with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons node rest ih =>
      simp only [allAt, Bool.and_eq_true, isArgument_exact, ih]
      constructor
      · rintro ⟨⟨payload, rfl⟩, ⟨terms, rfl⟩⟩
        exact ⟨payload :: terms, rfl⟩
      · rintro ⟨terms, same⟩
        cases terms with
        | nil => simp [SupportJoin.arguments] at same
        | cons payload terms =>
            have parts := List.cons.inj same
            exact ⟨⟨payload, parts.1⟩, ⟨terms, parts.2⟩⟩

/-- Canonical argument wrapping does not change the number of arguments. -/
theorem arguments_length (component first : Nat) (terms : List (Term (Label Symbol))) :
    (SupportJoin.arguments component first terms).length = terms.length := by
  induction terms generalizing first with
  | nil => rfl
  | cons term rest ih => simp [SupportJoin.arguments, ih]

/-- The source's complete key checker is equivalent to the exact join constructor's key shape. -/
theorem join_keys_exact (component : Nat) (keys nodes : List (Term (Label Symbol))) :
    joinKeysMatch component keys nodes = true ↔
      ∃ terms, keys = SupportJoin.keys component 0 terms.length ∧ nodes = SupportJoin.arguments component 0 terms := by
  simp only [joinKeysMatch, Bool.and_eq_true, decide_eq_true_eq, keys_exact, arguments_exact]
  constructor
  · rintro ⟨⟨lengths, keysEq⟩, terms, nodesEq⟩
    refine ⟨terms, ?_, nodesEq⟩
    rw [keysEq, lengths, nodesEq, arguments_length]
  · rintro ⟨terms, keysEq, nodesEq⟩
    have lengths : keys.length = nodes.length := by
      have keyLength : ∀ first, (SupportJoin.keys (Symbol := Symbol) component first terms.length).length = terms.length := by
        induction terms.length with
        | zero => intro first; rfl
        | succ count ih => intro first; simp [SupportJoin.keys, ih]
      rw [keysEq, nodesEq, arguments_length, keyLength]
    refine ⟨⟨lengths, ?_⟩, terms, nodesEq⟩
    rw [lengths, nodesEq, arguments_length]
    exact keysEq

/-- Chain flags follow checkedProduct and intentionally do not inspect the argument keys. -/
def chainRanks [DecidableEq Symbol] : List (Source Symbol) → List (Term (Label Symbol)) → List Checked
  | [] => fun nodes => match nodes with | [] => [(0, true)] | _ => []
  | source :: rest => fun nodes => match nodes with
      | .node .argKeyed [_, term] :: terms =>
          product (chainCount rest) (ranks source .whole [term]) (chainRanks rest terms)
      | _ => []

/-- Execute the source chain selector with suffix-cardinality radices. -/
def selectChain : List (Source Symbol) → Nat → Option (List (Term (Label Symbol)))
  | [], _ => some []
  | source :: rest, rank => do
      let first ← StaticCandidateRanks.select source (rank / chainCount rest)
      let tail ← selectChain rest (rank % chainCount rest)
      pure (first :: tail)

/-- The chosen payload list is reproduced exactly by the actual chain selector. -/
theorem select_chain_complete (sources : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) sources chosen) :
    selectChain sources (chainRank sources (chosen.map Prod.fst)) = some (chosen.map Prod.snd) := by
  induction selected with
  | nil => rfl
  | @cons source entry sources chosen selected rest ih =>
      have split := Probability.split_pair (left := entry.1) (chain_rank_bound sources chosen rest)
      have first := congrArg Prod.fst split
      have tail := congrArg Prod.snd split
      simp only [Probability.splitRank] at first tail
      simp [selectChain, chainRank, first, tail, select_complete selected, ih, Bind.bind, Option.bind]

/-- A chain's true flags select exactly the payloads once the separate key check supplies canonical wrappers. -/
theorem chain_checked [DecidableEq Symbol] (sources : List (Source Symbol)) (component first : Nat)
    (terms : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ chainRanks sources (SupportJoin.arguments component first terms)) (checked : candidate.2 = true) :
    ∃ chosen, All₂ (fun source entry => Selected source entry.1 entry.2) sources chosen ∧
      chosen.map Prod.snd = terms ∧ candidate.1 = chainRank sources (chosen.map Prod.fst) := by
  induction sources generalizing first terms candidate with
  | nil =>
      cases terms with
      | nil =>
          have same : candidate = (0, true) := by simpa [chainRanks, SupportJoin.arguments] using member
          exact ⟨[], .nil, rfl, by simp [same, chainRank]⟩
      | cons term rest => simp [SupportJoin.arguments, chainRanks] at member
  | cons source sources ih =>
      cases terms with
      | nil => simp [SupportJoin.arguments, chainRanks] at member
      | cons term terms =>
          obtain ⟨left, leftMember, right, rightMember, leftChecked, rightChecked, rankEq⟩ :=
            product_checked _ _ _ candidate member checked
          obtain ⟨value, selected, view⟩ := checked_sound source .whole [term] left leftMember leftChecked
          have same := whole_eq value term view
          subst value
          obtain ⟨chosen, selectedTail, sameTerms, sameRank⟩ := ih (first + 1) terms right rightMember rightChecked
          refine ⟨(left.1, term) :: chosen, .cons selected selectedTail, by simp [sameTerms], ?_⟩
          simp [chainRank, rankEq, sameRank]

/-- Every selected chain supplies a true candidate in argument order. -/
theorem chain_certified_complete [DecidableEq Symbol]
    (sources : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) sources chosen)
    (compatible : ∀ source ∈ sources, MatchesSelf source) (component first : Nat) :
    (chainRank sources (chosen.map Prod.fst), true) ∈ chainRanks sources (SupportJoin.arguments component first (chosen.map Prod.snd)) := by
  induction selected generalizing first with
  | nil => simp [chainRanks, chainRank, SupportJoin.arguments]
  | @cons source entry sources chosen selected rest ih =>
      exact product_member_true _ _ _ _ _
        (certified_complete selected (compatible source (by simp)) .whole)
        (ih (fun source member => compatible source (by simp [member])) (first + 1))

/-- The source join combines operation and argument flags with the independent key certificate. -/
def joinChildren [DecidableEq Symbol] (component : Nat) (operation : Source Symbol) (arguments : List (Source Symbol)) :
    List (Term (Label Symbol)) → List Checked
  | .node .centerKeyed (term :: keys) :: nodes =>
      (product (chainCount arguments) (ranks operation .whole [term]) (chainRanks arguments nodes)).map
        (fun entry => (entry.1, entry.2 && joinKeysMatch component keys nodes))
  | _ => []

/-- Exact source n-way join callback dispatch over whole, spine, and labelled views. -/
def joinRanks [DecidableEq Symbol] (component : Nat) (operation : Source Symbol) (arguments : List (Source Symbol)) :
    View → List (Term (Label Symbol)) → List Checked
  | .whole | .spine => fun wanted => match wanted with
      | [.node .joinN children] => joinChildren component operation arguments children
      | _ => []
  | .labelled => joinChildren component operation arguments

/-- Execute the source join selector, retaining its range check and exact private key term. -/
def selectJoin (component : Nat) (operation : Source Symbol) (arguments : List (Source Symbol)) (rank : Nat) :
    Option (Term (Label Symbol)) :=
  if rank < cardinality operation * chainCount arguments then do
    let first ← StaticCandidateRanks.select operation (rank / chainCount arguments)
    let rest ← selectChain arguments (rank % chainCount arguments)
    pure (SupportJoin.joinTerm component first rest)
  else none

/-- A certified join child list is exactly the selected constructor's complete child list. -/
theorem join_children_checked [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (arguments : List (Source Symbol)) (children : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ joinChildren component operation arguments children) (checked : candidate.2 = true) :
    ∃ term, selectJoin component operation arguments candidate.1 = some term ∧ project .labelled term = children := by
  unfold joinChildren at member
  split at member
  · rename_i operationTerm keys nodes
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    subst candidate
    have flags : original.2 = true ∧ joinKeysMatch component keys nodes = true := by
      simpa only [Bool.and_eq_true] using checked
    obtain ⟨terms, keysEq, nodesEq⟩ := (join_keys_exact component keys nodes).mp flags.2
    obtain ⟨left, leftMember, right, rightMember, leftChecked, rightChecked, rankEq⟩ :=
      product_checked _ _ _ original present flags.1
    obtain ⟨value, selected, view⟩ := checked_sound operation .whole [operationTerm] left leftMember leftChecked
    have sameValue := whole_eq value operationTerm view
    subst value
    rw [nodesEq] at rightMember
    obtain ⟨chosen, selectedTail, termsEq, rightEq⟩ := chain_checked arguments component 0 terms right rightMember rightChecked
    have argumentBound := chain_rank_bound arguments chosen selectedTail
    have bounded := Probability.pairRank_lt (selected_bound selected) argumentBound
    have split := Probability.split_pair (left := left.1) argumentBound
    have first := congrArg Prod.fst split
    have tail := congrArg Prod.snd split
    simp only [Probability.splitRank] at first tail
    refine ⟨SupportJoin.joinTerm component operationTerm terms, ?_, ?_⟩
    · simp [selectJoin, rankEq, rightEq, bounded, first, tail, select_complete selected,
        select_chain_complete arguments chosen selectedTail, termsEq, Bind.bind, Option.bind]
    · simp [SupportJoin.joinTerm, project, labelled, keysEq, nodesEq]
  · simp at member

/-- A true source join flag certifies exact successful replay in every request view. -/
theorem join_checked [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (arguments : List (Source Symbol)) (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ joinRanks component operation arguments view wanted) (checked : candidate.2 = true) :
    ∃ term, selectJoin component operation arguments candidate.1 = some term ∧ project view term = wanted := by
  cases view with
  | labelled => exact join_children_checked component operation arguments wanted candidate member checked
  | whole | spine =>
      simp only [joinRanks] at member
      split at member
      · rename_i children
        obtain ⟨term, selected, same⟩ := join_children_checked component operation arguments children candidate member checked
        unfold selectJoin at selected
        split at selected
        · cases first : StaticCandidateRanks.select operation (candidate.1 / chainCount arguments) with
          | none => simp [first, Bind.bind, Option.bind] at selected
          | some value => cases tail : selectChain arguments (candidate.1 % chainCount arguments) with
            | none => simp [first, tail, Bind.bind, Option.bind] at selected
            | some terms =>
                have termEq : term = SupportJoin.joinTerm component value terms := by
                  simpa [first, tail, Bind.bind, Option.bind, Pure.pure] using selected.symm
                subst term
                refine ⟨SupportJoin.joinTerm component value terms, ?_, ?_⟩
                · simp [selectJoin, Bind.bind, Option.bind, *]
                · simpa [SupportJoin.joinTerm, project, labelled, spine, SupportTerms.applicationLeftChildren,
                    SupportTerms.applicationTermChildren] using congrArg (fun children => [Term.node Label.joinN children]) same
        · simp at selected
      · simp at member

/-- Every selected operation and argument tuple supplies the join's fully checked candidate. -/
theorem join_certified_complete [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (operationRank : Nat) (operationTerm : Term (Label Symbol))
    (operationSelected : Selected operation operationRank operationTerm) (operationSelf : MatchesSelf operation)
    (arguments : List (Source Symbol)) (chosen : List (Nat × Term (Label Symbol)))
    (selected : All₂ (fun source entry => Selected source entry.1 entry.2) arguments chosen)
    (compatible : ∀ source ∈ arguments, MatchesSelf source) (view : View) :
    (Probability.pairRank (chainCount arguments) operationRank (chainRank arguments (chosen.map Prod.fst)), true) ∈
      joinRanks component operation arguments view
        (project view (SupportJoin.joinTerm component operationTerm (chosen.map Prod.snd))) := by
  have keysChecked : joinKeysMatch component (SupportJoin.keys component 0 (chosen.map Prod.snd).length)
      (SupportJoin.arguments component 0 (chosen.map Prod.snd)) = true :=
    (join_keys_exact component _ _).mpr ⟨chosen.map Prod.snd, rfl, rfl⟩
  have tuple := product_member_true (chainCount arguments) _ _ operationRank _
    (certified_complete operationSelected operationSelf .whole)
    (chain_certified_complete arguments chosen selected compatible component 0)
  have certified :
      (Probability.pairRank (chainCount arguments) operationRank (chainRank arguments (chosen.map Prod.fst)), true) ∈
        joinChildren component operation arguments
          (.node .centerKeyed (operationTerm :: SupportJoin.keys component 0 (chosen.map Prod.snd).length) ::
            SupportJoin.arguments component 0 (chosen.map Prod.snd)) := by
    simp only [joinChildren]
    refine List.mem_map.mpr ⟨_, tuple, ?_⟩
    simp only [Bool.true_and, keysChecked]
  cases view <;> simpa only [joinRanks, project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren, SupportJoin.joinTerm, Option.getD_none] using certified

/-- Removing chain flags returns the exact previously modeled argument candidate loop. -/
theorem chain_erasure [DecidableEq Symbol] (sources : List (Source Symbol)) (nodes : List (Term (Label Symbol))) :
    (chainRanks sources nodes).map Prod.fst = chainCandidates sources nodes := by
  induction sources generalizing nodes with
  | nil => cases nodes <;> rfl
  | cons source sources ih =>
      simp only [chainRanks]
      split <;> simp_all [chainCandidates, product_erasure, erasure]

/-- Removing join flags retains every candidate, including candidates with incorrect key values. -/
theorem join_erasure [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (arguments : List (Source Symbol)) (view : View) (wanted : List (Term (Label Symbol))) :
    (joinRanks component operation arguments view wanted).map Prod.fst = joinCandidates operation arguments view wanted := by
  have childrenExact : ∀ children,
      (joinChildren component operation arguments children).map Prod.fst =
        StaticCompositeCandidateRanks.joinChildren operation arguments children := by
    intro children
    unfold joinChildren
    split
    · simp only [StaticCompositeCandidateRanks.joinChildren, List.map_map, Function.comp_def]
      rw [product_erasure, erasure, chain_erasure]
    · simp_all [StaticCompositeCandidateRanks.joinChildren]
  cases view with
  | labelled => exact childrenExact wanted
  | whole | spine =>
      simp only [joinRanks]
      split <;> simp_all [joinCandidates]

/-- All chain candidates are strictly ordered and within the suffix product cardinality. -/
theorem chain_valid [DecidableEq Symbol] (sources : List (Source Symbol)) (nodes : List (Term (Label Symbol))) :
    ValidRanks (chainCount sources) ((chainRanks sources nodes).map Prod.fst) := by
  induction sources generalizing nodes with
  | nil => cases nodes <;> simp [chainRanks, chainCount, ValidRanks]
  | cons source sources ih =>
      simp only [chainRanks]
      split
      · rw [product_erasure]
        simpa [chainCount] using valid_product _ _ _ _ (callbacks_valid source .whole _) (ih _)
      · exact valid_nil _

/-- Key checks change certificates but preserve strict join candidate order and cardinality bounds. -/
theorem join_valid [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (arguments : List (Source Symbol)) (view : View) (wanted : List (Term (Label Symbol))) :
    ValidRanks (cardinality operation * chainCount arguments)
      ((joinRanks component operation arguments view wanted).map Prod.fst) := by
  have childrenValid : ∀ children, ValidRanks (cardinality operation * chainCount arguments)
      ((joinChildren component operation arguments children).map Prod.fst) := by
    intro children
    unfold joinChildren
    split
    · simp only [List.map_map, Function.comp_def]
      rw [product_erasure]
      exact valid_product _ _ _ _ (callbacks_valid operation .whole _) (chain_valid arguments _)
    · exact valid_nil _
  cases view with
  | labelled => exact childrenValid wanted
  | whole | spine =>
      simp only [joinRanks]
      split
      · exact childrenValid _
      · exact valid_nil _

/-- One source frequency branch preserves the child flag while it adds its cumulative offset. -/
def branchRanks [DecidableEq Symbol] (source : Source Symbol) (branch start : Nat) :
    View → List (Term (Label Symbol)) → List Checked
  | .labelled => fun wanted => offset start (ranks source .labelled wanted)
  | .whole | .spine => fun wanted => match wanted with
      | [.node (.choice found) [term]] => if found = branch then offset start (ranks source .whole [term]) else []
      | _ => []

/-- Arbitrary retained frequency alternatives occur in source order with cumulative cardinality offsets. -/
def frequencyRanks [DecidableEq Symbol] (first start : Nat) :
    List (Source Symbol) → View → List (Term (Label Symbol)) → List Checked
  | [], _, _ => []
  | source :: rest, view, wanted => branchRanks source first start view wanted ++
      frequencyRanks (first + 1) (start + cardinality source) rest view wanted

/-- A certified frequency branch replays its selected child and exact private choice view. -/
theorem branch_checked [DecidableEq Symbol] (source : Source Symbol) (branch start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ branchRanks source branch start view wanted) (checked : candidate.2 = true) :
    ∃ rank term, candidate.1 = start + rank ∧ Selected source rank term ∧
      project view (.node (.choice branch) [term]) = wanted := by
  cases view with
  | labelled =>
      obtain ⟨child, childMember, childChecked, rankEq⟩ := offset_checked start _ candidate member checked
      obtain ⟨term, selected, same⟩ := checked_sound source .labelled wanted child childMember childChecked
      exact ⟨child.1, term, rankEq, selected, same⟩
  | whole | spine =>
      simp only [branchRanks] at member
      split at member
      · rename_i found term
        split at member
        · next branchEq =>
          obtain ⟨child, childMember, childChecked, rankEq⟩ := offset_checked start _ candidate member checked
          obtain ⟨value, selected, same⟩ := checked_sound source .whole [term] child childMember childChecked
          have termEq := whole_eq value term same
          refine ⟨child.1, value, rankEq, selected, ?_⟩
          simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, termEq, branchEq]
        · simp at member
      · simp at member

/-- A certified arbitrary frequency result retains one exact source alternative and its full prefix offset. -/
theorem frequency_checked_origin [DecidableEq Symbol] (first start : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ frequencyRanks first start sources view wanted) (checked : candidate.2 = true) :
    ∃ before source after rank term, sources = before ++ source :: after ∧ Selected source rank term ∧
      candidate.1 = start + (before.map cardinality).sum + rank ∧
      project view (.node (.choice (first + before.length)) [term]) = wanted := by
  induction sources generalizing first start with
  | nil => simp [frequencyRanks] at member
  | cons source rest ih =>
      rcases List.mem_append.mp member with here | later
      · obtain ⟨rank, term, rankEq, selected, viewEq⟩ := branch_checked source first start view wanted candidate here checked
        exact ⟨[], source, rest, rank, term, rfl, selected, by simpa using rankEq, by simpa using viewEq⟩
      · obtain ⟨before, chosen, after, rank, term, parts, selected, rankEq, viewEq⟩ := ih (first + 1) _ later
        refine ⟨source :: before, chosen, after, rank, term, by simp [parts], selected, ?_, ?_⟩
        · simpa [List.map_cons, List.sum_cons, Nat.add_assoc] using rankEq
        · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using viewEq

/-- The source selector chooses the first cumulative cardinality block containing the rank. -/
def selectFrequency (first : Nat) : List (Source Symbol) → Nat → Option (Term (Label Symbol))
  | [], _ => none
  | source :: rest, rank =>
      if rank < cardinality source then
        (StaticCandidateRanks.select source rank).map (fun term => .node (.choice first) [term])
      else selectFrequency (first + 1) rest (rank - cardinality source)

/-- Every original frequency member is replayed at the sum of its preceding cardinalities. -/
theorem select_frequency_member (first : Nat) (before after : List (Source Symbol)) (source : Source Symbol)
    (rank : Nat) (term : Term (Label Symbol)) (selected : Selected source rank term) :
    selectFrequency first (before ++ source :: after) ((before.map cardinality).sum + rank) =
      some (.node (.choice (first + before.length)) [term]) := by
  induction before generalizing first with
  | nil => simp [selectFrequency, selected_bound selected, select_complete selected]
  | cons head rest ih =>
      have outside : ¬cardinality head + (rest.map cardinality).sum + rank < cardinality head := by omega
      simp only [List.cons_append, List.map_cons, List.sum_cons, selectFrequency, ite_eq_right outside]
      have indexEq : cardinality head + (rest.map cardinality).sum + rank - cardinality head =
          (rest.map cardinality).sum + rank := by omega
      rw [indexEq]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (first + 1)

/-- Every true arbitrary frequency flag certifies successful exact selection in its requested view. -/
theorem frequency_checked [DecidableEq Symbol] (first start : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ frequencyRanks first start sources view wanted) (checked : candidate.2 = true) :
    start ≤ candidate.1 ∧ ∃ term, selectFrequency first sources (candidate.1 - start) = some term ∧ project view term = wanted := by
  obtain ⟨before, source, after, rank, term, parts, selected, rankEq, viewEq⟩ :=
    frequency_checked_origin first start sources view wanted candidate member checked
  refine ⟨by omega, .node (.choice (first + before.length)) [term], ?_, viewEq⟩
  rw [parts, rankEq]
  simpa [Nat.add_assoc] using select_frequency_member first before after source rank term selected

/-- Every source member supplies a certified candidate in its retained branch. -/
theorem branch_certified_complete [DecidableEq Symbol] (source : Source Symbol) (branch start rank : Nat)
    (term : Term (Label Symbol)) (selected : Selected source rank term) (compatible : MatchesSelf source) (view : View) :
    (start + rank, true) ∈ branchRanks source branch start view (project view (.node (.choice branch) [term])) := by
  cases view <;> simp only [branchRanks, project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren, Option.getD_none, ↓reduceIte]
  all_goals exact List.mem_map.mpr ⟨(rank, true), certified_complete selected compatible _, rfl⟩

/-- All retained alternatives remain certified candidates at their exact cumulative source offsets. -/
theorem frequency_certified_complete [DecidableEq Symbol]
    (before after : List (Source Symbol)) (source : Source Symbol) (rank : Nat) (term : Term (Label Symbol))
    (selected : Selected source rank term) (compatible : MatchesSelf source) (view : View) (first start : Nat) :
    (start + (before.map cardinality).sum + rank, true) ∈
      frequencyRanks first start (before ++ source :: after) view
        (project view (.node (.choice (first + before.length)) [term])) := by
  induction before generalizing first start with
  | nil =>
      simpa [frequencyRanks] using (List.mem_append_left _
        (branch_certified_complete source first start rank term selected compatible view))
  | cons head rest ih =>
      apply List.mem_append_right
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1) (start + cardinality head)

/-- Branch erasure preserves the original candidate dispatch and offset arithmetic. -/
theorem branch_erasure [DecidableEq Symbol] (source : Source Symbol) (branch start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) :
    (branchRanks source branch start view wanted).map Prod.fst = branchCandidates source branch start view wanted := by
  cases view with
  | labelled => simp [branchRanks, branchCandidates, offset_erasure, erasure]
  | whole | spine =>
      simp only [branchRanks]
      split
      · split <;> simp_all [branchCandidates, offset_erasure, erasure]
      · simp_all [branchCandidates]

/-- Arbitrary frequency flags erase to the already verified cumulative candidate callback. -/
theorem frequency_erasure [DecidableEq Symbol] (first start : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) :
    (frequencyRanks first start sources view wanted).map Prod.fst = frequencyCandidates first start sources view wanted := by
  induction sources generalizing first start with
  | nil => rfl
  | cons source rest ih => simp [frequencyRanks, frequencyCandidates, branch_erasure, ih]

/-- One frequency branch is ordered and lies inside its cumulative bound. -/
theorem branch_valid [DecidableEq Symbol] (source : Source Symbol) (branch start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) :
    ValidRanks (start + cardinality source) ((branchRanks source branch start view wanted).map Prod.fst) := by
  have shifted : ∀ view wanted, ValidRanks (start + cardinality source) ((offset start (ranks source view wanted)).map Prod.fst) := by
    intro view wanted
    rw [offset_erasure]
    exact valid_offset _ _ _ (callbacks_valid source view wanted)
  cases view with
  | labelled => exact shifted _ _
  | whole | spine =>
      simp only [branchRanks]
      split
      · split
        · exact shifted _ _
        · exact valid_nil _
      · exact valid_nil _

/-- Every branch candidate lies at or above its source offset, including unchecked candidates. -/
theorem branch_lower [DecidableEq Symbol] (source : Source Symbol) (branch start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ branchRanks source branch start view wanted) : start ≤ candidate.1 := by
  have shifted : ∀ rows, candidate ∈ offset start rows → start ≤ candidate.1 := by
    intro rows member
    obtain ⟨original, _, same⟩ := List.mem_map.mp member
    subst candidate
    omega
  cases view with
  | labelled => exact shifted _ member
  | whole | spine =>
      simp only [branchRanks] at member
      split at member
      · split at member
        · exact shifted _ member
        · simp at member
      · simp at member

/-- Each subsequent frequency block starts after all cardinalities already visited. -/
theorem frequency_lower [DecidableEq Symbol] (first start : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ frequencyRanks first start sources view wanted) : start ≤ candidate.1 := by
  induction sources generalizing first start with
  | nil => simp [frequencyRanks] at member
  | cons source rest ih =>
      rcases List.mem_append.mp member with here | later
      · exact branch_lower source first start view wanted candidate here
      · have lower := ih (first + 1) (start + cardinality source) later
        omega

/-- Every arbitrary frequency callback is strictly ascending and within its total cumulative cardinality. -/
theorem frequency_valid [DecidableEq Symbol] (first start : Nat) (sources : List (Source Symbol))
    (view : View) (wanted : List (Term (Label Symbol))) :
    ValidRanks (start + (sources.map cardinality).sum) ((frequencyRanks first start sources view wanted).map Prod.fst) := by
  induction sources generalizing first start with
  | nil => exact valid_nil _
  | cons source rest ih =>
      have left := branch_valid source first start view wanted
      have right := ih (first + 1) (start + cardinality source)
      simp only [frequencyRanks, List.map_append, List.map_cons, List.sum_cons]
      constructor
      · apply List.pairwise_append.mpr
        refine ⟨left.1, right.1, ?_⟩
        intro before beforeMember after afterMember
        have bounded := left.2 before beforeMember
        obtain ⟨candidate, candidateMember, same⟩ := List.mem_map.mp afterMember
        have lower := frequency_lower (first + 1) (start + cardinality source) rest view wanted candidate candidateMember
        omega
      · intro rank member
        rcases List.mem_append.mp member with here | later
        · have bounded := left.2 rank here; omega
        · have bounded := right.2 rank later; omega

/-- The source enumerated callback certifies every retained full-view comparison. -/
def enumeratedRanks [DecidableEq Symbol] (terms : List (Term (Label Symbol))) (view : View)
    (wanted : List (Term (Label Symbol))) : List Checked :=
  (enumeratedCandidates terms view wanted).map fun rank => (rank, true)

/-- Enumerated certification follows from the actual selected list entry and requested projection. -/
theorem enumerated_checked [DecidableEq Symbol] (terms : List (Term (Label Symbol))) (view : View)
    (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ enumeratedRanks terms view wanted) :
    candidate.2 = true ∧ ∃ term, terms[candidate.1]? = some term ∧ project view term = wanted := by
  obtain ⟨rank, present, same⟩ := List.mem_map.mp member
  subst candidate
  obtain ⟨_, checked⟩ := List.mem_filter.mp present
  cases found : terms[rank]? with
  | none => simp [found] at checked
  | some term => exact ⟨rfl, term, rfl, by simpa [found] using checked⟩

/-- Every selected enumerated term is certified in every original request view. -/
theorem enumerated_certified_complete [DecidableEq Symbol] (terms : List (Term (Label Symbol)))
    (rank : Nat) (term : Term (Label Symbol)) (found : terms[rank]? = some term) (view : View) :
    (rank, true) ∈ enumeratedRanks terms view (project view term) := by
  refine List.mem_map.mpr ⟨rank, ?_, rfl⟩
  simp only [enumeratedCandidates, List.mem_filter, List.mem_range]
  exact ⟨(List.getElem?_eq_some_iff.mp found).1, by simp [found]⟩

/-- The enumerated scan preserves strict increasing rank order and bounds. -/
theorem enumerated_valid [DecidableEq Symbol] (terms : List (Term (Label Symbol))) (view : View)
    (wanted : List (Term (Label Symbol))) :
    ValidRanks terms.length ((enumeratedRanks terms view wanted).map Prod.fst) := by
  have erased : (enumeratedRanks terms view wanted).map Prod.fst = enumeratedCandidates terms view wanted := by
    simp [enumeratedRanks, List.map_map, Function.comp_def]
  rw [erased]
  unfold enumeratedCandidates
  exact ⟨List.pairwise_lt_range.sublist List.filter_sublist,
    fun rank member => List.mem_range.mp (List.mem_filter.mp member).1⟩

mutual
/-- The imported adapter accepts user labels at every node and rejects any private label. -/
def userTerm : Term (Label Symbol) → Option (Term Symbol)
  | .node (.user symbol) children => (userForest children).map (.node symbol)
  | _ => none

/-- Traverse all imported child terms in their source order. -/
def userForest : List (Term (Label Symbol)) → Option (List (Term Symbol))
  | [] => some []
  | first :: rest => do
      let term ← userTerm first
      let terms ← userForest rest
      pure (term :: terms)
end

/-- Successful user-label removal retains the entire original term. -/
theorem userTerm_sound (term : Term (Label Symbol)) (value : Term Symbol) (found : userTerm term = some value) :
    SymbolRelabel.termMap Label.user value = term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ values, userForest terms = some values → values.map (SymbolRelabel.termMap Label.user) = terms)
    generalizing value with
  | node label children ih =>
      cases label <;> simp only [userTerm] at found
      all_goals try contradiction
      rename_i symbol
      obtain ⟨values, read, same⟩ := Option.map_eq_some_iff.mp found
      subst value
      simp [SymbolRelabel.termMap, ih values read]
  | nil =>
      rename_i values found
      have same : values = [] := by simpa [userForest] using found.symm
      simp [same]
  | cons first rest ih ir =>
      rename_i values found
      cases head : userTerm first with
      | none => simp [userForest, head, Bind.bind, Option.bind] at found
      | some value => cases tail : userForest rest with
        | none => simp [userForest, head, tail, Bind.bind, Option.bind] at found
        | some remaining =>
            have same : values = value :: remaining := by simpa [userForest, head, tail, Bind.bind, Option.bind] using found.symm
            simp [same, ih value head, ir remaining tail]

/-- Relabelled backend values always survive the complete user-label traversal. -/
theorem userTerm_complete (value : Term Symbol) : userTerm (SymbolRelabel.termMap Label.user value) = some value := by
  induction value using Term.rec
    (motive_2 := fun values => userForest (values.map (SymbolRelabel.termMap Label.user)) = some values) with
  | node symbol children ih => simp [SymbolRelabel.termMap, userTerm, ih]
  | nil => rfl
  | cons first rest ih ir => simp [userForest, ih, ir, Bind.bind, Option.bind]

/-- The imported callback emits a true flag only after successful user-term conversion and backend ranking. -/
def importedRanks (rankTerm : Term Symbol → Except Cause Nat) (_view : View) :
    List (Term (Label Symbol)) → List Checked
  | [term] => match userTerm term with
      | none => []
      | some value => match rankTerm value with
          | .error _ => []
          | .ok rank => [(rank, true)]
  | _ => []

/-- The imported selector adds a user label at every node of the selected backend term. -/
def selectImported (select : Nat → Option (Term Symbol)) (rank : Nat) : Option (Term (Label Symbol)) :=
  (select rank).map (SymbolRelabel.termMap Label.user)

/-- Backend inverse certificates imply the complete imported checked flag, including the user-label traversal. -/
theorem imported_checked (rankTerm : Term Symbol → Except Cause Nat) (select : Nat → Option (Term Symbol))
    (inverse : ∀ term rank, rankTerm term = .ok rank → select rank = some term)
    (view : View) (wanted : List (Term (Label Symbol))) (candidate : Checked)
    (member : candidate ∈ importedRanks rankTerm view wanted) :
    candidate.2 = true ∧ ∃ term, selectImported select candidate.1 = some term ∧ project view term = wanted := by
  unfold importedRanks at member
  split at member
  · rename_i term
    cases found : userTerm term with
    | none => simp [found] at member
    | some value => cases ranked : rankTerm value with
      | error error => simp [found, ranked] at member
      | ok rank =>
          have same : candidate = (rank, true) := by simpa [found, ranked] using member
          subst candidate
          have termEq := userTerm_sound term value found
          refine ⟨rfl, SymbolRelabel.termMap Label.user value, ?_, ?_⟩
          · simp [selectImported, inverse value rank ranked]
          · rw [← termEq]
            cases value with
            | node symbol children => simpa only [SymbolRelabel.termMap] using (project_user view symbol (children.map (SymbolRelabel.termMap Label.user)))
  · simp at member

/-- A backend inverse result is retained with a true imported certificate in every opaque-root view. -/
theorem imported_certified (rankTerm : Term Symbol → Except Cause Nat) (value : Term Symbol)
    (rank : Nat) (ranked : rankTerm value = .ok rank) (view : View) :
    (rank, true) ∈ importedRanks rankTerm view (project view (SymbolRelabel.termMap Label.user value)) := by
  have projected : project view (SymbolRelabel.termMap Label.user value) = [SymbolRelabel.termMap Label.user value] := by
    cases value with
    | node symbol children => simpa only [SymbolRelabel.termMap] using (project_user view symbol (children.map (SymbolRelabel.termMap Label.user)))
  rw [projected]
  simp [importedRanks, userTerm_complete, ranked]


/-- Lift the concrete nonnegative composite candidates to the public signed-rank records. -/
def publicCandidates (rows : List Checked) : List CheckedRankQueries.Candidate :=
  rows.map fun entry => ⟨entry.1, entry.2⟩

/-- Public term replay rejects negative ranks and retains the selector's successful term. -/
def replay (select : Nat → Option Value) (rank : Int) : Except Unit Value :=
  if rank < 0 then .error () else match select rank.toNat with
    | none => .error ()
    | some term => .ok term

/-- A constructor-local replay certificate supplies the exact public checked-flag obligation. -/
theorem certified_public (select : Nat → Option Value) (wanted : Value) (rows : List Checked)
    (certified : ∀ candidate ∈ rows, candidate.2 = true → select candidate.1 = some wanted) :
    CheckedRankQueries.CheckedSound (replay select) wanted (publicCandidates rows) := by
  intro candidate member checked
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  subst candidate
  simp [replay, certified original present checked]

/-- Actual n-way join flags satisfy the public shortcut contract. -/
theorem join_public_checked [DecidableEq Symbol] (component : Nat) (operation : Source Symbol)
    (arguments : List (Source Symbol)) (wanted : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (replay (selectJoin component operation arguments)) wanted
      (publicCandidates (joinRanks component operation arguments .whole [wanted])) := by
  apply certified_public
  intro candidate member checked
  obtain ⟨term, selected, view⟩ := join_checked component operation arguments .whole [wanted] candidate member checked
  have same := whole_eq term wanted view
  simpa only [same] using selected

/-- Actual arbitrary frequency flags satisfy the public shortcut contract. -/
theorem frequency_public_checked [DecidableEq Symbol] (first : Nat) (sources : List (Source Symbol))
    (wanted : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (replay (selectFrequency first sources)) wanted
      (publicCandidates (frequencyRanks first 0 sources .whole [wanted])) := by
  apply certified_public
  intro candidate member checked
  obtain ⟨_, term, selected, view⟩ := frequency_checked first 0 sources .whole [wanted] candidate member checked
  have same := whole_eq term wanted view
  simpa [same] using selected

/-- Actual enumerated flags satisfy the public shortcut contract. -/
theorem enumerated_public_checked [DecidableEq Symbol] (terms : List (Term (Label Symbol)))
    (wanted : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (replay (fun rank => terms[rank]?)) wanted
      (publicCandidates (enumeratedRanks terms .whole [wanted])) := by
  apply certified_public
  intro candidate member _
  obtain ⟨_, term, selected, view⟩ := enumerated_checked terms .whole [wanted] candidate member
  have same := whole_eq term wanted view
  simpa only [same] using selected

/-- The imported producer's public shortcut follows from backend rank certificates and checked user-label traversal. -/
theorem imported_public_checked (rankTerm : Term Symbol → Except Cause Nat) (select : Nat → Option (Term Symbol))
    (inverse : ∀ term rank, rankTerm term = .ok rank → select rank = some term) (wanted : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (replay (selectImported select)) wanted
      (publicCandidates (importedRanks rankTerm .whole [wanted])) := by
  apply certified_public
  intro candidate member _
  obtain ⟨_, term, selected, view⟩ := imported_checked rankTerm select inverse .whole [wanted] candidate member
  have same := whole_eq term wanted view
  simpa only [same] using selected

/-- A wrong component can preserve the payload ranks but cannot obtain a checked join certificate. -/
theorem wrong_join_component :
    joinRanks 0 (.pure : Source Nat) [.pure] .whole [SupportJoin.joinTerm 1 (.node .pure []) [.node .pure []]] = [(0, false)] := rfl

/-- Extra center keys are rejected by the independent length check. -/
theorem wrong_join_length :
    joinKeysMatch (Symbol := Nat) 0 [.node (.argKey 0 0) []] [] = false := rfl

/-- Repeated equal frequency terms remain distinct checked member ranks in source branch order. -/
theorem frequency_checked_duplicates :
    frequencyRanks 0 0 ([.pure, .pure, .pure] : List (Source Nat)) .labelled [] = [(0, true), (1, true), (2, true)] := rfl

end MicroCFTA.CompositeCheckedRanks
