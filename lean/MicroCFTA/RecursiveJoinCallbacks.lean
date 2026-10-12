import MicroCFTA.RecursiveJoinFields

/-!
# Recursive join callback parsing

The source parses argument wrappers before it checks their keys. A failed
key check retains the candidate positions and clears their checked flags.
-/
namespace MicroCFTA.RecursiveJoinCallbacks
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveJoinFields CompositeCheckedRanks

/-- Source argumentOf discards the key and requires the exact binary wrapper. -/
def argumentOf : EngineTerm Symbol → Option (EngineTerm Symbol)
  | .node .argKeyed [_, argument] => some argument
  | _ => none

/-- Traverse all argument wrappers without inspecting their keys. -/
def collect : List (EngineTerm Symbol) → Option (List (EngineTerm Symbol))
  | [] => some []
  | node :: rest => do
      let term ← argumentOf node
      let terms ← collect rest
      pure (term :: terms)

/-- Canonical wrappers parse to their original argument forest. -/
theorem collect_arguments (component first : Nat) (terms : List (EngineTerm Symbol)) :
    collect (SupportJoin.arguments component first terms) = some terms := by
  induction terms generalizing first with
  | nil => rfl
  | cons term rest ih => simp [SupportJoin.arguments, collect, argumentOf, ih]

/-- Parsing does not change the number of argument wrappers. -/
theorem collect_length (nodes terms : List (EngineTerm Symbol)) (parsed : collect nodes = some terms) :
    terms.length = nodes.length := by
  induction nodes generalizing terms with
  | nil => simpa [collect] using congrArg (Option.map List.length) parsed |>.symm
  | cons node rest ih =>
      simp only [collect, bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨term, _, tail, found, result⟩ := parsed
      cases Option.some.inj result
      simp [ih tail found]

/-- The final mapIndex builds the source's private n-way join term. -/
def selected (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (position : Position) : Option (EngineTerm Symbol) :=
  ((accumulate (start operation) arguments).select position).map
    (fun payload => SupportJoin.joinTerm component payload.1 payload.2)

/-- Read the exact center and argument shapes before the key check. -/
def childrenPositions (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol)) :
    List (EngineTerm Symbol) → List Checked
  | .node .centerKeyed (wantedOperation :: keys) :: nodes =>
      match collect nodes with
      | none => []
      | some wantedArguments =>
          if wantedArguments.length = arguments.length then
            (requests (start operation)
              (mask (joinKeysMatch component keys nodes) (operation.positions .whole [wantedOperation]))
              (arguments.zip wantedArguments)).2
          else []
  | _ => []

/-- Whole and labelled requests use one sort. A spine request sorts the whole result again. -/
def positions (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (view : View) (wanted : List (EngineTerm Symbol)) : List Checked :=
  match view with
  | .whole => match wanted with
      | [.node .joinN children] => sorted (childrenPositions component operation arguments children)
      | _ => []
  | .labelled => sorted (childrenPositions component operation arguments wanted)
  | .spine => match wanted with
      | [.node .joinN children] => sorted (sorted (childrenPositions component operation arguments children))
      | _ => []

/-- The join exposes the independent count, selector, and callback fields. -/
def field (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol)) : Finite Symbol :=
  ⟨(accumulate (start operation) arguments).counts, selected component operation arguments,
    positions component operation arguments⟩

/-- The final wrapper cannot remove any successful source index. -/
theorem field_indexed (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument) :
    FiniteIndex (field component operation arguments) := by
  have indexed := accumulate_indexed (start operation) arguments (start_indexed operation operationIndexed) argumentsIndexed
  intro position
  constructor
  · rintro ⟨term, found⟩
    obtain ⟨payload, selected, _⟩ := Option.map_eq_some_iff.mp found
    exact (indexed position).mp ⟨payload, selected⟩
  · intro bound
    obtain ⟨payload, found⟩ := (indexed position).mpr bound
    exact ⟨SupportJoin.joinTerm component payload.1 payload.2, by simp [field, selected, found]⟩

/-- Equal-length source zip retains all argument fields. -/
theorem zip_fields (arguments : List (Finite Symbol)) (terms : List (EngineTerm Symbol))
    (length : terms.length = arguments.length) : (arguments.zip terms).map Prod.fst = arguments := by
  simp [List.map_fst_zip, length]

/-- Equal-length source zip retains all requested terms. -/
theorem zip_terms (arguments : List (Finite Symbol)) (terms : List (EngineTerm Symbol))
    (length : terms.length = arguments.length) : (arguments.zip terms).map Prod.snd = terms := by
  simp [List.map_snd_zip, length]

/-- The initial operation callback is exact for the empty accumulated forest. -/
theorem start_exact (operation : Finite Symbol) (wanted : EngineTerm Symbol)
    (exact : WholeExact operation wanted) : RowsExact (start operation) (operation.positions .whole [wanted]) (wanted, []) := by
  intro position
  rw [exact]
  simp [start]

/-- The zipped all-arity fold is exact for the requested operation and every requested argument. -/
theorem zipped_exact (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (wantedOperation : EngineTerm Symbol) (wantedArguments : List (EngineTerm Symbol))
    (length : wantedArguments.length = arguments.length)
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (operationExact : WholeExact operation wantedOperation)
    (argumentsExact : ∀ entry ∈ arguments.zip wantedArguments, WholeExact entry.1 entry.2) :
    RowsExact (accumulate (start operation) arguments)
      (requests (start operation) (operation.positions .whole [wantedOperation]) (arguments.zip wantedArguments)).2
      (wantedOperation, wantedArguments) := by
  have result := requests_exact (start operation) _ (wantedOperation, []) (arguments.zip wantedArguments)
    (start_indexed operation operationIndexed)
    (fun entry member => argumentsIndexed entry.1 (List.of_mem_zip member).1) argumentsExact
    (start_exact operation wantedOperation operationExact)
  simpa [zip_fields arguments wantedArguments length, zip_terms arguments wantedArguments length] using result

/-- Canonical join wrapping is injective in its operation and argument forest. -/
theorem join_injective (component : Nat) (first second : Accumulated Symbol)
    (same : SupportJoin.joinTerm component first.1 first.2 = SupportJoin.joinTerm component second.1 second.2) :
    first = second := by
  have parts := List.cons.inj (Term.node.inj same).2
  have operation := (List.cons.inj (Term.node.inj parts.1).2).1
  have collected := congrArg collect parts.2
  rw [collect_arguments, collect_arguments] at collected
  exact Prod.ext operation (Option.some.inj collected)

/-- A selected join uses exactly the source's fixed argument arity. -/
theorem selected_length (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (position : Position) (payload : Accumulated Symbol)
    (found : (accumulate (start operation) arguments).select position = some payload) :
    payload.2.length = arguments.length := by
  simpa using accumulate_length (start operation) arguments 0 (start_length operation) position payload found

/-- A parsed argument payload is strictly shorter than its argument wrapper forest. -/
theorem collect_height (nodes terms : List (EngineTerm Symbol)) (parsed : collect nodes = some terms)
    (term : EngineTerm Symbol) (member : term ∈ terms) : term.height < forestHeight nodes := by
  induction nodes generalizing terms with
  | nil => simp [collect] at parsed; subst terms; simp at member
  | cons node rest ih =>
      simp only [collect, bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨head, headFound, tail, tailFound, result⟩ := parsed
      cases Option.some.inj result
      rcases List.mem_cons.mp member with same | member
      · subst term
        unfold argumentOf at headFound
        split at headFound
        · cases Option.some.inj headFound
          simp only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
          omega
        · cases headFound
      · have small := ih tail tailFound member
        change term.height < max node.height (forestHeight rest)
        omega

/-- The center wrapper makes the operation request strictly shorter. -/
theorem operation_below (operation : EngineTerm Symbol) (keys nodes : List (EngineTerm Symbol)) :
    operation.height < forestHeight (.node .centerKeyed (operation :: keys) :: nodes) := by
  simp only [forestHeight, Term.height, List.foldr_cons]
  omega

/-- Each parsed argument request is strictly shorter than the whole child forest. -/
theorem argument_below (operation : EngineTerm Symbol) (keys nodes terms : List (EngineTerm Symbol))
    (parsed : collect nodes = some terms) (term : EngineTerm Symbol) (member : term ∈ terms) :
    term.height < forestHeight (.node .centerKeyed (operation :: keys) :: nodes) := by
  have small := collect_height nodes terms parsed term member
  change term.height < max _ (forestHeight nodes)
  omega

/-- The source fixes its key list from the declared arity before it selects a payload. -/
def sourceJoin (component arity : Nat) (operation : EngineTerm Symbol) (arguments : List (EngineTerm Symbol)) : EngineTerm Symbol :=
  let keys := SupportJoin.keys component 0 arity
  .node .joinN (.node .centerKeyed (operation :: keys) ::
    List.zipWith (fun key argument => .node .argKeyed [key, argument]) keys arguments)

/-- Equal arity prevents the source zipWith from dropping an argument term. -/
theorem zipped_keys (component first : Nat) (terms : List (EngineTerm Symbol)) :
    List.zipWith (fun key argument => .node .argKeyed [key, argument])
      (SupportJoin.keys component first terms.length) terms = SupportJoin.arguments component first terms := by
  induction terms generalizing first with
  | nil => rfl
  | cons term rest ih => simp [SupportJoin.keys, SupportJoin.arguments, ih]

/-- The canonical join wrapper is the source fixed-arity wrapper on every selected payload. -/
theorem source_selected (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol)) (position : Position) :
    selected component operation arguments position =
      ((accumulate (start operation) arguments).select position).map
        (fun payload => sourceJoin component arguments.length payload.1 payload.2) := by
  cases found : (accumulate (start operation) arguments).select position with
  | none => simp [selected, found]
  | some payload =>
      have length := selected_length operation arguments position payload found
      simp [selected, found, sourceJoin, ← length, zipped_keys, SupportJoin.joinTerm]

/-- True callback rows recover precisely the selected private join term. -/
theorem children_exact_local (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (children : List (EngineTerm Symbol))
    (operationExact : ∀ term, term.height < forestHeight children → WholeExact operation term)
    (argumentsExact : ∀ argument ∈ arguments, ∀ term, term.height < forestHeight children → WholeExact argument term)
    (position : Position) :
    (position, true) ∈ childrenPositions component operation arguments children ↔
      selected component operation arguments position = some (.node .joinN children) := by
  constructor
  · intro member
    unfold childrenPositions at member
    split at member
    · rename_i wantedOperation keys nodes
      split at member
      · simp at member
      · rename_i wantedArguments parsed
        split at member
        · rename_i length
          rw [requests_mask, mask_true] at member
          obtain ⟨terms, keysEq, nodesEq⟩ := (join_keys_exact component keys nodes).mp member.1
          have termsEq : terms = wantedArguments := by
            rw [nodesEq, collect_arguments] at parsed
            exact Option.some.inj parsed
          subst terms
          have found := (zipped_exact operation arguments wantedOperation wantedArguments length operationIndexed argumentsIndexed
            (operationExact wantedOperation (operation_below _ _ _))
            (fun entry present => argumentsExact entry.1 (List.of_mem_zip present).1 entry.2
              (argument_below _ _ _ _ parsed entry.2 (List.of_mem_zip present).2)) position).mp member.2
          simp [selected, found, SupportJoin.joinTerm, keysEq, nodesEq]
        · simp at member
    · simp at member
  · intro found
    obtain ⟨payload, payloadFound, same⟩ := Option.map_eq_some_iff.mp found
    have length := selected_length operation arguments position payload payloadFound
    have childrenEq := (Term.node.inj same).2
    subst children
    have keysPass := (join_keys_exact (Symbol := Symbol) component _ _).mpr ⟨payload.2, rfl, rfl⟩
    simp only [childrenPositions, collect_arguments, ite_eq_left length, requests_mask, mask_true, keysPass, true_and]
    exact (zipped_exact operation arguments payload.1 payload.2 length operationIndexed argumentsIndexed
      (operationExact payload.1 (operation_below _ _ _))
      (fun entry present => argumentsExact entry.1 (List.of_mem_zip present).1 entry.2
        (argument_below _ _ _ _ (collect_arguments _ _ _) entry.2 (List.of_mem_zip present).2)) position).mpr payloadFound

/-- Full finite child contracts imply the local checked callback contract. -/
theorem children_exact (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (operationExact : FiniteExact operation) (argumentsExact : ∀ argument ∈ arguments, FiniteExact argument)
    (children : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ childrenPositions component operation arguments children ↔
      selected component operation arguments position = some (.node .joinN children) :=
  children_exact_local component operation arguments operationIndexed argumentsIndexed children
    (fun term _ => whole_exact operation operationExact term)
    (fun argument member term _ => whole_exact argument (argumentsExact argument member) term) position

/-- The complete source callback is exact in the whole, spine, and labelled views. -/
theorem field_exact (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (operationExact : FiniteExact operation) (argumentsExact : ∀ argument ∈ arguments, FiniteExact argument) :
    FiniteExact (field component operation arguments) := by
  intro view wanted position
  constructor
  · intro member
    change (position, true) ∈ positions component operation arguments view wanted at member
    cases view with
    | labelled =>
        rw [positions, mem_sorted] at member
        exact ⟨.node .joinN wanted, (children_exact component operation arguments operationIndexed argumentsIndexed
          operationExact argumentsExact wanted position).mp member, rfl⟩
    | whole | spine =>
        simp only [positions] at member
        split at member
        · rename_i children
          simp only [mem_sorted] at member
          exact ⟨.node .joinN children, (children_exact component operation arguments operationIndexed argumentsIndexed
            operationExact argumentsExact children position).mp member, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
        · simp at member
  · rintro ⟨term, found, rfl⟩
    change selected component operation arguments position = some term at found
    obtain ⟨payload, payloadFound, rfl⟩ := Option.map_eq_some_iff.mp found
    have selectedFound : selected component operation arguments position =
        some (SupportJoin.joinTerm component payload.1 payload.2) := by simp [selected, payloadFound]
    have member := (children_exact component operation arguments operationIndexed argumentsIndexed
      operationExact argumentsExact _ position).mpr selectedFound
    cases view <;> simpa [field, positions, SupportJoin.joinTerm, project, labelled, spine,
      SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, mem_sorted] using member

/-- The source sort orders every callback, including malformed-key candidates. -/
theorem field_ordered (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (view : View) (wanted : List (EngineTerm Symbol)) :
    ((field component operation arguments).positions view wanted).Pairwise
      (fun left right => before left right = true) := by
  cases view <;> simp only [field, positions]
  all_goals first | exact sorted_ordered _ | split <;> first | exact sorted_ordered _ | simp

/-- Callback interval bounds include rows with failed key checks. -/
theorem children_bounded (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationBounded : ∀ term, Bounded operation.counts (operation.positions .whole [term]))
    (argumentsBounded : ∀ argument ∈ arguments, ∀ term, Bounded argument.counts (argument.positions .whole [term]))
    (children : List (EngineTerm Symbol)) :
    Bounded (accumulate (start operation) arguments).counts (childrenPositions component operation arguments children) := by
  unfold childrenPositions
  split
  · rename_i wantedOperation keys nodes
    split
    · intro row member; simp at member
    · rename_i terms parsed
      split
      · rename_i length
        have bound := requests_bounded (start operation) _ (arguments.zip terms)
          (mask_bounded (joinKeysMatch component keys nodes) _ _ (operationBounded wantedOperation))
          (fun entry member => argumentsBounded entry.1 (List.of_mem_zip member).1 entry.2)
        simpa only [zip_fields arguments terms length] using bound
      · intro row member; simp at member
  · intro row member; simp at member

/-- All views retain the interval bounds after their source sorts. -/
theorem field_bounded (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationBounded : ∀ term, Bounded operation.counts (operation.positions .whole [term]))
    (argumentsBounded : ∀ argument ∈ arguments, ∀ term, Bounded argument.counts (argument.positions .whole [term]))
    (view : View) (wanted : List (EngineTerm Symbol)) :
    Bounded (field component operation arguments).counts ((field component operation arguments).positions view wanted) := by
  intro row member
  change row ∈ positions component operation arguments view wanted at member
  cases view with
  | labelled =>
      rw [positions, mem_sorted] at member
      exact children_bounded component operation arguments operationBounded argumentsBounded wanted row member
  | whole | spine =>
      simp only [positions] at member
      split at member
      · simp only [mem_sorted] at member
        exact children_bounded component operation arguments operationBounded argumentsBounded _ row member
      · simp at member

/-- Distinct positions survive the key mask and every prefix product. -/
theorem children_distinct (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationBounded : ∀ term, Bounded operation.counts (operation.positions .whole [term]))
    (argumentsBounded : ∀ argument ∈ arguments, ∀ term, Bounded argument.counts (argument.positions .whole [term]))
    (operationDistinct : ∀ term, Distinct (operation.positions .whole [term]))
    (argumentsDistinct : ∀ argument ∈ arguments, ∀ term, Distinct (argument.positions .whole [term]))
    (children : List (EngineTerm Symbol)) : Distinct (childrenPositions component operation arguments children) := by
  unfold childrenPositions
  split
  · split
    · exact .nil
    · split
      · exact requests_distinct (start operation) _ _ (mask_bounded _ _ _ (operationBounded _))
          (mask_distinct _ _ (operationDistinct _))
          (fun entry member => argumentsBounded entry.1 (List.of_mem_zip member).1 entry.2)
          (fun entry member => argumentsDistinct entry.1 (List.of_mem_zip member).1 entry.2)
      · exact .nil
  · exact .nil

/-- Every source view has distinct candidate positions, including unchecked rows. -/
theorem field_distinct (component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationBounded : ∀ term, Bounded operation.counts (operation.positions .whole [term]))
    (argumentsBounded : ∀ argument ∈ arguments, ∀ term, Bounded argument.counts (argument.positions .whole [term]))
    (operationDistinct : ∀ term, Distinct (operation.positions .whole [term]))
    (argumentsDistinct : ∀ argument ∈ arguments, ∀ term, Distinct (argument.positions .whole [term]))
    (view : View) (wanted : List (EngineTerm Symbol)) :
    Distinct ((field component operation arguments).positions view wanted) := by
  have children := children_distinct component operation arguments operationBounded argumentsBounded operationDistinct argumentsDistinct
  cases view <;> simp only [field, positions]
  all_goals first | exact sorted_distinct _ (children _) | split
  all_goals first | exact sorted_distinct _ (children _) | exact sorted_distinct _ (sorted_distinct _ (children _)) | exact .nil

end MicroCFTA.RecursiveJoinCallbacks
