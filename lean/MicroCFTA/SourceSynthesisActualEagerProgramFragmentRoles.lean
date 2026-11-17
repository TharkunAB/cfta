import MicroCFTA.SourceSynthesisProgramChildScope
import MicroCFTA.SourceSynthesisOwnChildTerminals
import MicroCFTA.SourceSynthesisSelectedProgramChildRetention
import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationSelectedStagedChildInvocation

namespace MicroCFTA.SourceSynthesisActualEagerProgramFragmentRoles
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceSynthesisProgramEnumerationRoles (FragmentRoles)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false


open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisGuardRegions
open SourcePruningEnumerationSharedEagerChildren (ordinaryNonterminal)
open SourceSynthesisSelectedProgramChildRetention (ProgramSlot)

/- Note [Actual eager Program fragment roles]
Program operands have ordinary source fields and annotation-only buckets.
The actual own preparation retains their physical positions and strict height.
The guarded visitor therefore uses the actual eager visitor at each Program operand.
The proof follows those same selected and child traces by strong height induction.
Annotation and Marker fragments remain unrestricted by FragmentRoles.
No resource receipt or future role premise supplies the recursive conclusion.
The pure scope proof follows SourceSynthesisProgramChildScope.
It uses physical ProgramSlot positions so literal symbols can remain arbitrary.
-/

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem annotation_tail (path : EqualityTrie.Path) (within : annotationRegion path) :
    ∃ tail, path = 0 :: tail := by
  obtain ⟨tail, same⟩ := within
  exact ⟨tail, same.symm⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem inherited_empty (scs : List Suspended) (index : Nat) (nonzero : index ≠ 0)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) :
    descendScs index scs = [] := by
  change EqualityTrie.descendScs index scs = []
  unfold EqualityTrie.descendScs
  apply List.filter_eq_nil_iff.mpr
  intro sc member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  have noPaths : EqualityTrie.fromPathTrie (EqualityTrie.pathTrieDescend original.trie index) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro path represented
    have originalPath := (EqualityTrie.descend_exact original.trie (inherited original included).1 index path).mp represented
    obtain ⟨tail, same⟩ := (inherited original included).2 (index :: path) originalPath
    exact nonzero (List.cons.inj same).1
  have empty := (EqualityTrie.empty_exact _
    (EqualityTrie.descend_valid original.trie (inherited original included).1 index)).mpr noPaths
  simp [empty]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem projected_scope (constraint : Constraint)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project constraint = some (tries, residual))
    (index : Nat)
    (scope : ∀ suffix, index :: suffix ∈ EqualityNormalize.members
      ((SourceCompactGuards.sourceEqualities constraint).getD []) → ∃ tail, suffix = 0 :: tail) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ trie ∈ tries, ∀ suffix, index :: suffix ∈ EqualityTrie.fromPathTrie trie →
        ∃ tail, suffix = 0 :: tail := by
  have checked := SourcePruningEnumerationConstraint.project_complete constraint cached
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none =>
      simp only [source] at checked
      rw [checked.1] at projected
      cases projected
  | some classes =>
      simp only [source] at checked
      have same : EnumerationEquality.readClasses classes = tries :=
        congrArg Prod.fst (Option.some.inj (checked.1.symm.trans projected))
      rw [← same]
      refine ⟨checked.2.1, ?_⟩
      intro trie member suffix represented
      obtain ⟨paths, included, rfl⟩ := List.mem_map.mp member
      have originalPath := (checked.2.2.1 paths included (index :: suffix)).mp represented
      apply scope suffix
      simp only [source, Option.getD_some, EqualityNormalize.members, List.mem_eraseDups]
      exact List.mem_flatten.mpr ⟨paths, included, originalPath⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem descend_scope (scs : List Suspended) (index : Nat)
    (scope : ∀ sc ∈ scs, ∀ suffix, index :: suffix ∈ EqualityTrie.fromPathTrie sc.trie →
      ∃ tail, suffix = 0 :: tail) :
    ∀ sc ∈ descendScs index scs, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      ∃ tail, path = 0 :: tail := by
  intro sc member path represented
  change sc ∈ EqualityTrie.descendScs index scs at member
  unfold EqualityTrie.descendScs at member
  obtain ⟨mapped, _retained⟩ := List.mem_filter.mp member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp mapped
  exact scope original included path
    (SourcePruningEnumerationPathTransport.descended_path_original original.trie index path represented)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem program_child_scope
    (valid : Constraint → Prop) (literal : String → Symbol) (edge : EdgeValue Symbol Constraint)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge)
    (scs : List EnumerationState.Suspended) (start : Nat)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (index : Nat) (incoming : Node) (bucket : List EnumerationState.Suspended)
    (selected : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    (programIndex : SourceSynthesisSelectedProgramChildRetention.ProgramSlot edge index) :
    SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
  have selectedMember := List.mem_of_getElem? selected
  rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at selected
  obtain ⟨indexed, indexedStored, inputSame⟩ := Option.map_eq_some_iff.mp selected
  have indexSame : indexed.2 = index := by
    rw [List.getElem?_zipIdx] at indexedStored
    obtain ⟨storedChild, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
    simp
  have childStored : edge.children[index]? = some incoming := by
    rw [List.getElem?_zipIdx] at indexedStored
    obtain ⟨storedChild, childStored, pairSame⟩ := Option.map_eq_some_iff.mp indexedStored
    have childSame : storedChild = incoming :=
      (congrArg Prod.fst pairSame).trans (congrArg Prod.fst inputSame)
    simpa only [childSame] using childStored
  have bucketSame : descendScs index scs ++ descendScs index (suspendedVars start tries) = bucket := by
    simpa only [indexSame] using congrArg Prod.snd inputSame
  have nonzero : index ≠ 0 := by
    rcases programIndex with ⟨_arity, rfl | rfl⟩ | ⟨_arity, rfl⟩ <;> decide
  have inheritedEmpty := inherited_empty scs index nonzero inherited
  have ownBucket : bucket = descendScs index (suspendedVars start tries) := by
    rw [← bucketSame, inheritedEmpty, List.nil_append]
  have rowScope : ValueFields valid literal incoming ∧
      SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
      ∀ suffix, index :: suffix ∈ EqualityNormalize.members
        ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []) →
        ∃ tail, suffix = 0 :: tail := by
    cases fields with
    | annotated edge annotation _guard children _typed =>
        simp [SourceSynthesisSelectedProgramChildRetention.ProgramSlot, children] at programIndex
    | application edge types marker function argument _symbol guard children _typesTyped _markerTyped
        functionFields argumentFields =>
        have position : index = 2 ∨ index = 3 := by
          simpa [SourceSynthesisSelectedProgramChildRetention.ProgramSlot, children] using programIndex
        refine ⟨?_, ?_, ?_⟩
        · rcases position with rfl | rfl
          · have same : function = incoming := Option.some.inj (by
              simpa only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
            exact same ▸ functionFields
          · have same : argument = incoming := Option.some.inj (by
              simpa only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
            exact same ▸ argumentFields
        · rw [guard, SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
          exact SourceEqualityGuardReadback.normalize_cached _
        · intro suffix member
          have region : applicationRegion (index :: suffix) :=
            (application_guard_endpoints .empty .empty .empty "app" _
              [.empty, SourceSynthesisTypeSyntax.arrowMarker top, .empty, .empty] rfl).2 _
                (by simpa only [guard] using member)
          rcases position with rfl | rfl
          · exact annotation_tail suffix ((application_descend_function suffix).mp region)
          · exact annotation_tail suffix ((application_descend_argument suffix).mp region)
    | filter edge goal candidates _symbol guard children _goalTyped candidateFields =>
        have position : index = 1 := by
          simpa [SourceSynthesisSelectedProgramChildRetention.ProgramSlot, children] using programIndex
        refine ⟨?_, ?_, ?_⟩
        · have same : candidates = incoming := Option.some.inj (by
            simpa only [children, position, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
          exact same ▸ candidateFields
        · rw [guard, SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
          exact SourceEqualityGuardReadback.normalize_cached _
        · intro suffix member
          have region : filterRegion (1 :: suffix) :=
            (filter_guard_endpoints .empty .empty "filter" _ [.empty, .empty] rfl).2 _
              (by simpa only [guard, position] using member)
          exact annotation_tail suffix ((filter_descend_program suffix).mp region)
  obtain ⟨projectedValid, projectedScope⟩ := projected_scope edge.entry.key.constraint rowScope.2.1
    tries residual projected index rowScope.2.2
  have bucketValid := SourcePruningEnumerationOrdinarySemanticGates.children_valid edge scs start tries
    (fun sc member => (inherited sc member).1) projectedValid incoming bucket selectedMember
  have ownScope : ∀ sc ∈ suspendedVars start tries, ∀ suffix,
      index :: suffix ∈ EqualityTrie.fromPathTrie sc.trie → ∃ tail, suffix = 0 :: tail := by
    intro sc member suffix represented
    have included : sc.trie ∈ tries := by
      rw [← suspendedVars_tries start tries]
      exact List.mem_map.mpr ⟨sc, member, rfl⟩
    exact projectedScope sc.trie included suffix represented
  refine ⟨rowScope.1, inheritedEmpty, ownBucket, ?_⟩
  intro sc member
  exact ⟨bucketValid sc member, descend_scope _ index ownScope sc (ownBucket ▸ member)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem annotation_nonterminal
    (scs : List Suspended)
    (scope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  apply List.any_eq_false.mpr
  intro sc member tagged
  have terminal : sc.trie = .terminal := by
    cases trieRead : sc.trie with
    | empty => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    | terminal => rfl
    | branch children => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
  obtain ⟨tail, impossible⟩ := (scope sc member).2 [] ((EqualityTrie.nil_mem sc.trie).mpr terminal)
  cases impossible

private theorem tuple_length
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (inputs : List (Node × List Suspended))
    (done : List Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : List Fragment → ChildDispatch.Observation width → Option Cached → Result Output Reason width)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (index consumerIndex : Nat) (output : Output) (fragments : List Fragment)
    (actual : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped inputs
      caller before queries index output (.done fragments reached saved after) consumerIndex) :
    fragments.length = inputs.length := by
  induction inputs generalizing done stopped caller before queries index fragments with
  | nil =>
      cases actual
      rfl
  | cons first rest ih =>
      rcases first with ⟨incoming, bucket⟩
      obtain ⟨fragment, current, capturedQueries, captured, childIndex, remaining,
        shape, _child, tail⟩ := children_done_head_invocation checkEmpty r n p h k edgesOf policy
          done stopped incoming bucket rest caller before queries index output fragments
          reached saved after consumerIndex actual
      have remainingLength := ih (done := fun produced => done (fragment :: produced))
        (stopped := fun completed => stopped (fragment :: completed))
        (caller := current) (before := captured) (queries := capturedQueries)
        (index := childIndex) (fragments := remaining) tail
      simpa only [shape, List.length_cons] using congrArg (fun count => count + 1) remainingLength

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem own_inputs
    (heap : InternedConstructorTemplates.State Symbol Constraint) (scs : List Suspended)
    (edge : Edge) (before middle : Cached) (symbol : Symbol) (staged : List Input)
    (residual : Option Constraint)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)]) :
    ∃ tries, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      symbol = edge.entry.key.symbol ∧
      staged.map (fun input => (input.1, input.2.1)) =
        SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries ∧
      staged.length = edge.children.length := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at actual
    | some plan =>
        rcases plan with ⟨tries, kept⟩
        have shape := SourcePruningEnumerationCachedOwn.prepare_inputs heap scs edge before middle
          tries kept (symbol, staged, residual) projected actual
        simp only [Prod.mk.injEq] at shape
        obtain ⟨symbolSame, stagedSame, residualSame⟩ := shape
        subst kept
        refine ⟨tries, rfl, symbolSame, ?_, ?_⟩
        · rw [stagedSame, List.map_map]
          exact List.map_id _
        · simp only [stagedSame, SourcePruningEnumerationEdgeInputs.children,
            List.length_map, List.length_zipIdx]
  · simp [SourcePruningEnumerationCachedOwn.prepare, allowed] at actual

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem roles_from_program_positions
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (edge : Edge) (fields : EdgeFields valid literal edge) (symbol : Symbol)
    (symbolSame : symbol = edge.entry.key.symbol) (fragments : List Fragment)
    (count : fragments.length = edge.children.length)
    (positions : ∀ position, ProgramSlot edge position → ∀ fragment,
      fragments[position]? = some fragment → FragmentRoles literal marked fragment) :
    FragmentRoles literal marked (.node symbol fragments) := by
  cases fields with
  | annotated edge annotation _guard children _typed =>
      rw [children] at count
      cases fragments with
      | nil => simp at count
      | cons first rest =>
          have empty : rest = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons, List.length_nil] at count
            omega)
          subst rest
          exact .component symbol first
  | application edge types marker function argument symbolField _guard children
      _typesTyped _markerTyped _functionFields _argumentFields =>
      rw [children] at count
      cases fragments with
      | nil => simp at count
      | cons annotation rest =>
        cases rest with
        | nil => simp at count
        | cons mark rest =>
          cases rest with
          | nil => simp at count
          | cons first rest =>
            cases rest with
            | nil => simp at count
            | cons second rest =>
              have empty : rest = [] := List.length_eq_zero_iff.mp (by
                simp only [List.length_cons, List.length_nil] at count
                omega)
              subst rest
              rw [symbolSame, symbolField]
              exact .application annotation mark first second
                (positions 2 (by simp [ProgramSlot, children]) first rfl)
                (positions 3 (by simp [ProgramSlot, children]) second rfl)
  | filter edge goal candidates symbolField _guard children _goalTyped _candidateFields =>
      rw [children] at count
      cases fragments with
      | nil => simp at count
      | cons goalFragment rest =>
        cases rest with
        | nil => simp at count
        | cons candidateFragment rest =>
          have empty : rest = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons, List.length_nil] at count
            omega)
          subst rest
          rw [symbolSame, symbolField]
          exact .filter goalFragment candidateFragment
            (positions 1 (by simp [ProgramSlot, children]) candidateFragment rfl)

private theorem selected_roles
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (selected : edge ∈ rows) (fields : EdgeFields valid literal edge)
    (scs : List Suspended)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (recur : ∀ (child : Node) (bucket : List Suspended)
      (childCaller childReached : Caller width) (childBefore childAfter : Cached)
      (childQueries childSaved : Queries)
      (childDone : Fragment → Caller width → Queries → Cached → Result Output Reason width)
      (childStopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
      (childIndex childConsumerIndex : Nat) (childOutput : Output) (childFragment : Fragment),
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) →
      ValueFields valid literal child →
      (∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) →
      ChildInvocationAt checkEmpty r n p h k edgesOf .eager bucket child
        childCaller childBefore childQueries childDone childStopped childIndex childOutput
        (.done childFragment childReached childSaved childAfter) childConsumerIndex →
      FragmentRoles literal marked childFragment)
    (consume : SelectedEdge.Result width → Result Output Reason width)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (index consumerIndex : Nat) (output : Output) (fragment : Fragment)
    (actual : SelectedInvocationAt checkEmpty r n p h k edgesOf (.guarded (.node entry rows depth free))
      consume scs edge caller before queries index output
      (.complete fragment reached saved after) consumerIndex) :
    FragmentRoles literal marked fragment := by
  obtain ⟨symbol, staged, residual, middle, fragments, afterChildren,
    prepared, children, assembled, _finished⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf (.guarded (.node entry rows depth free))
      consume scs edge caller before queries index output fragment reached saved after consumerIndex actual
  obtain ⟨tries, projected, symbolSame, inputsSame, stagedCount⟩ :=
    own_inputs caller.checked.native.machine.heap scs edge before middle symbol staged residual prepared
  have count : fragments.length = edge.children.length := by
    have tupleCount := tuple_length checkEmpty r n p h k edgesOf (.guarded (.node entry rows depth free))
      (staged.map (fun input => (input.1, input.2.1))) _ _ caller reached middle afterChildren
      queries saved index consumerIndex output fragments children
    simpa only [List.length_map, stagedCount] using tupleCount
  have positions : ∀ position, ProgramSlot edge position → ∀ produced,
      fragments[position]? = some produced → FragmentRoles literal marked produced := by
    intro position slot produced producedAt
    have inside : position < staged.length := by
      rw [stagedCount]
      rcases slot with ⟨arity, rfl | rfl⟩ | ⟨arity, rfl⟩ <;> omega
    let input := staged[position]'inside
    have inputAt : staged[position]? = some input :=
      List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
    rcases input with ⟨child, bucket, action⟩
    have pairAt : (staged.map (fun input => (input.1, input.2.1)))[position]? =
        some (child, bucket) := by
      simp only [List.getElem?_map, inputAt, Option.map_some]
    have originalInput : (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)[position]? =
        some (child, bucket) := by
      rw [← inputsSame]
      exact pairAt
    have scope := program_child_scope valid literal edge fields scs before.core.counter pathScope
      tries residual projected position child bucket originalInput slot
    have member : (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) :=
      List.mem_of_getElem? pairAt
    obtain ⟨_childTries, _childProjection, _childInputs, lower⟩ :=
      SourcePruningEnumerationSharedEagerChildren.prepared_child_lt caller.checked.native.machine.heap
        entry rows depth free edge selected scs before middle symbol staged residual prepared child bucket member
    obtain ⟨_priorStaged, _laterStaged, priorFragments, childCaller, childBefore, childQueries,
      childRootIndex, childFragment, childReached, childSaved, childAfter, childCallbackIndex,
      _remainingFragments, _tupleAfter, _stagedSplit, _priorLength, completedLength,
      childAssembled, _childFinished, childTrace, _childTail⟩ :=
      selected_staged_child_invocation checkEmpty r n p h k edgesOf (.guarded (.node entry rows depth free))
        consume scs edge caller before queries index output fragment reached saved after consumerIndex
        symbol staged residual middle prepared position child bucket action inputAt actual
    have fragmentShape : fragments = priorFragments ++ childFragment :: _remainingFragments :=
      (Fragments.Fragment.node.inj (assembled.symm.trans childAssembled)).2
    have childAt : fragments[position]? = some childFragment := by
      rw [fragmentShape, List.getElem?_append_right (by omega), ← completedLength, Nat.sub_self]
      rfl
    have producedSame : produced = childFragment := Option.some.inj (producedAt.symm.trans childAt)
    subst produced
    cases childTrace with
    | guarded_lower _actualLower eagerTrace =>
        exact recur child bucket childCaller childReached childBefore childAfter childQueries childSaved
          _ _ childRootIndex childCallbackIndex output childFragment lower scope.1 scope.2.2.2 eagerTrace
    | guarded_else notLower _shallow =>
        exact (notLower lower).elim
  rw [assembled]
  exact roles_from_program_positions valid literal marked edge fields symbol symbolSame fragments count positions

private theorem at_height
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (selectionMembers : ∀ entry rows depth free, ∀ row ∈ edgesOf (.node entry rows depth free), row ∈ rows)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (height : Nat) :
    ∀ (incoming : Node) (scs : List Suspended)
      (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
      (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
      (stopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
      (index consumerIndex : Nat) (output : Output) (fragment : Fragment),
      MergedOrdinaryHeight.height incoming ≤ height →
      ValueFields valid literal incoming →
      (∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) →
      ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming
        caller before queries done stopped index output (.done fragment reached saved after) consumerIndex →
      FragmentRoles literal marked fragment := by
  induction height using Nat.strongRecOn with
  | ind height smaller =>
    intro incoming scs caller reached before after queries saved done stopped index consumerIndex output fragment
      ranked fields pathScope actual
    cases fields with
    | empty =>
      cases actual with
      | eager_fallback _fallback child =>
        cases child with
        | shallow_done observed _hit =>
          simp [ChildDispatch.run] at observed
      | eager_ordinary ordinary _order _past _rowRun _row _offset _hit =>
        change (false : Bool) = true at ordinary
        cases ordinary
    | node entry rows depth free checked =>
      have recursive : ∀ (child : Node) (bucket : List Suspended)
          (childCaller childReached : Caller width) (childBefore childAfter : Cached)
          (childQueries childSaved : Queries)
          (childDone : Fragment → Caller width → Queries → Cached → Result Output Reason width)
          (childStopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
          (childIndex childConsumerIndex : Nat) (childOutput : Output) (childFragment : Fragment),
          MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) →
          ValueFields valid literal child →
          (∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
            ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) →
          ChildInvocationAt checkEmpty r n p h k edgesOf .eager bucket child
            childCaller childBefore childQueries childDone childStopped childIndex childOutput
            (.done childFragment childReached childSaved childAfter) childConsumerIndex →
          FragmentRoles literal marked childFragment := by
        intro child bucket childCaller childReached childBefore childAfter childQueries childSaved
          childDone childStopped childIndex childConsumerIndex childOutput childFragment lower
          childFields childScope childTrace
        exact smaller (MergedOrdinaryHeight.height child) (Nat.lt_of_lt_of_le lower ranked)
          child bucket childCaller childReached childBefore childAfter childQueries childSaved
          childDone childStopped childIndex childConsumerIndex childOutput childFragment
          (Nat.le_refl _) childFields childScope childTrace
      cases actual with
      | eager_fallback fallback _child =>
        have positive : ordinaryNonterminal scs (.node entry rows depth free) = true := by
          simp only [ordinaryNonterminal, annotation_nonterminal scs pathScope, Bool.not_false]
        rw [positive] at fallback
        cases fallback
      | eager_ordinary _ordinary rowOrder _past _rowRun rowTrace _offset _hit =>
        apply selected_roles checkEmpty r n p h k edgesOf valid literal marked entry rows depth free
          (scs := scs) (pathScope := pathScope) (recur := recursive) (actual := rowTrace)
        · apply selectionMembers entry rows depth free
          rw [rowOrder]
          exact List.mem_append_right _ List.mem_cons_self
        · apply checked
          apply selectionMembers entry rows depth free
          rw [rowOrder]
          exact List.mem_append_right _ List.mem_cons_self

/-- The same actual eager Program return has source fragment roles at every supplied fuel. -/
theorem eager_program_fragment_roles
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (selectionMembers : ∀ entry rows depth free, ∀ row ∈ edgesOf (.node entry rows depth free), row ∈ rows)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (incoming : Node) (scs : List Suspended)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
    (index consumerIndex : Nat) (output : Output) (fragment : Fragment)
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (actual : ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming
      caller before queries done stopped index output (.done fragment reached saved after) consumerIndex) :
    FragmentRoles literal marked fragment

 := by
  exact at_height checkEmpty r n p h k edgesOf selectionMembers valid literal marked
    (MergedOrdinaryHeight.height incoming) incoming scs caller reached before after queries saved
    done stopped index consumerIndex output fragment (Nat.le_refl _) fields pathScope actual


end MicroCFTA.SourceSynthesisActualEagerProgramFragmentRoles

namespace MicroCFTA.SourceSynthesisActualEagerProgramFragmentRoles
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceSynthesisProgramEnumerationRoles (FragmentRoles)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

open SourceSynthesisSelectedProgramChildRetention (ProgramSlot)

/- Note [Program layout at the selected eager row]
The actual outer captured row uses the eager visitor directly.
Its same own preparation fixes each original Program operand position.
The closed eager child theorem supplies that operand's fragment role.
The selected fragment equation assembles those roles at the same return.
No resource admission, future callback role, or new mark set is assumed.
-/

/-- One actual eager selected row returns its source Program layout. -/
theorem selected_eager_program_fragment_roles
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (selectionMembers : ∀ entry rows depth free, ∀ row ∈ edgesOf (.node entry rows depth free), row ∈ rows)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (scs : List Suspended) (edge : Edge)
    (consume : SelectedEdge.Result width → Result Output Reason width)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (index consumerIndex : Nat) (output : Output) (fragment : Fragment)
    (fields : EdgeFields valid literal edge)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (actual : SelectedInvocationAt checkEmpty r n p h k edgesOf .eager consume scs edge
      caller before queries index output (.complete fragment reached saved after) consumerIndex) :
    FragmentRoles literal marked fragment
:= by
  obtain ⟨symbol, staged, residual, middle, fragments, afterChildren,
    prepared, children, assembled, _finished⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf .eager
      consume scs edge caller before queries index output fragment reached saved after consumerIndex actual
  obtain ⟨tries, projected, symbolSame, inputsSame, stagedCount⟩ :=
    own_inputs caller.checked.native.machine.heap scs edge before middle symbol staged residual prepared
  have count : fragments.length = edge.children.length := by
    have tupleCount := tuple_length checkEmpty r n p h k edgesOf .eager
      (staged.map (fun input => (input.1, input.2.1))) _ _ caller reached middle afterChildren
      queries saved index consumerIndex output fragments children
    simpa only [List.length_map, stagedCount] using tupleCount
  have positions : ∀ position, ProgramSlot edge position → ∀ produced,
      fragments[position]? = some produced → FragmentRoles literal marked produced := by
    intro position slot produced producedAt
    have inside : position < staged.length := by
      rw [stagedCount]
      rcases slot with ⟨arity, rfl | rfl⟩ | ⟨arity, rfl⟩ <;> omega
    let input := staged[position]'inside
    have inputAt : staged[position]? = some input :=
      List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
    rcases input with ⟨child, bucket, action⟩
    have pairAt : (staged.map (fun input => (input.1, input.2.1)))[position]? =
        some (child, bucket) := by
      simp only [List.getElem?_map, inputAt, Option.map_some]
    have originalInput : (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)[position]? =
        some (child, bucket) := by
      rw [← inputsSame]
      exact pairAt
    have scope := program_child_scope valid literal edge fields scs before.core.counter pathScope
      tries residual projected position child bucket originalInput slot
    obtain ⟨_priorStaged, _laterStaged, priorFragments, childCaller, childBefore, childQueries,
      childRootIndex, childFragment, childReached, childSaved, childAfter, childCallbackIndex,
      _remainingFragments, _tupleAfter, _stagedSplit, _priorLength, completedLength,
      childAssembled, _childFinished, childTrace, _childTail⟩ :=
      selected_staged_child_invocation checkEmpty r n p h k edgesOf .eager
        consume scs edge caller before queries index output fragment reached saved after consumerIndex
        symbol staged residual middle prepared position child bucket action inputAt actual
    have fragmentShape : fragments = priorFragments ++ childFragment :: _remainingFragments :=
      (Fragments.Fragment.node.inj (assembled.symm.trans childAssembled)).2
    have childAt : fragments[position]? = some childFragment := by
      rw [fragmentShape, List.getElem?_append_right (by omega), ← completedLength, Nat.sub_self]
      rfl
    have producedSame : produced = childFragment := Option.some.inj (producedAt.symm.trans childAt)
    subst produced
    exact eager_program_fragment_roles checkEmpty r n p h k edgesOf selectionMembers
      valid literal marked child bucket childCaller childReached childBefore childAfter
      childQueries childSaved _ _ childRootIndex childCallbackIndex output childFragment
      scope.1 scope.2.2.2 childTrace
  rw [assembled]
  exact roles_from_program_positions valid literal marked edge fields symbol symbolSame fragments count positions

end MicroCFTA.SourceSynthesisActualEagerProgramFragmentRoles
