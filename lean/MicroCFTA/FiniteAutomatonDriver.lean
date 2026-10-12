import MicroCFTA.CompactIndexChoice
import MicroCFTA.SymbolicStructuralBudget
import MicroCFTA.Cache

/-!
# Mixed finite automaton compilation

The source caches both successful indexes and empty results. Empty rows are
checked before the cache. Symbolic fallback does not recurse through this
cache. Compact compilation visits every edge and every group before dropping
empty results. New group intersections decrease the structural graph budget.
-/
namespace MicroCFTA.FiniteAutomatonDriver
open Language CompactEdgeRanks CompactChildSlots

/-- Source fallback checks in their declaration order. -/
structure Flags where
  sharedSymbols : Bool
  ambiguous : Bool
  tied : Bool
  residual : Bool
  deepPath : Bool

/-- The exact source compact-versus-symbolic condition. -/
def useSymbolic (flags : Flags) : Bool :=
  (flags.sharedSymbols && (flags.ambiguous || flags.tied)) || flags.residual || flags.deepPath

/-- One source row after ordering and direct-child group parsing. -/
structure EdgeSpec (Node Symbol : Type) where
  symbol : Symbol
  children : List Node
  groups : Option (List (List Nat))

/-- Source graph observations and the symbolic backend. -/
structure Source (Node Symbol Failure : Type) where
  edges : Node → List (EdgeSpec Node Symbol)
  flags : Node → Flags
  meet : Node → Node → Node
  symbolic : Node → Except Failure (Index (Term Symbol))

/-- Source buildGroup selects children by their original positions, then intersects from the left. -/
def groupRequest (meet : Node → Node → Node) (children : List Node) (positions : List Nat) : Option Node :=
  match readGroup children positions with
  | [] => none
  | first :: rest => some (rest.foldl meet first)

/-- All direct recursive requests of a compact edge. -/
def edgeRequests (meet : Node → Node → Node) (edge : EdgeSpec Node Symbol) : List Node :=
  match edge.groups with
  | none => []
  | some groups => groups.filterMap (groupRequest meet edge.children)

/-- All possible buildNode requests of this node's compact branch. -/
def requests (source : Source Node Symbol Failure) (node : Node) : List Node :=
  (source.edges node).flatMap (edgeRequests source.meet)

/-- Folded intersections never increase their first operand's structural budget. -/
theorem fold_meet_bound (meet : Node → Node → Node) (measure : Node → Nat)
    (bounded : ∀ first second, measure (meet first second) ≤ measure first)
    (first : Node) (rest : List Node) : measure (rest.foldl meet first) ≤ measure first := by
  induction rest generalizing first with
  | nil => exact Nat.le_refl _
  | cons second rest ih => exact Nat.le_trans (ih _) (bounded first second)

/-- A source group request is bounded by an actual child from its selected nonempty list. -/
theorem group_request_bound (meet : Node → Node → Node) (measure : Node → Nat)
    (bounded : ∀ first second, measure (meet first second) ≤ measure first)
    (children : List Node) (positions : List Nat) (requested : Node)
    (found : groupRequest meet children positions = some requested) :
    ∃ child ∈ children, measure requested ≤ measure child := by
  cases selected : readGroup children positions with
  | nil => simp [groupRequest, selected] at found
  | cons first rest =>
      have same : rest.foldl meet first = requested := by simpa [groupRequest, selected] using found
      have present : first ∈ readGroup children positions := by simp [selected]
      obtain ⟨index, _, childFound⟩ := (readGroup_member children positions first).mp present
      exact ⟨first, List.mem_of_getElem? childFound, same ▸ fold_meet_bound meet measure bounded first rest⟩

/-- Actual nonempty group intersections decrease below the compact parent. -/
theorem requests_decrease (source : Source Node Symbol Failure) (measure : Node → Nat)
    (childBelow : ∀ node edge, edge ∈ source.edges node → ∀ child ∈ edge.children, measure child < measure node)
    (meetBound : ∀ first second, measure (source.meet first second) ≤ measure first)
    (node requested : Node) (member : requested ∈ requests source node) : measure requested < measure node := by
  obtain ⟨edge, edgeMember, present⟩ := List.mem_flatMap.mp member
  cases groups : edge.groups with
  | none => simp [edgeRequests, groups] at present
  | some positions =>
      simp only [edgeRequests, groups] at present
      obtain ⟨group, _, found⟩ := List.mem_filterMap.mp present
      obtain ⟨child, childMember, bound⟩ := group_request_bound source.meet measure meetBound edge.children group requested found
      exact Nat.lt_of_le_of_lt bound (childBelow node edge edgeMember child childMember)

/-- Gather every computed group result before checking whether any intersection is empty. -/
def finishGroups : List (List Nat × Option (Index Value)) → Option (List (Group Value))
  | [] => some []
  | (_, none) :: _ => none
  | (positions, some index) :: rest => (finishGroups rest).map (⟨positions, index⟩ :: ·)

/-- The source edge result after all child group requests complete. -/
def finishEdge [DecidableEq Symbol] (symbol : Symbol) (arity : Nat)
    (groups : List (List Nat × Option (Index (Term Symbol)))) : Option (Index (Term Symbol)) :=
  (finishGroups groups).map (compiledEdge symbol arity)

/-- Source oneof rejects an empty list and retains the ordered direct choice otherwise. -/
def finishChoice (indexes : List (Index Value)) : Option (Index Value) :=
  match indexes with
  | [] => none
  | retained => some (CompactIndexChoice.choice retained)

/-- Source catMaybes followed by oneof and share. -/
def finishAlternatives (alternatives : List (Option (Index Value))) : Option (Index Value) :=
  finishChoice (alternatives.filterMap id)

/-- Pure compact edge evaluation uses the same parsed group order and exact requests. -/
def localEdge [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (resolve : Node → Option (Index (Term Symbol))) (edge : EdgeSpec Node Symbol) : Option (Index (Term Symbol)) :=
  match edge.groups with
  | none => none
  | some groups => finishEdge edge.symbol edge.children.length
      (groups.map fun positions => (positions, (groupRequest source.meet edge.children positions).bind resolve))

/-- The source local branch, including all symbolic failures becoming Nothing. -/
def localNode [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (node : Node) (resolve : Node → Option (Index (Term Symbol))) : Option (Index (Term Symbol)) :=
  if (source.edges node).isEmpty then none
  else if useSymbolic (source.flags node) then (source.symbolic node).toOption
  else finishAlternatives ((source.edges node).map (localEdge source resolve))

/-- Local edge evaluation reads only its explicitly computed group requests. -/
theorem localEdge_ext [DecidableEq Symbol] (source : Source Node Symbol Failure) (edge : EdgeSpec Node Symbol)
    (first second : Node → Option (Index (Term Symbol)))
    (same : ∀ requested ∈ edgeRequests source.meet edge, first requested = second requested) :
    localEdge source first edge = localEdge source second edge := by
  cases groups : edge.groups with
  | none => simp [localEdge, groups]
  | some positions =>
      simp only [localEdge, groups]
      congr 1
      apply List.map_congr_left
      intro group member
      cases found : groupRequest source.meet edge.children group with
      | none => rfl
      | some node =>
          have included : node ∈ edgeRequests source.meet edge := by
            simp only [edgeRequests, groups]
            exact List.mem_filterMap.mpr ⟨group, member, found⟩
          simp [same node included]

/-- A local compilation step depends only on strictly smaller requested nodes. -/
theorem localNode_ext [DecidableEq Symbol] (source : Source Node Symbol Failure) (node : Node)
    (first second : Node → Option (Index (Term Symbol)))
    (same : ∀ requested ∈ requests source node, first requested = second requested) :
    localNode source node first = localNode source node second := by
  unfold localNode
  split
  · rfl
  · split
    · rfl
    · congr 1
      apply List.map_congr_left
      intro edge member
      apply localEdge_ext
      intro requested present
      exact same requested (List.mem_flatMap.mpr ⟨edge, member, present⟩)

/-- A pure bounded port of the source's mixed compilation branches. -/
def pureBuild [DecidableEq Symbol] (source : Source Node Symbol Failure) : Nat → Node → Option (Index (Term Symbol))
  | 0, _ => none
  | fuel + 1, node => localNode source node (pureBuild source fuel)

/-- Structural decrease makes every adequate pure execution bound return the same exact result. -/
theorem pure_stable [DecidableEq Symbol] (source : Source Node Symbol Failure) (measure : Node → Nat)
    (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (firstFuel secondFuel : Nat) (node : Node) (firstEnough : measure node < firstFuel)
    (secondEnough : measure node < secondFuel) : pureBuild source firstFuel node = pureBuild source secondFuel node := by
  induction firstFuel generalizing secondFuel node with
  | zero => omega
  | succ firstFuel ih =>
      cases secondFuel with
      | zero => omega
      | succ secondFuel =>
          apply localNode_ext
          intro requested member
          have lower := decreases node requested member
          exact ih secondFuel requested (by omega) (by omega)

/-- A finite pure reference is selected from the derived structural execution bound. -/
def reference [DecidableEq Symbol] (source : Source Node Symbol Failure) (measure : Node → Nat) (node : Node) : Option (Index (Term Symbol)) :=
  pureBuild source (measure node + 1) node

/-- The bounded reference satisfies the source recursive equation without an assumed fixed-point law. -/
theorem reference_equation [DecidableEq Symbol] (source : Source Node Symbol Failure) (measure : Node → Nat)
    (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node) (node : Node) :
    reference source measure node = localNode source node (reference source measure) := by
  unfold reference
  apply localNode_ext
  intro requested member
  have lower := decreases node requested member
  exact pure_stable source measure decreases (measure node) (measure requested + 1) requested lower (by omega)

/-- The source cache distinguishes a missing entry from a stored empty result. -/
abbrev BuildCache (Node Symbol : Type) := Cache.Table Node (Option (Index (Term Symbol)))

/-- Sequential traversal preserves state even when the returned payload is Nothing. -/
def walk (action : Input → State → Option (Output × State)) : List Input → State → Option (List Output × State)
  | [], state => some ([], state)
  | first :: rest, state => do
      let (value, middle) ← action first state
      let (values, after) ← walk action rest middle
      pure (value :: values, after)

/-- Locally exact total actions give an exact complete traversal and preserve its state invariant. -/
theorem walk_exact (action : Input → State → Option (Output × State)) (expected : Input → Output)
    (invariant : State → Prop) (items : List Input)
    (correct : ∀ item ∈ items, ∀ state, invariant state →
      ∃ after, action item state = some (expected item, after) ∧ invariant after)
    (state : State) (valid : invariant state) :
    ∃ after, walk action items state = some (items.map expected, after) ∧ invariant after := by
  induction items generalizing state with
  | nil => exact ⟨state, rfl, valid⟩
  | cons first rest ih =>
      obtain ⟨middle, found, middleValid⟩ := correct first (by simp) state valid
      obtain ⟨after, later, afterValid⟩ := ih (fun item member => correct item (by simp [member])) middle middleValid
      exact ⟨after, by simp [walk, found, later], afterValid⟩

/-- One group call retains its slot list even when the request or its language is empty. -/
def runGroup (source : Source Node Symbol Failure)
    (build : Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol))
    (children : List Node) (positions : List Nat) (cache : BuildCache Node Symbol) :
    Option ((List Nat × Option (Index (Term Symbol))) × BuildCache Node Symbol) :=
  match groupRequest source.meet children positions with
  | none => some ((positions, none), cache)
  | some node => (build node cache).map fun (compiled, after) => ((positions, compiled), after)

/-- The source visits every group before sequencing its optional compiled indexes. -/
def runEdge [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (build : Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol))
    (edge : EdgeSpec Node Symbol) (cache : BuildCache Node Symbol) :
    Option (Option (Index (Term Symbol)) × BuildCache Node Symbol) :=
  match edge.groups with
  | none => some (none, cache)
  | some groups => (walk (runGroup source build edge.children) groups cache).map fun (results, after) =>
      (finishEdge edge.symbol edge.children.length results, after)

/-- The source visits every edge before dropping its empty results and making the ordered choice. -/
def runCompact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (build : Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol))
    (node : Node) (cache : BuildCache Node Symbol) :
    Option (Option (Index (Term Symbol)) × BuildCache Node Symbol) :=
  (walk (runEdge source build) (source.edges node) cache).map fun (results, after) =>
    (finishAlternatives results, after)

/-- The bounded operational source worker keeps empty-row, cache-hit, branch, and insertion order. -/
def buildNode [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure) :
    Nat → Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol)
  | 0, _, _ => none
  | fuel + 1, node, cache =>
      if (source.edges node).isEmpty then some (none, cache)
      else match cache node with
        | some compiled => some (compiled, cache)
        | none =>
            if useSymbolic (source.flags node) then
              let compiled := (source.symbolic node).toOption
              some (compiled, Cache.put cache node compiled)
            else (runCompact source (buildNode source fuel) node cache).map fun (compiled, after) =>
              (compiled, Cache.put after node compiled)

/-- Source Map.insert of the exact reference result preserves the complete cache invariant. -/
theorem put_reference [DecidableEq Node] (compute : Node → Result) (cache : Cache.Table Node Result)
    (valid : Cache.MemoValid compute cache) (node : Node) :
    Cache.MemoValid compute (Cache.put cache node (compute node)) := by
  intro other value present
  by_cases same : other = node
  · subst other
    simpa [Cache.put] using present.symm
  · exact valid other value (by simpa [Cache.put, same] using present)

/-- A compact edge's actual state traversal agrees with its pure local compilation. -/
theorem runEdge_exact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (build : Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol))
    (compute : Node → Option (Index (Term Symbol))) (edge : EdgeSpec Node Symbol)
    (correct : ∀ requested ∈ edgeRequests source.meet edge, ∀ cache, Cache.MemoValid compute cache →
      ∃ after, build requested cache = some (compute requested, after) ∧ Cache.MemoValid compute after)
    (cache : BuildCache Node Symbol) (valid : Cache.MemoValid compute cache) :
    ∃ after, runEdge source build edge cache = some (localEdge source compute edge, after) ∧ Cache.MemoValid compute after := by
  cases groups : edge.groups with
  | none => exact ⟨cache, by simp [runEdge, localEdge, groups], valid⟩
  | some positions =>
      let expected := fun group => (group, (groupRequest source.meet edge.children group).bind compute)
      have each : ∀ group ∈ positions, ∀ before, Cache.MemoValid compute before →
          ∃ after, runGroup source build edge.children group before = some (expected group, after) ∧ Cache.MemoValid compute after := by
        intro group member before beforeValid
        cases found : groupRequest source.meet edge.children group with
        | none => exact ⟨before, by simp [runGroup, expected, found], beforeValid⟩
        | some requested =>
            have included : requested ∈ edgeRequests source.meet edge := by
              simp only [edgeRequests, groups]
              exact List.mem_filterMap.mpr ⟨group, member, found⟩
            obtain ⟨after, selected, afterValid⟩ := correct requested included before beforeValid
            exact ⟨after, by simp [runGroup, expected, found, selected], afterValid⟩
      obtain ⟨after, visited, afterValid⟩ := walk_exact (runGroup source build edge.children) expected
        (Cache.MemoValid compute) positions each cache valid
      exact ⟨after, by simp [runEdge, localEdge, groups, visited, expected], afterValid⟩

/-- The full compact traversal has exactly the pure local alternative result. -/
theorem runCompact_exact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (build : Node → BuildCache Node Symbol → Option (Option (Index (Term Symbol)) × BuildCache Node Symbol))
    (compute : Node → Option (Index (Term Symbol))) (node : Node)
    (correct : ∀ requested ∈ requests source node, ∀ cache, Cache.MemoValid compute cache →
      ∃ after, build requested cache = some (compute requested, after) ∧ Cache.MemoValid compute after)
    (cache : BuildCache Node Symbol) (valid : Cache.MemoValid compute cache) :
    ∃ after, runCompact source build node cache =
      some (finishAlternatives ((source.edges node).map (localEdge source compute)), after) ∧ Cache.MemoValid compute after := by
  have each : ∀ edge ∈ source.edges node, ∀ before, Cache.MemoValid compute before →
      ∃ after, runEdge source build edge before = some (localEdge source compute edge, after) ∧ Cache.MemoValid compute after := by
    intro edge member before beforeValid
    exact runEdge_exact source build compute edge (fun requested present =>
      correct requested (List.mem_flatMap.mpr ⟨edge, member, present⟩)) before beforeValid
  obtain ⟨after, visited, afterValid⟩ := walk_exact (runEdge source build) (localEdge source compute)
    (Cache.MemoValid compute) (source.edges node) each cache valid
  exact ⟨after, by simp [runCompact, visited], afterValid⟩

/-- The actual cache driver terminates and returns the derived pure result at every sufficient structural bound. -/
theorem buildNode_exact [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat)
    (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (fuel : Nat) (node : Node) (cache : BuildCache Node Symbol)
    (valid : Cache.MemoValid (reference source measure) cache) (enough : measure node < fuel) :
    ∃ after, buildNode source fuel node cache = some (reference source measure node, after) ∧
      Cache.MemoValid (reference source measure) after := by
  induction fuel generalizing node cache with
  | zero => omega
  | succ fuel ih =>
      have referenceEq := reference_equation source measure decreases node
      by_cases empty : (source.edges node).isEmpty = true
      · have result : reference source measure node = none := by simpa [localNode, empty] using referenceEq
        exact ⟨cache, by simp [buildNode, empty, result], valid⟩
      · cases cached : cache node with
        | some compiled =>
            have same := valid node compiled cached
            exact ⟨cache, by simp [buildNode, empty, cached, same], valid⟩
        | none =>
            by_cases fallback : useSymbolic (source.flags node) = true
            · have result : reference source measure node = (source.symbolic node).toOption := by
                simpa [localNode, empty, fallback] using referenceEq
              refine ⟨Cache.put cache node (reference source measure node), ?_, put_reference _ cache valid node⟩
              simp [buildNode, empty, cached, fallback, result]
            · have children : ∀ requested ∈ requests source node, ∀ before, Cache.MemoValid (reference source measure) before →
                  ∃ after, buildNode source fuel requested before = some (reference source measure requested, after) ∧
                    Cache.MemoValid (reference source measure) after := by
                intro requested member before beforeValid
                have smaller := decreases node requested member
                exact ih requested before beforeValid (by omega)
              obtain ⟨after, compiled, afterValid⟩ := runCompact_exact source (buildNode source fuel)
                (reference source measure) node children cache valid
              have result : reference source measure node =
                  finishAlternatives ((source.edges node).map (localEdge source (reference source measure))) := by
                simpa [localNode, empty, fallback] using referenceEq
              rw [← result] at compiled
              refine ⟨Cache.put after node (reference source measure node), ?_, put_reference _ after afterValid node⟩
              simp [buildNode, empty, cached, fallback, compiled]

/-- An empty cache satisfies the exact source reference invariant. -/
theorem empty_cache (compute : Node → Result) : Cache.MemoValid compute (fun _ => none) := by
  intro node result impossible
  cases impossible

/-- The mixed cache driver always completes from its source empty initial cache. -/
theorem buildNode_terminates [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat)
    (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node) (node : Node) :
    ∃ after, buildNode source (measure node + 1) node (fun _ => none) =
      some (reference source measure node, after) ∧ Cache.MemoValid (reference source measure) after :=
  buildNode_exact source measure decreases _ node _ (empty_cache _) (by omega)


/-- Actual copied intersection rows derive the decreasing budget for every compact request. -/
theorem structural_requests_decrease [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (automaton : Automaton Node Symbol) (rank : Node → Nat)
    (below : ∀ node edge, edge ∈ automaton node → ∀ child ∈ edge.children, rank child < rank node)
    (rows : ∀ node edge, edge ∈ source.edges node → ∃ original ∈ automaton node, original.children = edge.children)
    (copied : SymbolicGraphView.RowsCorrespond (Language.intersect automaton automaton) automaton
      (fun pair => source.meet pair.1 pair.2)) (node requested : Node)
    (member : requested ∈ requests source node) :
    SymbolicGraphView.structuralValue automaton rank below requested <
      SymbolicGraphView.structuralValue automaton rank below node := by
  apply requests_decrease source (SymbolicGraphView.structuralValue automaton rank below) ?_ ?_ node requested member
  · intro parent edge present child childMember
    obtain ⟨original, originalMember, same⟩ := rows parent edge present
    exact GraphBudget.child_smaller automaton (SymbolicGraphView.structuralBudget automaton rank below)
      parent original originalMember child (same ▸ childMember)
  · intro first second
    exact (SymbolicGraphView.structural_intersection automaton rank below source.meet copied first second).1

/-- Acyclic source rows and the concrete product-row adapter suffice for complete driver termination. -/
theorem buildNode_from_rows [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (automaton : Automaton Node Symbol) (rank : Node → Nat)
    (below : ∀ node edge, edge ∈ automaton node → ∀ child ∈ edge.children, rank child < rank node)
    (rows : ∀ node edge, edge ∈ source.edges node → ∃ original ∈ automaton node, original.children = edge.children)
    (copied : SymbolicGraphView.RowsCorrespond (Language.intersect automaton automaton) automaton
      (fun pair => source.meet pair.1 pair.2)) (node : Node) :
    ∃ after, buildNode source (SymbolicGraphView.structuralValue automaton rank below node + 1) node (fun _ => none) =
      some (reference source (SymbolicGraphView.structuralValue automaton rank below) node, after) ∧
      Cache.MemoValid (reference source (SymbolicGraphView.structuralValue automaton rank below)) after :=
  buildNode_terminates source _ (structural_requests_decrease source automaton rank below rows copied) node

/-- A stored result either proves emptiness or gives a positive exact direct index. -/
def ResultExact (language : Value → Prop) : Option (Index Value) → Prop
  | none => ∀ value, ¬ language value
  | some index => 0 < index.count ∧ Correct index ∧
      ∀ value, (∃ rank, index.select rank = some value) ↔ language value

/-- Exact optional indexes depend only on the represented language. -/
theorem result_ext (first second : Value → Prop) (same : ∀ value, first value ↔ second value)
    (result : Option (Index Value)) : ResultExact first result ↔ ResultExact second result := by
  cases result <;> simp only [ResultExact]
  · exact forall_congr' (fun value => not_congr (same value))
  · apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    exact forall_congr' (fun value => iff_congr Iff.rfl (same value))

/-- Folded source intersection implements conjunction of all selected child domains. -/
theorem fold_meet_language (meet : Node → Node → Node) (language : Node → Value → Prop)
    (exact : ∀ first second value, language (meet first second) value ↔ language first value ∧ language second value)
    (first : Node) (rest : List Node) (value : Value) :
    language (rest.foldl meet first) value ↔ language first value ∧ ∀ child ∈ rest, language child value := by
  induction rest generalizing first with
  | nil => simp
  | cons second rest ih => simp [List.foldl_cons, ih, exact, and_assoc]

/-- A valid nonempty position group always makes an actual intersection request. -/
theorem groupRequest_exists (meet : Node → Node → Node) (children : List Node) (positions : List Nat)
    (nonempty : positions ≠ []) (within : ∀ index ∈ positions, index < children.length) :
    ∃ requested, groupRequest meet children positions = some requested := by
  obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil positions nonempty
  have present : children[index]'(within index member) ∈ readGroup children positions :=
    (readGroup_member children positions _).mpr ⟨index, member, List.getElem?_eq_getElem (within index member)⟩
  cases read : readGroup children positions with
  | nil => simp [read] at present
  | cons first rest => exact ⟨rest.foldl meet first, by simp [groupRequest, read]⟩

/-- The actual requested intersection has precisely the group's indexed child-domain language. -/
theorem groupRequest_language (meet : Node → Node → Node) (language : Node → Term Symbol → Prop)
    (exact : ∀ first second value, language (meet first second) value ↔ language first value ∧ language second value)
    (children : List Node) (positions : List Nat) (within : ∀ index ∈ positions, index < children.length)
    (requested : Node) (found : groupRequest meet children positions = some requested) (value : Term Symbol) :
    language requested value ↔ ∀ index ∈ positions, positionDomain language children index value := by
  have readExact : language requested value ↔ ∀ child ∈ readGroup children positions, language child value := by
    cases read : readGroup children positions with
    | nil => simp [groupRequest, read] at found
    | cons first rest =>
        have same : rest.foldl meet first = requested := by simpa [groupRequest, read] using found
        rw [← same, fold_meet_language meet language exact first rest value]
        simp
  rw [readExact]
  constructor
  · intro accepted index member
    have bound := within index member
    refine ⟨children[index], List.getElem?_eq_getElem bound, ?_⟩
    exact accepted _ ((readGroup_member children positions _).mpr ⟨index, member, List.getElem?_eq_getElem bound⟩)
  · intro accepted child member
    obtain ⟨index, present, childFound⟩ := (readGroup_member children positions child).mp member
    obtain ⟨other, found, domain⟩ := accepted index present
    have same := Option.some.inj (childFound.symm.trans found)
    simpa only [same] using domain

/-- The source constraint parser supplies the direct-child grouping needed by compact compilation. -/
def ParsedLayout (classes : EdgeSpec Node Symbol → List (List Nat)) (edge : EdgeSpec Node Symbol) : Prop :=
  ∀ groups, edge.groups = some groups →
    CompactGroups.ValidClasses edge.children.length (classes edge) ∧
      groups = CompactGroups.childGroups edge.children.length (classes edge)

/-- A compact row's language retains its symbol, children, and complete parsed equalities. -/
def EdgeLanguage (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (edge : EdgeSpec Node Symbol) (term : Term Symbol) : Prop :=
  edge.groups.isSome = true ∧ EdgeTerms edge.symbol edge.children.length (classes edge)
    (positionDomain language edge.children) term

/-- Optional group sequencing fails exactly when one already-computed result is empty. -/
theorem finishGroups_none (groups : List (List Nat × Option (Index Value))) :
    finishGroups groups = none ↔ ∃ positions, (positions, none) ∈ groups := by
  induction groups with
  | nil => simp [finishGroups]
  | cons first rest ih =>
      rcases first with ⟨positions, result⟩
      cases result with
      | none => simp [finishGroups]
      | some index => simp [finishGroups, ih]

/-- Successful group sequencing retains each position list and exactly its compiled index. -/
theorem finishGroups_some (input : List (List Nat × Option (Index Value))) (groups : List (Group Value))
    (found : finishGroups input = some groups) :
    groups.map Group.positions = input.map Prod.fst ∧
      ∀ group ∈ groups, (group.positions, some group.index) ∈ input := by
  induction input generalizing groups with
  | nil => cases found; simp
  | cons first rest ih =>
      rcases first with ⟨positions, result⟩
      cases result with
      | none => cases found
      | some index =>
          obtain ⟨tail, tailFound, same⟩ := Option.map_eq_some_iff.mp found
          subst groups
          obtain ⟨samePositions, members⟩ := ih tail tailFound
          constructor
          · simp [samePositions]
          · intro group member
            rcases List.mem_cons.mp member with rfl | member
            · simp
            · simp [members group member]


/-- The concrete compact edge assembler derives exactness from its requested child intersections. -/
theorem localEdge_exact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (meetExact : ∀ first second value, language (source.meet first second) value ↔ language first value ∧ language second value)
    (edge : EdgeSpec Node Symbol) (parsed : ParsedLayout classes edge)
    (resolve : Node → Option (Index (Term Symbol)))
    (resolved : ∀ requested ∈ edgeRequests source.meet edge, ResultExact (language requested) (resolve requested)) :
    ResultExact (EdgeLanguage language classes edge) (localEdge source resolve edge) := by
  cases shape : edge.groups with
  | none => simp [localEdge, shape, ResultExact, EdgeLanguage]
  | some positions =>
      obtain ⟨valid, layout⟩ := parsed positions shape
      let results := positions.map fun group => (group, (groupRequest source.meet edge.children group).bind resolve)
      have each : ∀ entry ∈ results,
          ResultExact (fun value => ∀ index ∈ entry.1, positionDomain language edge.children index value) entry.2 := by
        intro entry member
        obtain ⟨group, present, same⟩ := List.mem_map.mp member
        subst entry
        have groupMember : group ∈ CompactGroups.childGroups edge.children.length (classes edge) := by simpa [layout] using present
        have nonempty := CompactGroups.childGroups_nonempty edge.children.length (classes edge) valid group groupMember
        have within : ∀ index ∈ group, index < edge.children.length := by
          intro index inGroup
          exact List.mem_range.mp ((CompactGroups.childGroups_positions edge.children.length (classes edge)).mem_iff.mp
            (List.mem_flatten.mpr ⟨group, groupMember, inGroup⟩))
        obtain ⟨requested, found⟩ := groupRequest_exists source.meet edge.children group nonempty within
        have requestedMember : requested ∈ edgeRequests source.meet edge := by
          simp only [edgeRequests, shape]
          exact List.mem_filterMap.mpr ⟨group, present, found⟩
        have precise := resolved requested requestedMember
        have transformed := (result_ext (language requested)
          (fun value => ∀ index ∈ group, positionDomain language edge.children index value)
          (groupRequest_language source.meet language meetExact edge.children group within requested found)
          (resolve requested)).mp precise
        simpa only [found, Option.bind_some] using transformed
      cases compiled : finishGroups results with
      | none =>
          simp only [localEdge, shape]
          change ResultExact _ (finishEdge edge.symbol edge.children.length results)
          rw [finishEdge, compiled]
          change ∀ term, ¬ EdgeLanguage language classes edge term
          obtain ⟨emptyPositions, emptyMember⟩ := (finishGroups_none results).mp compiled
          have empty := each (emptyPositions, none) emptyMember
          have positionMember : emptyPositions ∈ positions := by
            obtain ⟨group, present, same⟩ := List.mem_map.mp emptyMember
            have positionsSame : group = emptyPositions := congrArg Prod.fst same
            simpa only [positionsSame] using present
          intro term accepted
          cases term with
          | node symbol values =>
              obtain ⟨_, root, size, domains, equalities⟩ := accepted
              have selected := (CompactGroups.groupSelections_exact (positionDomain language edge.children)
                (childValue (.node edge.symbol []) values) edge.children.length (classes edge) valid).mpr
                  ⟨by simpa only [size] using domains, equalities⟩
              obtain ⟨value, properties⟩ := selected emptyPositions (by simpa only [layout] using positionMember)
              exact empty value (fun index member => (properties index member).1)
      | some groups =>
          have sequenced := finishGroups_some results groups compiled
          have groupLayout : groups.map Group.positions = CompactGroups.childGroups edge.children.length (classes edge) := by
            rw [sequenced.1]
            simp only [results, List.map_map, Function.comp_def]
            change positions.map id = _
            rw [List.map_id]
            exact layout
          have correct : ∀ group ∈ groups, Correct group.index := by
            intro group member
            exact (each (group.positions, some group.index) (sequenced.2 group member)).2.1
          have positive : 0 < (plan groups).count := by
            rw [plan_count]
            apply List.prod_pos_iff_forall_pos_nat.mpr
            intro number member
            obtain ⟨group, present, same⟩ := List.mem_map.mp member
            have greater := (each (group.positions, some group.index) (sequenced.2 group present)).1
            simpa only [same] using greater
          have domains : ∀ group ∈ groups, ∀ value,
              (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, positionDomain language edge.children index value := by
            intro group member
            exact (each (group.positions, some group.index) (sequenced.2 group member)).2.2
          simp only [localEdge, shape]
          change ResultExact _ (finishEdge edge.symbol edge.children.length results)
          rw [finishEdge, compiled]
          refine ⟨positive, compiledEdge_correct edge.symbol edge.children.length (classes edge) valid groups groupLayout correct, ?_⟩
          intro term
          simpa only [EdgeLanguage, shape, Option.isSome_some, true_and, compiledEdge] using
            edge_language_exact edge.symbol edge.children.length (classes edge) valid
              (positionDomain language edge.children) groups groupLayout correct domains term


/-- Dropping empty edge results and adding ordered offsets preserves the exact disjoint union. -/
theorem finishAlternatives_exact (items : List Input) (language : Input → Value → Prop)
    (compiled : Input → Option (Index Value)) (each : ∀ item ∈ items, ResultExact (language item) (compiled item))
    (separate : items.Pairwise (fun first second => ∀ value, language first value → ¬language second value)) :
    ResultExact (fun value => ∃ item ∈ items, language item value) (finishAlternatives (items.map compiled)) := by
  let retained := items.filterMap compiled
  have origin : ∀ index ∈ retained, ∃ item ∈ items, compiled item = some index := by
    intro index member
    exact List.mem_filterMap.mp member
  have valid : ∀ index ∈ retained, Correct index := by
    intro index member
    obtain ⟨item, present, found⟩ := origin index member
    have result := each item present
    rw [found] at result
    exact result.2.1
  have positive : ∀ index ∈ retained, 0 < index.count := by
    intro index member
    obtain ⟨item, present, found⟩ := origin index member
    have result := each item present
    rw [found] at result
    exact result.1
  have disjoint : CompactIndexChoice.Disjoint retained := by
    apply List.pairwise_filterMap.mpr
    apply separate.imp_of_mem
    intro first second firstMember secondMember apart a aFound b bFound firstRank secondRank value firstSelected secondSelected
    have firstExact := each first firstMember
    have secondExact := each second secondMember
    rw [aFound] at firstExact
    rw [bFound] at secondExact
    exact apart value ((firstExact.2.2 value).mp ⟨firstRank, firstSelected⟩)
      ((secondExact.2.2 value).mp ⟨secondRank, secondSelected⟩)
  have semantics : ∀ value, (∃ rank, CompactIndexChoice.select retained rank = some value) ↔
      ∃ item ∈ items, language item value := by
    intro value
    rw [CompactIndexChoice.language_exact retained valid]
    constructor
    · rintro ⟨index, member, rank, selected⟩
      obtain ⟨item, present, found⟩ := origin index member
      have precise := each item present
      rw [found] at precise
      exact ⟨item, present, (precise.2.2 value).mp ⟨rank, selected⟩⟩
    · rintro ⟨item, member, accepted⟩
      have precise := each item member
      cases found : compiled item with
      | none => rw [found] at precise; exact False.elim (precise value accepted)
      | some index =>
          rw [found] at precise
          obtain ⟨rank, selected⟩ := (precise.2.2 value).mpr accepted
          exact ⟨index, List.mem_filterMap.mpr ⟨item, member, found⟩, rank, selected⟩
  have result : finishAlternatives (items.map compiled) = finishChoice retained := by
    simp only [finishAlternatives, List.filterMap_map, Function.comp_def, id_eq, retained]

  rw [result]
  cases shape : retained with
  | nil =>
      change ∀ value, ¬ (∃ item ∈ items, language item value)
      intro value accepted
      obtain ⟨rank, selected⟩ := (semantics value).mpr accepted
      simp [shape, CompactIndexChoice.select] at selected
  | cons first rest =>
      change ResultExact _ (some (CompactIndexChoice.choice (first :: rest)))
      have greater := positive first (by simp [shape])
      have positiveCount : 0 < CompactIndexChoice.count (first :: rest) := by
        simp only [CompactIndexChoice.count, List.map_cons, List.sum_cons]
        omega
      refine ⟨positiveCount, ?_, ?_⟩
      · simpa only [shape] using CompactIndexChoice.choice_correct retained valid disjoint
      · simpa only [shape, CompactIndexChoice.choice] using semantics

/-- Local source adapters retain original row languages and the already verified fallback backend. -/
structure Semantics [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat)) : Prop where
  empty : ∀ node, (source.edges node).isEmpty = true → ∀ term, ¬language node term
  symbolic : ∀ node, useSymbolic (source.flags node) = true → ResultExact (language node) (source.symbolic node).toOption
  intersection : ∀ first second value,
    language (source.meet first second) value ↔ language first value ∧ language second value
  parsed : ∀ node, useSymbolic (source.flags node) = false → ∀ edge ∈ source.edges node, ParsedLayout classes edge
  rows : ∀ node, useSymbolic (source.flags node) = false → ∀ term,
    language node term ↔ ∃ edge ∈ source.edges node, EdgeLanguage language classes edge term
  disjoint : ∀ node, useSymbolic (source.flags node) = false →
    (source.edges node).Pairwise (fun first second => ∀ term,
      EdgeLanguage language classes first term → ¬EdgeLanguage language classes second term)

/-- One exact source node step follows from child indexes, copied intersection semantics, and the actual compact gate. -/
theorem localNode_exact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node)
    (resolve : Node → Option (Index (Term Symbol)))
    (resolved : ∀ requested ∈ requests source node, ResultExact (language requested) (resolve requested)) :
    ResultExact (language node) (localNode source node resolve) := by
  by_cases empty : (source.edges node).isEmpty = true
  · simpa only [localNode, empty, ↓reduceIte, ResultExact] using semantics.empty node empty
  · by_cases fallback : useSymbolic (source.flags node) = true
    · simpa [localNode, empty, fallback] using semantics.symbolic node fallback
    · have compact : useSymbolic (source.flags node) = false := Bool.eq_false_iff.mpr fallback
      have edges : ∀ edge ∈ source.edges node, ResultExact (EdgeLanguage language classes edge) (localEdge source resolve edge) := by
        intro edge member
        exact localEdge_exact source language classes semantics.intersection edge (semantics.parsed node compact edge member)
          resolve (fun requested present => resolved requested (List.mem_flatMap.mpr ⟨edge, member, present⟩))
      have exact := finishAlternatives_exact (source.edges node) (EdgeLanguage language classes)
        (localEdge source resolve) edges (semantics.disjoint node compact)
      have transformed := (result_ext (fun term => ∃ edge ∈ source.edges node, EdgeLanguage language classes edge term)
        (language node) (fun term => (semantics.rows node compact term).symm) _).mp exact
      simpa [localNode, empty, fallback] using transformed

/-- The derived pure reference is the exact complete node language, by strict structural induction. -/
theorem reference_exact [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node) :
    ResultExact (language node) (reference source measure node) := by
  have all : ∀ budget, ∀ node, measure node = budget → ResultExact (language node) (reference source measure node) := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
        intro node measured
        rw [reference_equation source measure decreases node]
        apply localNode_exact source language classes semantics node
        intro requested member
        apply ih (measure requested) ?_ requested rfl
        have lower := decreases node requested member
        omega
  exact all (measure node) node rfl

/-- The full actual cache driver terminates with the exact distinct node index or a proved empty language. -/
theorem driver_exact [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node) :
    ∃ result after, buildNode source (measure node + 1) node (fun _ => none) = some (result, after) ∧
      ResultExact (language node) result ∧
      ∀ stored compiled, after stored = some compiled → ResultExact (language stored) compiled := by
  obtain ⟨after, found, valid⟩ := buildNode_terminates source measure decreases node
  refine ⟨reference source measure node, after, found, reference_exact source measure decreases language classes semantics node, ?_⟩
  intro stored compiled present
  rw [valid stored compiled present]
  exact reference_exact source measure decreases language classes semantics stored


/-- Public source errors retain the unsupported-constraint distinction. Fuel is only a proof-port error. -/
inductive Error where
  | emptyGenerator
  | cannotCountConstrainedEdges
  | executionBound
  deriving DecidableEq, Repr

/-- Exact compileFiniteAutomaton precheck order and result mapping. -/
def compile [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (indicatorsAvailable : Bool) (fuel : Nat) (root : Node) : Except Error (Index (Term Symbol)) :=
  if (source.edges root).isEmpty then .error .emptyGenerator
  else if !indicatorsAvailable then .error .cannotCountConstrainedEdges
  else match buildNode source fuel root (fun _ => none) with
    | none => .error .executionBound
    | some (none, _) => .error .emptyGenerator
    | some (some compiled, _) => .ok compiled

/-- The actual empty-root check precedes the guard-indicator support check. -/
theorem compile_empty_rows [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (available : Bool) (fuel : Nat) (node : Node) (empty : (source.edges node).isEmpty = true) :
    compile source available fuel node = .error .emptyGenerator := by simp [compile, empty]

/-- Unsupported reachable guards retain the source's specific construction error. -/
theorem compile_unsupported [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (fuel : Nat) (node : Node) (nonempty : (source.edges node).isEmpty = false) :
    compile source false fuel node = .error .cannotCountConstrainedEdges := by simp [compile, nonempty]

/-- The source collapses every symbolic backend failure to a stored Nothing result. -/
theorem symbolic_failure_cached [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (fuel : Nat) (node : Node) (cache : BuildCache Node Symbol)
    (nonempty : (source.edges node).isEmpty = false) (missing : cache node = none)
    (fallback : useSymbolic (source.flags node) = true) (cause : Failure)
    (failed : source.symbolic node = .error cause) :
    buildNode source (fuel + 1) node cache = some (none, Cache.put cache node none) := by
  simp [buildNode, nonempty, missing, fallback, failed, Except.toOption]

/-- Stored empty results are cache hits and do not rerun either compilation backend. -/
theorem cached_empty [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (fuel : Nat) (node : Node) (cache : BuildCache Node Symbol)
    (nonempty : (source.edges node).isEmpty = false) (stored : cache node = some none) :
    buildNode source (fuel + 1) node cache = some (none, cache) := by simp [buildNode, nonempty, stored]

/-- Sufficient source execution has exactly the derived reference's successful indexes. -/
theorem compile_success_iff [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (node : Node) (index : Index (Term Symbol)) :
    compile source true (measure node + 1) node = .ok index ↔ reference source measure node = some index := by
  obtain ⟨after, built, _⟩ := buildNode_terminates source measure decreases node
  by_cases empty : (source.edges node).isEmpty = true
  · have referenceEmpty : reference source measure node = none := by
      simpa [localNode, empty] using reference_equation source measure decreases node
    simp [compile, empty, referenceEmpty]
  · simp [compile, empty, built]
    cases reference source measure node <;> simp

/-- Every valid structural execution rules out the explicit proof-bound failure. -/
theorem compile_no_execution_error [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (available : Bool) (node : Node) : compile source available (measure node + 1) node ≠ .error .executionBound := by
  obtain ⟨after, built, _⟩ := buildNode_terminates source measure decreases node
  unfold compile
  split
  · simp
  · split
    · simp
    · rw [built]
      cases reference source measure node <;> simp

/-- Every successful public object has an exact nonempty language, total distinct decoder, and same-pass inverse. -/
theorem compile_correct [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node) (index : Index (Term Symbol))
    (compiled : compile source true (measure node + 1) node = .ok index) :
    0 < index.count ∧ Correct index ∧ ∀ term, (∃ rank, index.select rank = some term) ↔ language node term := by
  have found := (compile_success_iff source measure decreases node index).mp compiled
  have exact := reference_exact source measure decreases language classes semantics node
  simpa only [found, ResultExact] using exact

/-- The derived optional result is empty exactly when the independent node language is empty. -/
theorem reference_empty_iff [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node) :
    reference source measure node = none ↔ ∀ term, ¬ language node term := by
  have exact := reference_exact source measure decreases language classes semantics node
  cases result : reference source measure node with
  | none => simpa [result, ResultExact] using exact
  | some index =>
      rw [result] at exact
      constructor
      · intro impossible; cases impossible
      · intro empty
        obtain ⟨term, selected⟩ := exact.2.1.total 0 exact.1
        exact False.elim (empty term ((exact.2.2 term).mp ⟨0, selected⟩))

/-- Under supported local backends, the public EmptyGenerator error means exactly an empty node language. -/
theorem compile_empty_iff [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (measure : Node → Nat) (decreases : ∀ node requested, requested ∈ requests source node → measure requested < measure node)
    (language : Node → Term Symbol → Prop) (classes : EdgeSpec Node Symbol → List (List Nat))
    (semantics : Semantics source language classes) (node : Node) :
    compile source true (measure node + 1) node = .error .emptyGenerator ↔ ∀ term, ¬ language node term := by
  rw [← reference_empty_iff source measure decreases language classes semantics node]
  obtain ⟨after, built, _⟩ := buildNode_terminates source measure decreases node
  by_cases empty : (source.edges node).isEmpty = true
  · have referenceEmpty : reference source measure node = none := by
      simpa [localNode, empty] using reference_equation source measure decreases node
    simp [compile, empty, referenceEmpty]
  · simp [compile, empty, built]
    cases reference source measure node <;> simp

/-- Actual acyclic rows, exact copied intersections, and local source adapters give the full driver theorem. -/
theorem driver_from_rows_exact [DecidableEq Node] [DecidableEq Symbol] (source : Source Node Symbol Failure)
    (automaton : Automaton Node Symbol) (rank : Node → Nat)
    (below : ∀ node edge, edge ∈ automaton node → ∀ child ∈ edge.children, rank child < rank node)
    (rows : ∀ node edge, edge ∈ source.edges node → ∃ original ∈ automaton node, original.children = edge.children)
    (copied : SymbolicGraphView.RowsCorrespond (Language.intersect automaton automaton) automaton
      (fun pair => source.meet pair.1 pair.2))
    (classes : EdgeSpec Node Symbol → List (List Nat)) (semantics : Semantics source (Accepts automaton) classes) (node : Node) :
    ∃ result after, buildNode source (SymbolicGraphView.structuralValue automaton rank below node + 1) node (fun _ => none) = some (result, after) ∧
      ResultExact (Accepts automaton node) result ∧
      ∀ stored compiled, after stored = some compiled → ResultExact (Accepts automaton stored) compiled :=
  driver_exact source _ (structural_requests_decrease source automaton rank below rows copied)
    (Accepts automaton) classes semantics node


/-- An exact compiled result has contiguous distinct ranks and exact membership rejection. -/
theorem exact_index_api (language : Value → Prop) (index : Index Value)
    (exact : ResultExact language (some index)) :
    (∀ rank, (∃ value, index.select rank = some value) ↔ rank < index.count) ∧
    (∀ value, index.rank value = none ↔ ¬language value) ∧
    (∀ first second value, index.select first = some value → index.select second = some value → first = second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro rank
    exact ⟨fun ⟨value, found⟩ => exact.2.1.bounded rank value found, exact.2.1.total rank⟩
  · intro value
    constructor
    · intro rejected accepted
      obtain ⟨rank, selected⟩ := (exact.2.2 value).mpr accepted
      have ranked := (exact.2.1.inverse rank value).mpr selected
      rw [rejected] at ranked
      cases ranked
    · intro absent
      cases ranked : index.rank value with
      | none => rfl
      | some rank =>
          have selected := (exact.2.1.inverse rank value).mp ranked
          exact False.elim (absent ((exact.2.2 value).mp ⟨rank, selected⟩))
  · intro first second value a b
    have firstRank := (exact.2.1.inverse first value).mpr a
    have secondRank := (exact.2.1.inverse second value).mpr b
    exact Option.some.inj (firstRank.symm.trans secondRank)

/-- A concrete driver probe with an empty first group and a successful later group. -/
def traversalSource : Source Nat Nat Unit where
  edges node := if node = 0 then [⟨9, [1, 2], some [[0], [1]]⟩] else [⟨node, [], some []⟩]
  flags node := if node = 0 then ⟨false, false, false, false, false⟩ else ⟨true, true, false, false, false⟩
  meet first _ := first
  symbolic node := if node = 1 then .error () else .ok (leafIndex 1)

/-- An empty early group does not suppress later group evaluation or its cache insertion. -/
theorem later_group_cached :
    (buildNode traversalSource 2 0 (fun _ => none)).map
      (fun (result, cache) => (result.isNone, (cache 1).map Option.isNone,
        (cache 2).map (fun result => result.map Index.count))) = some (true, some true, some (some 1)) := by cbv

/-- The stored root empty result is reused by subsequent source queries. -/
theorem root_empty_cached :
    (buildNode traversalSource 2 0 (fun _ => none)).map
      (fun (_, cache) => (cache 0).map Option.isNone) = some (some true) := by cbv


end MicroCFTA.FiniteAutomatonDriver
