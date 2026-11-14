import MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl
import MicroCFTA.SourceSynthesisUniverseRowTransform
import MicroCFTA.SourceRecursiveIntersectionOrdinaryProductRows
import MicroCFTA.InternedNodeSetCongruence
import MicroCFTA.InternedOrdinaryUnionReadback

/-!
# Ordered native body product with the body/Mu cutoff

The actual reference calls retain their domain allocation effects.
The source rows supply every child and every original self pair.
The final cache supplies the complete ordered row readback.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisUniverseOffDiagonalBody
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open EqualityLeafProjectionPhysical (dead)

variable {Symbol Guard : Type}

private theorem aligned_input {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    ∀ selected ∈ inputs, ∃ output ∈ outputs, relation selected output := by
  induction aligned with
  | nil => intro selected member; cases member
  | @cons first output inputs outputs own rest ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨output, List.mem_cons_self, own⟩
      · obtain ⟨other, present, related⟩ := ih selected later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem aligned_output {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    ∀ selected ∈ outputs, ∃ source ∈ inputs, relation source selected := by
  induction aligned with
  | nil => intro selected member; cases member
  | @cons first output inputs outputs own rest ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, own⟩
      · obtain ⟨other, present, related⟩ := ih selected later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem walk_complete {A B : Type}
    (call : A → Machine Symbol Guard → Result Symbol Guard B)
    (base : Machine Symbol Guard) (jobs : List A)
    (steps : ∀ job ∈ jobs, ∀ current, SourceRecursiveIntersectionKernel.Valid current →
      Extension base current → ∃ value after, call job current = .done value after ∧
        SourceRecursiveIntersectionKernel.Valid after ∧ Extension current after)
    (current : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid current)
    (growth : Extension base current) :
    ∃ values final, walk call jobs current = .done values final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension current final := by
  induction jobs generalizing current with
  | nil => exact ⟨[], current, rfl, valid, Extension.refl _⟩
  | cons job jobs ih =>
      obtain ⟨value, after, firstDone, afterValid, firstGrowth⟩ :=
        steps job List.mem_cons_self current valid growth
      obtain ⟨values, final, restDone, finalValid, lastGrowth⟩ :=
        ih (fun other member => steps other (List.mem_cons_of_mem _ member))
          after afterValid (growth.trans firstGrowth)
      exact ⟨value :: values, final,
        by simp only [walk, firstDone, Result.bind, restDone], finalValid, firstGrowth.trans lastGrowth⟩

private theorem children_self_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (referenceAvailable : Available state.heap (.reference (.interned u.identity)))
    (markerAvailable : Available state.heap (.node m markerRows 0 []))
    (bound : u.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (seen : pair b.identity u.identity ∈ domain.key.seen)
    (fresh : pair u.identity u.identity ∉ domain.key.seen)
    (children : List (Value Symbol Guard))
    (kinds : ∀ child ∈ children, child = .node m markerRows 0 [] ∨ child = .reference (.interned u.identity)) :
    ∃ after,
      walk (fun request : Value Symbol Guard × Value Symbol Guard =>
        execute emptyGuard conjoin 8 domain request.1 request.2) (children.zip children) state =
          .done (children.map (input (replacement (.interned u.identity)
            (repeatedValue (pair b.identity u.identity))))) after ∧
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ after.heap = state.heap := by
  induction children generalizing state with
  | nil => exact ⟨state, rfl, valid, Extension.refl _, rfl⟩
  | cons child children ih =>
      let mapped : Value Symbol Guard := input (replacement (.interned u.identity)
        (repeatedValue (pair b.identity u.identity))) child
      have head : ∃ after, execute emptyGuard conjoin 8 domain child child state = .done mapped after ∧
          SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ after.heap = state.heap := by
        rcases kinds child List.mem_cons_self with same | same
        · subst child
          have markerRead : mapped = .node m markerRows 0 [] :=
            InternedStoredSubstitutionScope.input_closed _ _ rfl
          exact ⟨state, by simpa only [markerRead] using
              SourceSynthesisUniverseRowProducts.execute_marker_self emptyGuard conjoin 6 domain m markerRows 0 state,
            valid, Extension.refl _, rfl⟩
        · subst child
          let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
            (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary)
            (.reference (.interned u.identity) : Value Symbol Guard) u.identity u.identity
          let after : Machine Symbol Guard := {state with domains := entered.2}
          have returned : execute emptyGuard conjoin 8 domain (.reference (.interned u.identity))
              (.reference (.interned u.identity)) state = .done mapped after := by
            simpa only [mapped, input, replacement, repeatedValue, ite_true, Option.getD_some] using
              SourceSynthesisUniverseOffDiagonalReferenceControl.execute_ref_self_off_diagonal_eight
                emptyGuard conjoin u b bodyRows depth ordinary domain state valid.1 valid.2 universeAvailable bound seen fresh
          have checked := execute_checked emptyGuard conjoin 8 domain
            (.reference (.interned u.identity)) (.reference (.interned u.identity)) state valid known
            referenceAvailable referenceAvailable
          exact ⟨after, returned, by simpa only [returned, Result.state] using checked.valid,
            by simpa only [returned, Result.state] using checked.extension, rfl⟩
      obtain ⟨after, headDone, afterValid, headGrowth, heapSame⟩ := head
      obtain ⟨final, restDone, finalValid, restGrowth, heapSameRest⟩ :=
        ih after afterValid (known.grows domain headGrowth) (headGrowth.available _ universeAvailable)
          (headGrowth.available _ referenceAvailable) (headGrowth.available _ markerAvailable)
          (fun other member => kinds other (List.mem_cons_of_mem _ member))
      exact ⟨final, by simp only [List.zip_cons_cons, List.map_cons, walk, headDone, Result.bind, restDone, mapped],
        finalValid, headGrowth.trans restGrowth, heapSameRest.trans heapSame⟩

private theorem edge_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (referenceAvailable : Available state.heap (.reference (.interned u.identity)))
    (markerAvailable : Available state.heap (.node m markerRows 0 []))
    (bound : u.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (seen : pair b.identity u.identity ∈ domain.key.seen)
    (fresh : pair u.identity u.identity ∉ domain.key.seen)
    (left right : EdgeValue Symbol Guard)
    (leftTop : left.entry.key.constraint = top) (rightTop : right.entry.key.constraint = top)
    (kinds : ∀ child ∈ left.children, child = .node m markerRows 0 [] ∨ child = .reference (.interned u.identity))
    (compatible : left.children.length = right.children.length → left.children = right.children) :
    ∃ row after,
      edge top conjoin (execute top conjoin 8 domain) left right state = .done row after ∧
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ EdgeResident after.heap row ∧
      (left.children.length = right.children.length →
        row.children = left.children.map (input (replacement (.interned u.identity)
          (repeatedValue (pair b.identity u.identity)))) ∧
        row.entry.key = ⟨left.entry.key.symbol,
          (left.children.map (input (replacement (.interned u.identity)
            (repeatedValue (pair b.identity u.identity))))).map Value.referenceOf, top⟩ ∧
        dead row = false ∧
        run (makeEdge left.entry.key.symbol top (left.children.map
          (input (replacement (.interned u.identity) (repeatedValue (pair b.identity u.identity))))))
          state.heap = (row, after.heap)) ∧
      (left.children.length ≠ right.children.length → dead row = true) := by
  let cutoff := repeatedValue (pair b.identity u.identity) (Symbol := Symbol) (Guard := Guard)
  let targets := left.children.map (input (replacement (.interned u.identity) cutoff))
  have targetAvailable : ∀ value ∈ targets, Available state.heap value := by
    intro value member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    rcases kinds source present with same | same
    · rw [same, InternedStoredSubstitutionScope.input_closed _ _ rfl]
      exact markerAvailable
    · rw [same]
      simp only [input, replacement, ite_true, Option.getD_some]
      apply reference_available
      intro name member
      simp [Value.free] at member
  by_cases arity : left.children.length = right.children.length
  · have sameChildren := compatible arity
    obtain ⟨middle, walked, middleValid, firstGrowth, heapSame⟩ :=
      children_self_complete top conjoin u b m bodyRows markerRows depth ordinary domain state valid known
        universeAvailable referenceAvailable markerAvailable bound seen fresh left.children kinds
    let made := run (makeEdge left.entry.key.symbol top targets) state.heap
    let after : Machine Symbol Guard := {middle with heap := made.2}
    have makeDone : SourceRecursiveIntersectionKernel.work (makeEdge left.entry.key.symbol top targets) middle =
        .done made.1 after := by simp only [SourceRecursiveIntersectionKernel.work, heapSame]; rfl
    have availableMiddle : ∀ value ∈ targets, Available middle.heap value := by
      simpa only [heapSame] using targetAvailable
    have checked := work_checked middle middleValid (makeEdge left.entry.key.symbol top targets) EdgeResident
      (InternedNestedFacts.edge_verified _ _ targets middle.heap middleValid.1 availableMiddle)
    have fields := InternedGuardedExecutionLists.makeEdge_fields left.entry.key.symbol top targets state.heap
      valid.1.coherent valid.1.cached targetAvailable
    have live : dead made.1 = false := by
      unfold dead
      rw [fields.2]
      apply List.any_eq_false.mpr
      intro value member
      obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
      rcases kinds source present with same | same
      · rw [same, InternedStoredSubstitutionScope.input_closed _ _ rfl]
        simp [Value.referenceOf]
      · rw [same]
        simp [input, replacement, cutoff, repeatedValue, Value.referenceOf]
    refine ⟨made.1, after, ?_, ?_, firstGrowth.trans ?_, checked.result _ _ makeDone, ?_, ?_⟩
    · simp only [edge, arity, ite_true, ← sameChildren, leftTop, rightTop, conjoinTop, walked, Result.bind]
      exact makeDone
    · simpa only [makeDone, Result.state] using checked.valid
    · simpa only [makeDone, Result.state] using checked.extension
    · intro _
      exact ⟨fields.2, fields.1, live, rfl⟩
    · exact fun different => False.elim (different arity)
  · let made := run (makeEdge left.entry.key.symbol top [.empty]) state.heap
    let after : Machine Symbol Guard := {state with heap := made.2}
    have returned : edge top conjoin (execute top conjoin 8 domain) left right state = .done made.1 after := by
      simp only [edge, arity, ite_false, SourceRecursiveIntersectionKernel.work]
      rfl
    have makeDone : SourceRecursiveIntersectionKernel.work (makeEdge left.entry.key.symbol top [.empty]) state =
        .done made.1 after := rfl
    have availableEmpty : ∀ value ∈ ([.empty] : List (Value Symbol Guard)), Available state.heap value := by
      intro value member
      rw [List.mem_singleton.mp member]
      exact empty_available state.heap
    have checked := work_checked state valid (makeEdge left.entry.key.symbol top [.empty]) EdgeResident
      (InternedNestedFacts.edge_verified _ _ [.empty] state.heap valid.1 availableEmpty)
    have children := InternedShallowValues.makeEdge_children left.entry.key.symbol top [.empty] state.heap
      valid.1.coherent valid.1.cached availableEmpty
    refine ⟨made.1, after, returned, ?_, ?_, checked.result _ _ makeDone,
      (fun same => False.elim (arity same)), ?_⟩
    · simpa only [makeDone, Result.state] using checked.valid
    · simpa only [makeDone, Result.state] using checked.extension
    · intro _
      unfold dead
      rw [children]
      rfl

/-- Native body execution derives its actual off-diagonal product and complete ordered source row readback. -/
theorem node_target_readback
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (referenceAvailable : Available state.heap (.reference (.interned u.identity)))
    (markerAvailable : Available state.heap (.node m markerRows 0 []))
    (bound : u.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (seen : pair b.identity u.identity ∈ domain.key.seen)
    (fresh : pair u.identity u.identity ∉ domain.key.seen)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m markerRows 0 [] ∨ child = .reference (.interned u.identity))
    (functional : ∀ left ∈ bodyRows, ∀ right ∈ bodyRows,
      left.entry.key.symbol = right.entry.key.symbol → left.children.length = right.children.length →
        left.children = right.children)
    (arrow : EdgeValue Symbol Guard) (arrowMember : arrow ∈ bodyRows)
    (arrowChildren : arrow.children = [.node m markerRows 0 [],
      .reference (.interned u.identity), .reference (.interned u.identity)]) :
    ∃ product final entry targets,
      node top conjoin (execute top conjoin 8 domain) bodyRows bodyRows state = .done product final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension state final ∧ Available final.heap product ∧
      product = .node entry (canonicalEdges targets) 0
        [.intersection (pair b.identity u.identity).1 (pair b.identity u.identity).2] ∧
      All₂ (fun (source : EdgeValue Symbol Guard) target =>
        target.children = source.children.map (input (replacement (.interned u.identity)
          (repeatedValue (pair b.identity u.identity)))) ∧
        target.entry.key = ⟨source.entry.key.symbol,
          (source.children.map (input (replacement (.interned u.identity)
            (repeatedValue (pair b.identity u.identity))))).map Value.referenceOf, top⟩) bodyRows targets ∧
      (∀ target ∈ targets, EdgeResident final.heap target) ∧
      (∀ target ∈ targets, dead target = false) ∧
      run (makeNode targets) final.heap = (product, final.heap) := by
  let cutoff : Reference := .intersection (pair b.identity u.identity).1 (pair b.identity u.identity).2
  let reads := fun (source target : EdgeValue Symbol Guard) =>
    target.children = source.children.map (input (replacement (.interned u.identity) (.reference cutoff))) ∧
    target.entry.key = ⟨source.entry.key.symbol,
      (source.children.map (input (replacement (.interned u.identity) (.reference cutoff)))).map Value.referenceOf, top⟩
  have bodyAvailable : Available state.heap (.node b bodyRows 0 [.interned u.identity]) :=
    universeAvailable.children _ (by simp [InternedProbeProvenance.children])
  have resident : ∀ row ∈ bodyRows, EdgeResident state.heap row :=
    fun row member => valid.1.linked b.key _ (bodyAvailable.resident b rfl) row member
  obtain ⟨products, middle, walked, middleValid, firstGrowth⟩ := walk_complete
    (fun job : EdgeValue Symbol Guard × EdgeValue Symbol Guard =>
      edge top conjoin (execute top conjoin 8 domain) job.1 job.2)
    state (pairs bodyRows bodyRows) (by
      intro job member current currentValid currentGrowth
      obtain ⟨leftIn, rightIn, sameSymbol⟩ := (pairs_member bodyRows bodyRows job).mp member
      obtain ⟨row, after, returned, afterValid, growth, _resident, _readback, _dead⟩ :=
        edge_complete top conjoin conjoinTop u b m bodyRows markerRows depth ordinary domain current
          currentValid (known.grows domain currentGrowth) (currentGrowth.available _ universeAvailable)
          (currentGrowth.available _ referenceAvailable) (currentGrowth.available _ markerAvailable)
          bound seen fresh job.1 job.2 (bodyTop job.1 leftIn) (bodyTop job.2 rightIn)
          (bodyChildren job.1 leftIn) (functional job.1 leftIn job.2 rightIn sameSymbol)
      exact ⟨row, after, returned, afterValid, growth⟩)
    state valid (Extension.refl _)
  have checkedRows := rows_checked top conjoin _ (execute_checked top conjoin 8)
    domain bodyRows bodyRows state valid known resident resident
  have productMiddle : ∀ row ∈ products, EdgeResident middle.heap row := checkedRows.result _ _ walked
  let made := run (makeNode products) middle.heap
  let final : Machine Symbol Guard := {middle with heap := made.2}
  have madeDone : work (makeNode products) middle = .done made.1 final := rfl
  have checkedNode := work_checked middle middleValid (makeNode products) Available
    (InternedNestedFacts.node_verified products middle.heap middleValid.1 productMiddle)
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by
    simpa only [madeDone, Result.state] using checkedNode.valid
  have lastGrowth : Extension middle final := by
    simpa only [madeDone, Result.state] using checkedNode.extension
  have growth : Extension state final := firstGrowth.trans lastGrowth
  have available : Available final.heap made.1 := checkedNode.result _ _ madeDone
  have done : node top conjoin (execute top conjoin 8 domain) bodyRows bodyRows state = .done made.1 final := by
    simp only [node, walked, Result.bind]
    exact madeDone
  have replayed := rows_pointwise_replay top conjoin _ (execute_checked top conjoin 8)
    (execute_replay top conjoin 8) domain bodyRows bodyRows state final products middle
    valid known resident resident walked lastGrowth
  have productResident : ∀ row ∈ products, EdgeResident final.heap row :=
    fun row member => edge_grows _ _ lastGrowth.heap row (productMiddle row member)
  have replayedNode := work_replay (makeNode products) middle final made.1 final middleValid madeDone (Extension.refl final)
  have replayedFields := work_done (makeNode products) final made.1 final replayedNode
  have pureNode : run (makeNode products) final.heap = (made.1, final.heap) := by
    exact Prod.ext replayedFields.1.symm (congrArg Machine.heap replayedFields.2).symm
  have finalKnown := known.grows domain growth
  have finalUniverse := growth.available _ universeAvailable
  have finalReference := growth.available _ referenceAvailable
  have finalMarker := growth.available _ markerAvailable
  have each : ∀ source ∈ bodyRows, ∃ target ∈ products, reads source target ∧ dead target = false := by
    intro source member
    have selfMember : (source, source) ∈ pairs bodyRows bodyRows :=
      (pairs_member bodyRows bodyRows (source, source)).mpr ⟨member, member, rfl⟩
    obtain ⟨target, targetIn, returned⟩ := aligned_input replayed (source, source) selfMember
    obtain ⟨result, after, completed, _valid, _growth, _resident, readback, _dead⟩ :=
      edge_complete top conjoin conjoinTop u b m bodyRows markerRows depth ordinary domain final
        finalValid finalKnown finalUniverse finalReference finalMarker bound seen fresh source source
        (bodyTop source member) (bodyTop source member) (bodyChildren source member) (fun _ => rfl)
    have same := (Result.done.inj (completed.symm.trans returned)).1
    have fields := readback rfl
    refine ⟨target, targetIn, ?_, ?_⟩
    · simpa only [reads, cutoff, repeatedValue, ← same] using And.intro fields.1 fields.2.1
    · simpa only [← same] using fields.2.2.1
  have gather (sources : List (EdgeValue Symbol Guard)) :
      (∀ source ∈ sources, source ∈ bodyRows) →
      ∃ targets, All₂ reads sources targets ∧
        (∀ target ∈ targets, target ∈ products) ∧ (∀ target ∈ targets, dead target = false) := by
    induction sources with
    | nil =>
        intro _
        refine ⟨[], .nil, ?_, ?_⟩
        · intro row member
          cases member
        · intro row member
          cases member
    | cons source sources ih =>
        intro included
        obtain ⟨target, targetIn, readback, live⟩ := each source (included source List.mem_cons_self)
        obtain ⟨targets, aligned, retained, liveRows⟩ :=
          ih (fun other member => included other (List.mem_cons_of_mem _ member))
        refine ⟨target :: targets, .cons readback aligned, ?_, ?_⟩
        · intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact targetIn
          · exact retained other later
        · intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact live
          · exact liveRows other later
  obtain ⟨targets, aligned, retained, targetLive⟩ := gather bodyRows (fun _ member => member)
  have targetResident : ∀ row ∈ targets, EdgeResident final.heap row :=
    fun row member => productResident row (retained row member)
  have origins : ∀ row ∈ products, dead row = false → ∃ source ∈ bodyRows, reads source row := by
    intro row member live
    obtain ⟨job, jobIn, returned⟩ := (pointwise_result_member
      (fun job : EdgeValue Symbol Guard × EdgeValue Symbol Guard =>
        edge top conjoin (execute top conjoin 8 domain) job.1 job.2 final)
      (pairs bodyRows bodyRows) products final replayed row).mp member
    obtain ⟨leftIn, rightIn, sameSymbol⟩ := (pairs_member bodyRows bodyRows job).mp jobIn
    obtain ⟨result, after, completed, _valid, _growth, _resident, readback, deadRow⟩ :=
      edge_complete top conjoin conjoinTop u b m bodyRows markerRows depth ordinary domain final
        finalValid finalKnown finalUniverse finalReference finalMarker bound seen fresh job.1 job.2
        (bodyTop job.1 leftIn) (bodyTop job.2 rightIn) (bodyChildren job.1 leftIn)
        (functional job.1 leftIn job.2 rightIn sameSymbol)
    have same := (Result.done.inj (completed.symm.trans returned)).1
    by_cases arity : job.1.children.length = job.2.children.length
    · have fields := readback arity
      exact ⟨job.1, leftIn, by simpa only [reads, cutoff, repeatedValue, ← same] using And.intro fields.1 fields.2.1⟩
    · have deadActual : dead row = true := by simpa only [← same] using deadRow arity
      simp only [live, Bool.false_eq_true] at deadActual
  have sameNode : makeNode products = makeNode targets := by
    apply InternedNodeSetCongruence.makeNode_same_members final.heap finalValid.1.coherent
      products targets productResident targetResident
    intro row
    simp only [surviving, List.mem_filter, Bool.not_eq_true']
    change (row ∈ products ∧ dead row = false) ↔ (row ∈ targets ∧ dead row = false)
    constructor
    · rintro ⟨present, live⟩
      obtain ⟨source, included, rowRead⟩ := origins row present live
      obtain ⟨target, selected, targetRead⟩ := aligned_input aligned source included
      have key : row.entry.key = target.entry.key := rowRead.2.trans targetRead.2.symm
      have first : final.heap.edgeRecords row.entry.key = some row := productResident row present
      have second : final.heap.edgeRecords target.entry.key = some target := targetResident target selected
      rw [key] at first
      have equal : row = target := Option.some.inj (first.symm.trans second)
      subst row
      exact ⟨selected, targetLive target selected⟩
    · rintro ⟨present, live⟩
      exact ⟨retained row present, live⟩
  have pureTargets : run (makeNode targets) final.heap = (made.1, final.heap) := by
    rw [← sameNode]
    exact pureNode
  have targetChildren : ∀ target ∈ targets, ∀ child ∈ target.children,
      child = .node m markerRows 0 [] ∨ child = .reference cutoff := by
    intro target member child present
    obtain ⟨source, included, readback⟩ := aligned_output aligned target member
    rw [readback.1] at present
    obtain ⟨original, originalIn, mapped⟩ := List.mem_map.mp present
    rcases bodyChildren source included original originalIn with same | same
    · left
      rw [same, InternedStoredSubstitutionScope.input_closed _ _ rfl] at mapped
      exact mapped.symm
    · right
      simpa [same, input, replacement] using mapped.symm
  obtain ⟨arrowTarget, arrowIn, arrowRead⟩ := aligned_input aligned arrow arrowMember
  have arrowTargetChildren : arrowTarget.children = [.node m markerRows 0 [],
      .reference cutoff, .reference cutoff] := by
    rw [arrowRead.1, arrowChildren]
    simp [input, replacement]
  have zero : ∀ child ∈ targets.flatMap EdgeValue.children, child.depth = 0 := by
    intro child present
    obtain ⟨target, included, childIn⟩ := List.mem_flatMap.mp present
    rcases targetChildren target included child childIn with same | same <;> rw [same] <;> rfl
  have only : ∀ child ∈ targets.flatMap EdgeValue.children, ∀ name ∈ child.free, name = cutoff := by
    intro child present name named
    obtain ⟨target, included, childIn⟩ := List.mem_flatMap.mp present
    rcases targetChildren target included child childIn with same | same
    · rw [same] at named
      cases named
    · simpa only [same, Value.free, List.mem_singleton] using named
  have witness : ∃ target ∈ targets, dead target = false ∧ ∃ child ∈ target.children, cutoff ∈ child.free := by
    refine ⟨arrowTarget, arrowIn, targetLive arrowTarget arrowIn, .reference cutoff, ?_, ?_⟩
    · rw [arrowTargetChildren]
      simp
    · simp [Value.free]
  obtain ⟨entry, nodeRead⟩ := InternedOrdinaryUnionReadback.makeNode_zero_singleton targets final.heap
    finalValid.1.coherent finalValid.1.linked targetResident cutoff zero only witness
  have valueRead : made.1 = .node entry (canonicalEdges (surviving targets)) 0 [cutoff] := by
    simpa only [pureTargets] using nodeRead
  have survivingTargets : surviving targets = targets := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    change (!dead row) = true
    simp only [targetLive row member, Bool.not_false]
  rw [survivingTargets] at valueRead
  exact ⟨made.1, final, entry, targets, done, finalValid, growth, available, valueRead,
    aligned, targetResident, targetLive, pureTargets⟩

end MicroCFTA.SourceSynthesisUniverseOffDiagonalBody
