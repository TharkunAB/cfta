import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRawReads

/-!
# Admission at every actual reached ordinary outer entry

Numeric plans supply only parent capacity. Initial admission supplies
the physical facts at the root. Earlier completed raw prefixes receive
their own strict reads before their exact Post and domain facts are used.
Step induction then derives admission at every reached entry. This gives
the existing outer range plan without a completed enclosing call.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterAdmission
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Step Reach)
open SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries (Plan Admitted)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Each source entry transition derives the current physical and domain admission facts. -/
theorem step {budget : Nat} {first last : Entry (bits + 2)}
    (one : Step budget first last) (initial : Admitted formulas solver first)
    (plan : Plan bits budget first) : Admitted formulas solver last := by
  cases one with
  | @node_evaluate request before handle running owner started =>
      obtain ⟨inventory, memos, context, stored, inherited, available, domain⟩ := initial
      obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
        context inherited available started
      obtain ⟨_same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate formulas solver
        request owner before running handle context.sound context.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited available domain started
      have retained : Stored running := by simpa only [started] using stored.beginNode request
      exact ⟨inventory, memos, current, retained, good.inherited, good.input, ownerDomain⟩
  | @node_ordinary inherited entry edges depth free before =>
      obtain ⟨inventory, memos, context, stored, inheritedReady, available, domain⟩ := initial
      exact ⟨inventory, memos, context, stored, inheritedReady,
        InternedEdgeResidency.resident_edges _ context.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident,
        domain.rows⟩
  | @edge_evaluate request before handle running owner started =>
      obtain ⟨inventory, memos, context, stored, inherited, resident, domain⟩ := initial
      obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
        context inherited resident started
      obtain ⟨_same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver
        request owner before running handle context.sound context.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited resident domain started
      have retained : Stored running := by simpa only [started] using stored.beginEdge request
      exact ⟨inventory, memos, current, retained, good.inherited, good.input, ownerDomain⟩
  | @rows_edge inherited original originals before =>
      obtain ⟨inventory, memos, context, stored, inheritedReady, resident, domain⟩ := initial
      exact ⟨inventory, memos, context, stored, inheritedReady, resident original List.mem_cons_self,
        domain.member original List.mem_cons_self⟩
  | @rows_descendants inherited original before narrowed middle originals earlier =>
      obtain ⟨inventory, memos, context, stored, inheritedReady, resident, domain⟩ := initial
      have originalResident := resident original List.mem_cons_self
      have originalDomain := domain.member original List.mem_cons_self
      obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.edge_call (bits := bits) (formulas := formulas) (solver := solver) earlier
        inventory context inheritedReady originalResident originalDomain stored (plan.restrict (.direct .rows_edge))
      obtain ⟨_checks, next, post, output, returned, bound, _law⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_call formulas solver reads inventory context
          inheritedReady originalResident originalDomain stored
      exact ⟨next, final, post.context, returned, inheritedReady.grows post.effects.grows.constraint_growth, output, bound.1⟩
  | @rows_tail inherited original before narrowed middle result afterChildren originals earlier children =>
      obtain ⟨inventory, memos, context, stored, inheritedReady, resident, domain⟩ := initial
      have originalResident := resident original List.mem_cons_self
      have originalDomain := domain.member original List.mem_cons_self
      obtain ⟨current, firstReads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.edge_call (bits := bits) (formulas := formulas) (solver := solver) earlier
        inventory context inheritedReady originalResident originalDomain stored (plan.restrict (.direct .rows_edge))
      obtain ⟨_firstChecks, next, firstPost, output, firstStored, bound, _firstLaw⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_call formulas solver firstReads inventory context
          inheritedReady originalResident originalDomain stored
      have nextInherited := inheritedReady.grows firstPost.effects.grows.constraint_growth
      obtain ⟨final, childReads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.descendants (bits := bits) (formulas := formulas) (solver := solver) children
        next firstPost.context nextInherited output bound.1 firstStored (plan.restrict (.direct (.rows_descendants earlier)))
      obtain ⟨_childChecks, afterInventory, childPost, _resultResident, childStored, _childBound, _childLaw⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants formulas solver childReads next firstPost.context
          nextInherited output bound.1 firstStored
      have kept := firstPost.effects.keeps.trans childPost.effects.keeps
      cases domain with
      | cons _ rest =>
          exact ⟨afterInventory, final, childPost.context, childStored,
            nextInherited.grows childPost.effects.grows.constraint_growth,
            (fun edge member => edge_grows _ _ kept.growth edge (resident edge (List.mem_cons_of_mem _ member))), rest⟩
  | @descendants_children inherited payload edge before combined =>
      obtain ⟨inventory, memos, context, stored, inheritedReady, resident, domain⟩ := initial
      obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
        context edge inherited payload resident inheritedReady combined
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
      exact ⟨inventory, memos, post.context, stored.prefixState edge inherited, receipt.combinedReady,
        (fun value member => post.effects.keeps.available value (available value member)), domain⟩
  | children_live => exact initial
  | @walk_node combined index value values before =>
      obtain ⟨inventory, memos, context, stored, inherited, available, domain⟩ := initial
      obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
        context combined index inherited
      exact ⟨inventory, memos, post.context, stored.descend combined index, receipt.inherited,
        post.effects.keeps.available value (available value List.mem_cons_self), domain.member value List.mem_cons_self⟩
  | @walk_tail before combined index value result middle values earlier =>
      obtain ⟨inventory, memos, context, stored, inherited, available, domain⟩ := initial
      obtain ⟨receipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
        context combined index inherited
      have firstAvailable := prefixPost.effects.keeps.available value (available value List.mem_cons_self)
      have firstDomain := domain.member value List.mem_cons_self
      obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.node_call (bits := bits) (formulas := formulas) (solver := solver) earlier
        inventory prefixPost.context receipt.inherited firstAvailable firstDomain (stored.descend combined index)
        (plan.restrict (.direct .walk_node))
      obtain ⟨_checks, next, post, _output, returned, _bound, _law⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver reads inventory prefixPost.context
          receipt.inherited firstAvailable firstDomain (stored.descend combined index)
      have total := prefixPost.trans post
      cases domain with
      | cons _ rest =>
          exact ⟨next, final, post.context, returned, inherited.grows total.effects.grows.constraint_growth,
            (fun child member => total.effects.keeps.available child (available child (List.mem_cons_of_mem _ member))), rest⟩

/-- Induction on actual entry paths derives each reached state from the root's initial admission. -/
theorem reach {budget : Nat} {root entry : Entry (bits + 2)}
    (reached : Reach budget root entry) (initial : Admitted formulas solver root)
    (plan : Plan bits budget root) : Admitted formulas solver entry := by
  revert initial plan
  induction reached with
  | refl => intro initial _; exact initial
  | direct one => intro initial plan; exact step bits formulas solver one initial plan
  | trans first _ firstIH restIH =>
      intro initial plan
      exact restIH (firstIH initial plan) (plan.restrict first)

/-- Numeric capacity and derived admission discharge every old raw-reached parent range obligation. -/
theorem ranges {budget : Nat} {root : Entry (bits + 2)}
    (initial : Admitted formulas solver root) (plan : Plan bits budget root) :
    SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget root := by
  intro request before reached
  obtain ⟨inventory, memos, context, stored, inherited, resident, domain⟩ :=
    reach bits formulas solver reached initial plan
  exact SourceCurrentAllocatedFiniteOrdinaryParentCapacity.resident_ranges bits formulas solver budget request
    context inherited resident domain stored (plan request before reached)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterAdmission
