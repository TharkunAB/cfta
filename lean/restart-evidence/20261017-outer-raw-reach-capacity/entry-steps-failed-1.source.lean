import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources

/-!
# Initial resource invariants through raw outer entry steps

Each completed raw prefix receives independent strict reads.
Its exact Work reserves capacity for the original suffix.
The invariant follows the original Step relation and its full domain.
No future entry Plan is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntrySteps
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Step)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs (Admitted)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Every literal raw entry transition preserves initial resource admission. -/
theorem step {budget : Nat} {first last : Entry (bits + 2)}
    (one : Step budget first last) (initial : Admitted bits formulas solver first) :
    Admitted bits formulas solver last := by
  cases one with
  | @node_evaluate request before handle running owner started =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
        available, domain, profile, guards, heightBound, room, active⟩ := initial
      obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
        context inherited available started
      obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate formulas solver
        request owner before running handle context.sound context.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited available domain started
      have retained : Stored running := by simpa only [started] using stored.beginNode request
      have checked : running.checked = before.checked := by
        simpa only [started] using (beginNode_components request before).1
      have smaller : nodeRank request - 1 < nodeRank request := by simp only [nodeRank]; omega
      have pushed := SourceCurrentAllocatedPartialActiveOrder.node_push formulas solver context.sound
        context.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available active smaller started
      have ownerActive : ActiveAbove (nodeRank owner - 1) running := by simpa only [nodeRank, same] using pushed
      exact ⟨inventory, memos, rows, arity, bound, limits, current, retained, good.inherited, good.input,
        ownerDomain, by simpa only [same] using profile, by simpa only [same] using guards,
        by simpa only [same] using heightBound, by simpa only [checked] using room, ownerActive⟩
  | @node_ordinary inherited entry edges depth free before =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        available, domain, profile, guards, heightBound, room, active⟩ := initial
      have resident := resident_edges _ context.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
      cases bound with
      | zero => simp only [height] at heightBound; omega
      | succ bound =>
          have rowsHeight : edgesHeight edges ≤ bound := Nat.le_of_add_le_add_right heightBound
          have rowsRoom : Headroom bits before.checked.native.machine.heap
              (edges.length * rowNodes rows arity limits bound) (edges.length * rowEdges rows arity limits bound) := by
            apply room.mono
            · have enough := Nat.mul_le_mul_right (rowNodes rows arity limits bound) profile.1
              change edges.length * rowNodes rows arity limits bound ≤ 1 + rows * rowNodes rows arity limits bound
              omega
            · exact Nat.mul_le_mul_right (rowEdges rows arity limits bound) profile.1
          refine ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
            resident, domain.rows, profile.2, guards, rowsHeight, rowsRoom,
            nodeRank ⟨inherited, .node entry edges depth free⟩ - 1, active, ?_⟩
          intro edge member
          have smaller := SourceCurrentAllocatedPartialActiveOrder.edge_lt_node inherited entry edges depth free edge member
          omega
  | @edge_evaluate request before handle running owner started =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
        resident, domain, profile, guards, heightBound, room, _active⟩ := initial
      obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
        context inherited resident started
      obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver
        request owner before running handle context.sound context.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited resident domain started
      have retained : Stored running := by simpa only [started] using stored.beginEdge request
      have checked : running.checked = before.checked := by
        simpa only [started] using (beginEdge_components request before).1
      exact ⟨inventory, memos, rows, arity, bound, limits, current, retained, good.inherited, good.input,
        ownerDomain, by simpa only [same] using profile, by simpa only [same] using guards,
        by simpa only [same] using heightBound, by simpa only [checked] using room, trivial⟩
  | @rows_edge inherited original originals before =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        resident, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      have edgeRoom : Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) := by
        apply room.mono
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowNodes]; omega
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowEdges]; omega
      exact ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        resident original List.mem_cons_self, domain.member original List.mem_cons_self, profile.1, guards.1,
        Nat.le_trans (Nat.le_max_left _ _) heightBound, edgeRoom,
        active.mono (smaller original List.mem_cons_self)⟩
  | @rows_descendants inherited original before narrowed middle originals earlier =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        resident, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      have originalHeight : edgeHeight original ≤ bound := Nat.le_trans (Nat.le_max_left _ _) heightBound
      let childNodes := descendantsNodes (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound
      let childEdges := descendantsEdges (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound
      have splitRoom : Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rows arity bound + (childNodes + originals.length * rowNodes rows arity limits bound))
          (edgeBudget limits rows arity bound + (childEdges + originals.length * rowEdges rows arity limits bound)) := by
        apply room.mono
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowNodes, childNodes, descendantsNodes]; omega
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowEdges, childEdges, descendantsEdges]; omega
      have edgeRoom := splitRoom.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      obtain ⟨next, final, reads, _checks, post, output, returned, narrow, certificate, work⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.edge_call bits formulas solver earlier inventory context
          inheritedReady (resident original List.mem_cons_self) (domain.member original List.mem_cons_self) stored
          (active.mono (smaller original List.mem_cons_self)) rows arity bound limits profile.1 guards.1 originalHeight edgeRoom
      have outputProfile := certificate rows arity bound limits profile.1 guards.1 originalHeight
      have remaining := splitRoom.after work
      refine ⟨next, final, parentRows limits rows arity bound, max arity 1, bound, parentGuards limits,
        post.context, returned, inheritedReady.grows post.effects.grows.constraint_growth, output,
        narrow.1, outputProfile.1, outputProfile.2, Nat.le_trans narrow.2 originalHeight,
        remaining.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _), cap,
        (SourceCurrentAllocatedPartialActiveFrames.edge_call earlier).activeExcept active, ?_⟩
      intro value member
      have lower := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited narrowed value member
      have originalSmaller := smaller original List.mem_cons_self
      have height := narrow.2
      simp only [nodeRank, edgeRank] at lower originalSmaller ⊢
      omega
  | @rows_tail inherited original before narrowed middle result afterChildren originals earlier children =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        resident, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      have originalHeight : edgeHeight original ≤ bound := Nat.le_trans (Nat.le_max_left _ _) heightBound
      let childNodes := descendantsNodes (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound
      let childEdges := descendantsEdges (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound
      have splitRoom : Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rows arity bound + (childNodes + originals.length * rowNodes rows arity limits bound))
          (edgeBudget limits rows arity bound + (childEdges + originals.length * rowEdges rows arity limits bound)) := by
        apply room.mono
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowNodes, childNodes, descendantsNodes]; omega
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, rowEdges, childEdges, descendantsEdges]; omega
      have edgeRoom := splitRoom.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      obtain ⟨next, edgeMemos, reads, _checks, edgePost, output, edgeStored, narrow, certificate, work⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.edge_call bits formulas solver earlier inventory context
          inheritedReady (resident original List.mem_cons_self) (domain.member original List.mem_cons_self) stored
          (active.mono (smaller original List.mem_cons_self)) rows arity bound limits profile.1 guards.1 originalHeight edgeRoom
      have outputProfile := certificate rows arity bound limits profile.1 guards.1 originalHeight
      have remaining := splitRoom.after work
      have childSmall : ∀ value ∈ narrowed.children, nodeRank ⟨inherited, value⟩ ≤ cap := by
        intro value member
        have lower := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited narrowed value member
        have originalSmaller := smaller original List.mem_cons_self
        have height := narrow.2
        simp only [nodeRank, edgeRank] at lower originalSmaller ⊢
        omega
      obtain ⟨afterInventory, final, childReads, _childChecks, childPost, _childOutput, childStored,
        _childNarrow, _childCertificate, childWork⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.descendants bits formulas solver children next edgePost.context
          (inheritedReady.grows edgePost.effects.grows.constraint_growth) output narrow.1 edgeStored cap
          ((SourceCurrentAllocatedPartialActiveFrames.edge_call earlier).activeExcept active) childSmall
          (parentRows limits rows arity bound) (max arity 1) bound (parentGuards limits)
          outputProfile.1 outputProfile.2 (Nat.le_trans narrow.2 originalHeight)
          (remaining.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      have tailRoom := remaining.after childWork
      have total := edgePost.trans childPost
      cases domain with
      | cons _ rest =>
          exact ⟨afterInventory, final, rows, arity, bound, limits, childPost.context, childStored,
            inheritedReady.grows total.effects.grows.constraint_growth,
            (fun edge member => edge_grows _ _ total.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))),
            rest, profile.2, guards.2, Nat.le_trans (Nat.le_max_right _ _) heightBound, tailRoom, cap,
            (SourceCurrentAllocatedPartialActiveFrames.descendants children).activeExcept
              ((SourceCurrentAllocatedPartialActiveFrames.edge_call earlier).activeExcept active),
            (fun edge member => smaller edge (List.mem_cons_of_mem _ member))⟩
  | @descendants_children inherited payload edge before combined =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inheritedReady,
        resident, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
        context edge inherited payload resident inheritedReady combined
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
      have retained : Stored (prefixState before edge inherited) := stored.advancePhysical _
      have childRoom : Headroom bits (prefixState before edge inherited).checked.native.machine.heap
          (edge.children.length * nodeNodes rows arity limits bound) (edge.children.length * nodeEdges rows arity limits bound) := by
        change Headroom bits before.checked.native.machine.heap _ _
        apply room.mono
        · exact Nat.mul_le_mul_right _ (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity edge profile)
        · have enough := Nat.mul_le_mul_right (nodeEdges rows arity limits bound)
            (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity edge profile)
          change edge.children.length * nodeEdges rows arity limits bound ≤ 1 + arity * nodeEdges rows arity limits bound
          omega
      exact ⟨inventory, memos, rows, arity, bound, limits, post.context, retained, receipt.combinedReady,
        (fun value member => post.effects.keeps.available value (available value member)), domain,
        SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children edge profile,
        SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge guards,
        by simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using heightBound,
        childRoom, cap,
        active.advance (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited) before.fourth before.merge,
        smaller⟩
  | children_live => exact initial
  | @walk_node combined index value values before =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
        available, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
        context combined index inherited
      have retained : Stored (descend before combined index).2 := stored.advancePhysical _
      have headRoom : Headroom bits (descend before combined index).2.checked.native.machine.heap
          (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) := by
        change Headroom bits before.checked.native.machine.heap _ _
        exact room.mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
          (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
      exact ⟨inventory, memos, rows, arity, bound, limits, post.context, retained, receipt.inherited,
        post.effects.keeps.available value (available value List.mem_cons_self), domain.member value List.mem_cons_self,
        profile.1, guards.1, Nat.le_trans (Nat.le_max_left _ _) heightBound, headRoom,
        (active.advance (descend before combined index).2.checked before.fourth before.merge).mono
          (smaller value List.mem_cons_self)⟩
  | @walk_tail before combined index value result middle values earlier =>
      obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
        available, domain, profile, guards, heightBound, room, cap, active, smaller⟩ := initial
      obtain ⟨receipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
        context combined index inherited
      have retained : Stored (descend before combined index).2 := stored.advancePhysical _
      have splitRoom : Headroom bits (descend before combined index).2.checked.native.machine.heap
          (nodeNodes rows arity limits bound + values.length * nodeNodes rows arity limits bound)
          (nodeEdges rows arity limits bound + values.length * nodeEdges rows arity limits bound) := by
        change Headroom bits before.checked.native.machine.heap _ _
        exact room.mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
          (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
      have firstAvailable := prefixPost.effects.keeps.available value (available value List.mem_cons_self)
      obtain ⟨next, final, _reads, _checks, post, _output, returned, _narrow, _certificate, work⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.node_call bits formulas solver earlier inventory prefixPost.context
          receipt.inherited firstAvailable (domain.member value List.mem_cons_self) retained
          ((active.advance (descend before combined index).2.checked before.fourth before.merge).mono
            (smaller value List.mem_cons_self)) rows arity bound limits profile.1 guards.1
          (Nat.le_trans (Nat.le_max_left _ _) heightBound)
          (splitRoom.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      have total := prefixPost.trans post
      cases domain with
      | cons _ rest =>
          exact ⟨next, final, rows, arity, bound, limits, post.context, returned,
            inherited.grows total.effects.grows.constraint_growth,
            (fun child member => total.effects.keeps.available child (available child (List.mem_cons_of_mem _ member))),
            rest, profile.2, guards.2, Nat.le_trans (Nat.le_max_right _ _) heightBound, splitRoom.after work, cap,
            (SourceCurrentAllocatedPartialActiveFrames.node_call earlier).activeExcept
              (active.advance (descend before combined index).2.checked before.fourth before.merge),
            (fun child member => smaller child (List.mem_cons_of_mem _ member))⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntrySteps
