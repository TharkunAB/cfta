import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceEqualityProjectionPathComplete

/-!
# Resources for repaired stored substitution and bounded row exposure

The initial causal store bounds full stored substitution and unfolding.
Reader bounds use their explicit proof fuel. They do not derive that fuel
from an initial selected path or supply a complete Operand forecast.
-/
namespace MicroCFTA.SourceCurrentAllocatedProjectionResources
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedNestedConstruction (Outcome)
open InternedValueMassHeap (Stored)
open SourceCurrentAllocatedRecursiveMassTrace (ceiling charge massAfter credit)
open SourceCurrentAllocatedRecursiveMassMonotone
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
variable {Symbol Guard : Type}

private theorem encoded_transform (value : Value Symbol Guard) (bound : Nat)
    (small : InternedValueMass.value value ≤ bound) :
    InternedFreshOrdinaryResultMass.transform (encode (leaves value) [] value) bound ≤ ceiling bound := by
  have encoded := InternedStoredEncodingMass.encode_bound (leaves value) [] value
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  have count : InternedFreshOrdinaryAllocationBudget.nodeBudget (encode (leaves value) [] value) +
      InternedFreshOrdinaryAllocationBudget.edgeBudget (encode (leaves value) [] value) ≤
      SourceCurrentAllocatedRecursiveMassBudget.growthSteps bound := by
    unfold SourceCurrentAllocatedRecursiveMassBudget.growthSteps
    omega
  exact Nat.le_trans (InternedFreshOrdinaryUniformMass.transform_bound bound _ bound
    (InternedStoredEncodingWidth.encode_width _ [] value bound small))
    (Nat.le_trans (InternedFreshOrdinaryUniformMass.evolve_count_mono bound count bound)
      (Nat.le_max_right _ _))

/-- Every stored-substitution outcome fits the initial store schedule, including old winners. -/
theorem execute_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (bound : Nat) (stored : Stored bound before)
    (available : Available before value) (replacements : Replacements before environment) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after →
        InternedValueMass.value result ≤ ceiling bound := by
  have small := InternedValueMassHeap.available before stored value available
  have inputs := inputs_available value environment before available replacements
  have built := InternedFreshOrdinaryResultMass.build_bound (encode (leaves value) [] value)
    ((leaves value).map (input environment)) before bound stored
    (fun child member => InternedValueMassHeap.available before stored child (inputs child member))
  have larger := encoded_transform value bound small
  have counters := InternedStoredEncodingMass.execute_bound value environment before
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  refine ⟨built.1.mono larger, ?_, ?_, fun result after done => Nat.le_trans (built.2 result after done) larger⟩
  all_goals unfold charge SourceCurrentAllocatedRecursiveMassBudget.charge; omega

/-- Full actual unfolding bounds every stopping heap and its exact successful result. -/
theorem unfold_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (stored : Stored bound before) (available : Available before value) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.unfold value before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after →
        InternedValueMass.value result ≤ ceiling bound := by
  cases value with
  | mu entry body depth ordinary =>
      exact execute_bound body _ before bound stored (available.children body (by simp [children]))
        (by intro name replacement found; dsimp only at found; split at found <;> cases found; exact available)
  | empty | reference | node | union =>
      refine ⟨stored.mono (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound),
        Nat.le_add_right _ _, Nat.le_add_right _ _, ?_⟩
      intro result after done
      cases done
      exact Nat.le_trans (InternedValueMassHeap.available before stored _ available)
        (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound)

private theorem pad (fuel bound : Nat) (before after : State Symbol Guard)
    (rows : List (EdgeValue Symbol Guard))
    (actual : Stored (massAfter fuel (ceiling bound)) after ∧
      after.nodes.next ≤ before.nodes.next + credit fuel (ceiling bound) ∧
      after.edges.next ≤ before.edges.next + credit fuel (ceiling bound) ∧
      rows.length ≤ fuel * massAfter fuel (ceiling bound)) :
    Stored (massAfter (fuel + 1) bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit (fuel + 1) bound ∧
      after.edges.next ≤ before.edges.next + credit (fuel + 1) bound ∧
      rows.length ≤ (fuel + 1) * massAfter (fuel + 1) bound := by
  refine ⟨actual.1, ?_, ?_, ?_⟩
  · exact Nat.le_trans actual.2.1 (Nat.add_le_add_left (Nat.le_add_left _ _) _)
  · exact Nat.le_trans actual.2.2.1 (Nat.add_le_add_left (Nat.le_add_left _ _) _)
  · exact Nat.le_trans actual.2.2.2 (Nat.mul_le_mul_right _ (Nat.le_succ fuel))

/-- A completed actual collector derives resources from its explicit read fuel and initial store. -/
theorem collect_bound [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values before pending) (closed : ClosedValues pending)
    (bound : Nat) (stored : Stored bound before) (rows : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : collect fuel before seen pending = .done rows after) :
    Stored (massAfter fuel bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit fuel bound ∧
      after.edges.next ≤ before.edges.next + credit fuel bound ∧
      rows.length ≤ fuel * massAfter fuel bound := by
  induction fuel generalizing before seen pending bound rows after with
  | zero =>
    cases pending with
    | nil => cases done; exact ⟨stored, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _⟩
    | cons => cases done
  | succ fuel ih =>
    cases pending with
    | nil =>
      cases done
      exact ⟨stored.mono (SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge _ _),
        Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.zero_le _⟩
    | cons value rest =>
      have available := inputs value List.mem_cons_self
      have valueClosed := closed value List.mem_cons_self
      have restInputs : Values before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
      have larger := stored.mono (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound)
      cases value with
      | empty =>
        exact pad fuel bound before after rows
          (ih before semantic covered seen rest restInputs restClosed _ larger rows after done)
      | reference name => simp [Value.free] at valueClosed
      | node entry own depth free =>
        cases tail : collect fuel before seen rest with
        | pending | unresolved | exhausted => simp only [collect, tail, Result.prepend] at done; cases done
        | done more final =>
          have equal : own ++ more = rows ∧ final = after := by
            simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
          rcases equal with ⟨rfl, rfl⟩
          have tailBounds := ih before semantic covered seen rest restInputs restClosed _ larger more final tail
          have padded := pad fuel bound before final more tailBounds
          have small := InternedValueMassHeap.available before stored (.node entry own depth free) available
          have length : own.length ≤ bound := Nat.le_trans (InternedStoredEncodingWidth.edges_length own)
            (by simp only [InternedValueMass.value] at small; omega)
          have headBound := Nat.le_trans length (SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge (fuel + 1) bound)
          change own.length ≤ massAfter fuel (ceiling bound) at headBound
          refine ⟨padded.1, padded.2.1, padded.2.2.1, ?_⟩
          rw [List.length_append, Nat.succ_mul]
          change own.length + more.length ≤ fuel * massAfter fuel (ceiling bound) + massAfter fuel (ceiling bound)
          omega
      | union entry members depth free =>
        by_cases visited : entry.identity ∈ seen
        · exact pad fuel bound before after rows
            (ih before semantic covered seen rest restInputs restClosed _ larger rows after
              (by simpa only [collect, ite_eq_left visited] using done))
        · have nextInputs : Values before (members ++ rest) := by
            intro child member
            rcases List.mem_append.mp member with first | later
            · exact available.children child first
            · exact restInputs child later
          have nextClosed : ClosedValues (members ++ rest) := by
            intro child member
            rcases List.mem_append.mp member with first | later
            · exact MergedColdReaderClosed.union_members_closed before semantic.1.normal.facts
                entry members depth free available valueClosed child first
            · exact restClosed child later
          exact pad fuel bound before after rows
            (ih before semantic covered (entry.identity :: seen) (members ++ rest) nextInputs nextClosed
              _ larger rows after (by simpa only [collect, ite_eq_right visited] using done))
      | mu entry body depth ordinary =>
        by_cases visited : entry.identity ∈ seen
        · exact pad fuel bound before after rows
            (ih before semantic covered seen rest restInputs restClosed _ larger rows after
              (by simpa only [collect, ite_eq_left visited] using done))
        · obtain ⟨result, middle, unfolded, context, heap, finalCovered, resultAvailable, growth, history⟩ :=
            InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
              before semantic.1 available semantic.2 covered
          have first := unfold_bound (.mu entry body depth ordinary) before bound stored available
          have middleStored : Stored (ceiling bound) middle := by simpa only [unfolded, Outcome.state] using first.1
          have firstNodes : middle.nodes.next ≤ before.nodes.next + charge bound := by
            simpa only [unfolded, Outcome.state] using first.2.1
          have firstEdges : middle.edges.next ≤ before.edges.next + charge bound := by
            simpa only [unfolded, Outcome.state] using first.2.2.1
          have nextInputs : Values middle (result :: rest) := by
            intro child member
            rcases List.mem_cons.mp member with rfl | later
            · exact resultAvailable
            · exact (restInputs child later).grows before middle growth history
          have nextClosed : ClosedValues (result :: rest) := by
            intro child member
            rcases List.mem_cons.mp member with same | later
            · subst child
              exact InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                before semantic.1 available valueClosed result middle unfolded
            · exact restClosed child later
          have tail := ih middle ⟨context, heap⟩ finalCovered (entry.identity :: seen) (result :: rest)
            nextInputs nextClosed _ middleStored rows after
            (by simpa only [collect, ite_eq_right visited, unfolded] using done)
          refine ⟨tail.1, ?_, ?_, ?_⟩
          · have combined := Nat.le_trans tail.2.1 (Nat.add_le_add_right firstNodes _)
            simpa only [credit, Nat.add_assoc] using combined
          · have combined := Nat.le_trans tail.2.2.1 (Nat.add_le_add_right firstEdges _)
            simpa only [credit, Nat.add_assoc] using combined
          · exact Nat.le_trans tail.2.2.2 (Nat.mul_le_mul_right _ (Nat.le_succ fuel))

private theorem widen (first last bound : Nat) (counts : first ≤ last)
    (before after : State Symbol Guard) (rows : List (EdgeValue Symbol Guard))
    (actual : Stored (massAfter first bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit first bound ∧
      after.edges.next ≤ before.edges.next + credit first bound ∧
      rows.length ≤ first * massAfter first bound) :
    Stored (massAfter last bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit last bound ∧
      after.edges.next ≤ before.edges.next + credit last bound ∧
      rows.length ≤ last * massAfter last bound :=
  ⟨actual.1.mono (massAfter_count_mono counts bound),
    Nat.le_trans actual.2.1 (Nat.add_le_add_left (credit_count_mono counts bound) _),
    Nat.le_trans actual.2.2.1 (Nat.add_le_add_left (credit_count_mono counts bound) _),
    Nat.le_trans actual.2.2.2 (Nat.mul_le_mul counts (massAfter_count_mono counts bound))⟩

private theorem canonical_bound [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before value) (closed : value.free = [])
    (bound : Nat) (stored : Stored bound before) (rows : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : (collect fuel before [] [value]).canonical = .done rows after) :
    Stored (massAfter fuel bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit fuel bound ∧
      after.edges.next ≤ before.edges.next + credit fuel bound ∧
      rows.length ≤ fuel * massAfter fuel bound := by
  cases collected : collect fuel before [] [value] with
  | pending | unresolved | exhausted => simp only [collected, Result.canonical] at done; cases done
  | done original final =>
    have equal : canonicalEdges original = rows ∧ final = after := by
      simpa only [collected, Result.canonical, Result.done.injEq] using done
    rcases equal with ⟨rfl, rfl⟩
    have actual := collect_bound fuel before semantic covered [] [value]
      (by intro item member; simpa only [List.mem_singleton.mp member] using available)
      (by intro item member; simpa only [List.mem_singleton.mp member] using closed)
      bound stored original final collected
    have length : (canonicalEdges original).length ≤ original.length :=
      List.Nodup.length_le_of_subset (MergedNodeRowBounds.canonical_nodup original) (canonicalEdges_member original)
    exact ⟨actual.1, actual.2.1, actual.2.2.1, Nat.le_trans length actual.2.2.2⟩

/-- The exact repaired row read derives resources and ordered row width at its own return. -/
theorem read_bound [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before value) (closed : value.free = [])
    (bound : Nat) (stored : Stored bound before) (rows : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : nodeEdges fuel value before = .done rows after) :
    Stored (massAfter (fuel + 1) bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit (fuel + 1) bound ∧
      after.edges.next ≤ before.edges.next + credit (fuel + 1) bound ∧
      rows.length ≤ (fuel + 1) * massAfter (fuel + 1) bound ∧ Edges after rows := by
  have resources : Stored (massAfter (fuel + 1) bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit (fuel + 1) bound ∧
      after.edges.next ≤ before.edges.next + credit (fuel + 1) bound ∧
      rows.length ≤ (fuel + 1) * massAfter (fuel + 1) bound := by
    cases value with
    | empty | reference =>
      cases done
      exact ⟨stored.mono (SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge _ _),
        Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.zero_le _⟩
    | node entry own depth free =>
      cases done
      have small := InternedValueMassHeap.available before stored (.node entry rows depth free) available
      have length : rows.length ≤ bound := Nat.le_trans (InternedStoredEncodingWidth.edges_length rows)
        (by simp only [InternedValueMass.value] at small; omega)
      have one : 1 ≤ fuel + 1 := by omega
      have multiplication := Nat.mul_le_mul_right (massAfter (fuel + 1) bound) one
      simp only [Nat.one_mul] at multiplication
      exact ⟨stored.mono (SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge _ _),
        Nat.le_add_right _ _, Nat.le_add_right _ _,
        Nat.le_trans length (Nat.le_trans (SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge _ _) multiplication)⟩
    | union entry members depth free =>
      exact widen fuel (fuel + 1) bound (Nat.le_succ _) before after rows
        (canonical_bound fuel (.union entry members depth free) before semantic covered available closed bound stored rows after done)
    | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, context, heap, middleCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          before semantic.1 available semantic.2 covered
      have first := unfold_bound (.mu entry body depth ordinary) before bound stored available
      have middleStored : Stored (ceiling bound) middle := by simpa only [unfolded, Outcome.state] using first.1
      have firstNodes : middle.nodes.next ≤ before.nodes.next + charge bound := by
        simpa only [unfolded, Outcome.state] using first.2.1
      have firstEdges : middle.edges.next ≤ before.edges.next + charge bound := by
        simpa only [unfolded, Outcome.state] using first.2.2.1
      have fallback (completed : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done rows after) :
          Stored (massAfter (fuel + 1) bound) after ∧
          after.nodes.next ≤ before.nodes.next + credit (fuel + 1) bound ∧
          after.edges.next ≤ before.edges.next + credit (fuel + 1) bound ∧
          rows.length ≤ (fuel + 1) * massAfter (fuel + 1) bound := by
        have tail := canonical_bound fuel (.mu entry body depth ordinary) middle ⟨context, heap⟩ middleCovered
          (available.grows before middle growth history) closed _ middleStored rows after completed
        refine ⟨tail.1, ?_, ?_, ?_⟩
        · have combined := Nat.le_trans tail.2.1 (Nat.add_le_add_right firstNodes _)
          simpa only [credit, Nat.add_assoc] using combined
        · have combined := Nat.le_trans tail.2.2.1 (Nat.add_le_add_right firstEdges _)
          simpa only [credit, Nat.add_assoc] using combined
        · exact Nat.le_trans tail.2.2.2 (Nat.mul_le_mul_right _ (Nat.le_succ fuel))
      cases result with
      | node entry own depth free =>
        have equal : own = rows ∧ middle = after := by
          simpa only [nodeEdges, unfolded, Result.done.injEq] using done
        rcases equal with ⟨rfl, rfl⟩
        have small := first.2.2.2 _ _ unfolded
        have length : own.length ≤ ceiling bound := Nat.le_trans (InternedStoredEncodingWidth.edges_length own)
          (by simp only [InternedValueMass.value] at small; omega)
        have grew := SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge fuel (ceiling bound)
        have multiply := Nat.mul_le_mul_right (massAfter fuel (ceiling bound)) (show 1 ≤ fuel + 1 by omega)
        simp only [Nat.one_mul] at multiply
        exact ⟨middleStored.mono grew,
          Nat.le_trans firstNodes (Nat.add_le_add_left (Nat.le_add_right _ _) _),
          Nat.le_trans firstEdges (Nat.add_le_add_left (Nat.le_add_right _ _) _),
          Nat.le_trans length (Nat.le_trans grew multiply)⟩
      | empty | reference | union | mu => exact fallback (by simpa only [nodeEdges, unfolded] using done)
  have resident := (MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before semantic covered available closed).edges rows after done
  exact ⟨resources.1, resources.2.1, resources.2.2.1, resources.2.2.2, resident⟩

end MicroCFTA.SourceCurrentAllocatedProjectionResources
