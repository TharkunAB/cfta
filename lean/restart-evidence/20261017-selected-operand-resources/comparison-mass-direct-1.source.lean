import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceMergedComparisonEffects

/-!
# Numeric resources for actual repaired comparisons

The supplied comparison fuel and initial causal payload bound determine a
numeric envelope. Actual reads and recursive calls derive every local bound.
The theorem covers successful closed recursive comparisons. It does not
derive an initial sufficient comparison fuel.
-/
namespace MicroCFTA.SourceMergedComparisonMass
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect bind_done read_graph)
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
variable {Symbol Guard : Type}

/-- One envelope bounds payloads and both increments from the original heap. -/
structure Resources (bound : Nat) (before after : State Symbol Guard) : Prop where
  /-- Every complete returned payload fits the envelope. -/
  stored : Stored bound after
  /-- The literal node supply fits the original supply plus the envelope. -/
  nodes : after.nodes.next ≤ before.nodes.next + bound
  /-- The literal edge supply fits the same increment envelope. -/
  edges : after.edges.next ≤ before.edges.next + bound

/-- A causal initial store supplies the initial numeric envelope. -/
theorem Resources.refl (before : State Symbol Guard) (bound : Nat) (stored : Stored bound before) :
    Resources bound before before := ⟨stored, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- A larger envelope retains the exact physical endpoints. -/
theorem Resources.mono {before after : State Symbol Guard} {first last : Nat}
    (known : Resources first before after) (enough : first ≤ last) : Resources last before after :=
  ⟨known.stored.mono enough, Nat.le_trans known.nodes (Nat.add_le_add_left enough _),
    Nat.le_trans known.edges (Nat.add_le_add_left enough _)⟩

/-- Numeric growth retains inequalities between initial bounds. -/
def Monotone (growth : Nat → Nat) : Prop := ∀ {first last : Nat}, first ≤ last → growth first ≤ growth last

/-- An ordered finite scan starts each action at its actual earlier bound. -/
def iterate (growth : Nat → Nat) : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => iterate growth count (growth bound)

/-- Monotone actions retain ordered bounds through a fixed scan. -/
theorem iterate_mono {growth : Nat → Nat} (mono : Monotone growth) (count : Nat)
    {first last : Nat} (enough : first ≤ last) : iterate growth count first ≤ iterate growth count last := by
  induction count generalizing first last with
  | zero => exact enough
  | succ count ih => exact ih (mono enough)

/-- Inflationary actions retain the initial envelope. -/
theorem iterate_ge {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (count bound : Nat) :
    bound ≤ iterate growth count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (ge bound) (ih _)

/-- Additional actions retain each earlier envelope. -/
theorem iterate_count_mono {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    iterate growth first bound ≤ iterate growth last bound := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (iterate_mono mono last (ge bound))

/-- Pointwise larger monotone actions support the same number of calls. -/
theorem iterate_family_mono {first last : Nat → Nat} (mono : Monotone last)
    (enough : ∀ bound, first bound ≤ last bound) (count bound : Nat) :
    iterate first count bound ≤ iterate last count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (ih _) (iterate_mono mono count (enough bound))

/-- One repaired read includes its old prefix credit and actual constructor charges. -/
def readBound (fuel bound : Nat) : Nat := massAfter (fuel + 1) bound + bound + credit (fuel + 1) bound

/-- The actual reader can return at most this many rows. -/
def readWidth (fuel bound : Nat) : Nat := (fuel + 1) * massAfter (fuel + 1) bound

private theorem read_ge (fuel bound : Nat) : bound ≤ readBound fuel bound := by
  unfold readBound
  omega

private theorem read_mono (fuel : Nat) : Monotone (readBound fuel) := by
  intro first last enough
  exact Nat.add_le_add (Nat.add_le_add
    (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_bound_mono _ enough) enough)
    (SourceCurrentAllocatedRecursiveMassMonotone.credit_bound_mono _ enough)

private theorem width_mono (fuel : Nat) : Monotone (readWidth fuel) := by
  intro first last enough
  exact Nat.mul_le_mul_left _ (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_bound_mono _ enough)

private def childrenBound (growth : Nat → Nat) (bound : Nat) : Nat := iterate growth bound bound

private theorem children_ge {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (bound : Nat) :
    bound ≤ childrenBound growth bound := iterate_ge ge bound bound

private theorem children_mono {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) : Monotone (childrenBound growth) := by
  intro first last enough
  exact Nat.le_trans (iterate_count_mono mono ge enough first) (iterate_mono mono last enough)

private def rowBound (fuel : Nat) (growth : Nat → Nat) (bound : Nat) : Nat :=
  iterate (childrenBound growth) (readWidth fuel bound) (readBound fuel bound)

private theorem row_ge (fuel : Nat) {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (bound : Nat) :
    bound ≤ rowBound fuel growth bound := Nat.le_trans (read_ge fuel bound) (iterate_ge (children_ge ge) _ _)

private theorem row_mono (fuel : Nat) {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) : Monotone (rowBound fuel growth) := by
  intro first last enough
  exact Nat.le_trans (iterate_count_mono (children_mono mono ge) (children_ge ge) (width_mono fuel enough) _)
    (iterate_mono (children_mono mono ge) _ (read_mono fuel enough))

/-- Each recursive comparison level pays for its actual narrow and wide reads. -/
def comparisonBound : Nat → Nat → Nat
  | 0, bound => bound
  | fuel + 1, bound => iterate (rowBound (fuel + 1) (comparisonBound fuel))
      (readWidth (fuel + 1) bound) (readBound (fuel + 1) bound)

/-- The comparison envelope retains the initial store bound. -/
theorem comparisonBound_ge (fuel bound : Nat) : bound ≤ comparisonBound fuel bound := by
  induction fuel generalizing bound with
  | zero => exact Nat.le_refl _
  | succ fuel ih => exact Nat.le_trans (read_ge _ _) (iterate_ge (row_ge _ ih) _ _)

/-- A larger initial store supports the same comparison fuel. -/
theorem comparisonBound_mono (fuel : Nat) : Monotone (comparisonBound fuel) := by
  induction fuel with
  | zero => exact fun enough => enough
  | succ fuel ih =>
      intro first last enough
      exact Nat.le_trans (iterate_count_mono (row_mono _ ih (comparisonBound_ge fuel))
        (row_ge _ (comparisonBound_ge fuel)) (width_mono _ enough) _)
        (iterate_mono (row_mono _ ih (comparisonBound_ge fuel)) _ (read_mono _ enough))

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem read_resources (fuel : Nat) (value : Value Symbol Guard) (origin before : State Symbol Guard)
    (bound : Nat) (known : Resources bound origin before) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Resources (readBound fuel bound) origin after ∧ rows.length ≤ readWidth fuel bound := by
  have actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows after := by
    cases found : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
    | done edges final =>
        simp only [MergedFreshOrdinaryExposure.read, found] at done
        cases done
        exact found
    | unresolved | pending | exhausted => simp only [MergedFreshOrdinaryExposure.read, found] at done; cases done
  obtain ⟨stored, nodes, edges, length, _resident⟩ := SourceCurrentAllocatedProjectionResources.read_bound
    fuel value before semantic.ready.semantic semantic.ready.covered available closed bound known.stored rows after actual
  refine ⟨⟨stored.mono (by unfold readBound; omega), ?_, ?_⟩, length⟩
  · have initial := known.nodes
    unfold readBound
    omega
  · have initial := known.edges
    unfold readBound
    omega

private def Callback (growth : Nat → Nat)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ origin before bound wide narrow, Resources bound origin before → SemanticReady before →
    Available before wide → Available before narrow → wide.free = [] → narrow.free = [] →
    ∀ answer after, compare wide narrow before = .done answer after → Resources (growth bound) origin after

private theorem children_resources (growth : Nat → Nat) (ge : ∀ bound, bound ≤ growth bound)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (effects : SourceMergedComparisonEffects.Callback compare) (callback : Callback growth compare)
    (wides narrows : List (Value Symbol Guard)) (origin before : State Symbol Guard) (bound : Nat)
    (known : Resources bound origin before) (semantic : SemanticReady before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) :
    Resources (iterate growth wides.length bound) origin after := by
  induction wides generalizing narrows before bound with
  | nil => cases done; exact known
  | cons wide wides ih =>
      cases narrows with
      | nil => cases done; exact known.mono (iterate_ge ge _ _)
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have result := callback origin before bound wide narrow known semantic
            (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle first
          have effect := effects wide narrow before semantic (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => cases later; exact result.mono (iterate_ge ge _ _)
          | true => exact ih narrows middle (growth bound) result effect.2
              (fun value member => effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
              (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) later

private theorem anyCover_resources [DecidableEq Symbol] (growth : Nat → Nat) (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (effects : SourceMergedComparisonEffects.Callback compare) (callback : Callback growth compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (origin before : State Symbol Guard) (bound : Nat)
    (known : Resources bound origin before) (semantic : SemanticReady before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) :
    Resources (iterate (childrenBound growth) wides.length bound) origin after := by
  induction wides generalizing before bound with
  | nil => cases done; exact known
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)
        have result := children_resources growth ge compare effects callback wide.children narrow.children origin before bound
          known semantic childInputs narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
        have mass := InternedValueMassHeap.resident before known.stored wide (wideInputs _ List.mem_cons_self)
        rw [InternedValueMass.edge_children, InternedValueMass.values_eq_length_sum] at mass
        have bounded : Resources (childrenBound growth bound) origin middle :=
          result.mono (iterate_count_mono mono ge (by omega) bound)
        have effect := SourceMergedComparisonEffects.children_effect compare effects wide.children narrow.children before semantic
          childInputs narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
        cases accepted with
        | true => cases later; exact bounded.mono (iterate_ge (children_ge ge) _ _)
        | false => exact ih middle _ bounded effect.2
            (fun value member => effect.1.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.1.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later
      · exact (ih before bound known semantic narrowInputs
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done).mono
          (iterate_mono (children_mono mono ge) _ (children_ge ge bound))

private theorem allRows_resources [DecidableEq Symbol] (growth : Nat → Nat) (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (effects : SourceMergedComparisonEffects.Callback compare) (callback : Callback growth compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (origin before : State Symbol Guard) (bound : Nat)
    (known : Resources bound origin before) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) :
    Resources (iterate (rowBound fuel growth) narrows.length bound) origin after := by
  induction narrows generalizing before bound with
  | nil => cases done; exact known
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readResult := read_resources fuel wide origin before bound known semantic wideInput wideClosed wides readAfter read
      have readFacts := (read_graph fuel wide before wides readAfter read).verified semantic wideInput wideClosed
      have narrowChildren := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have result := anyCover_resources growth mono ge clear compare effects callback narrow wides origin readAfter _
        readResult.1 readFacts.2.1 (fun value member => readFacts.1.available value (narrowChildren value member))
        readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have bounded : Resources (rowBound fuel growth bound) origin middle :=
        result.mono (iterate_count_mono (children_mono mono ge) (children_ge ge) readResult.2 _)
      have coverFacts := SourceMergedComparisonEffects.anyCover_effect clear compare effects narrow wides readAfter readFacts.2.1
        (fun value member => readFacts.1.available value (narrowChildren value member)) readFacts.2.2.1
        (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have first : Effect before middle := ⟨readFacts.1.trans coverFacts.1, coverFacts.2⟩
      cases accepted with
      | false => cases rest; exact bounded.mono (iterate_ge (row_ge fuel ge) _ _)
      | true => exact ih middle _ bounded first.2 (first.1.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.1.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
          (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest

/-- A successful actual comparison derives its envelope without later resource premises. -/
theorem check_resources [DecidableEq Symbol] (clear : Guard → Bool) (fuel : Nat)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (origin before : State Symbol Guard)
    (bound : Nat) (known : Resources bound origin before) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) :
    Resources (comparisonBound fuel bound) origin after := by
  rw [check] at done
  split at done
  · cases done; exact known.mono (comparisonBound_ge _ _)
  · split at done
    · cases done; exact known.mono (comparisonBound_ge _ _)
    · split at done
      · cases done; exact known.mono (comparisonBound_ge _ _)
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
          cases narrowFound : identity narrow with
          | none => simp only [wideFound, narrowFound] at done; cases done
          | some narrowId =>
            simp only [wideFound, narrowFound] at done
            split at done
            · cases done; exact known.mono (comparisonBound_ge _ _)
            · cases fuel with
              | zero => cases done
              | succ fuel =>
                obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                have readResult := read_resources (fuel + 1) narrow origin before bound known semantic narrowInput narrowClosed narrows middle read
                have readFacts := (read_graph (fuel + 1) narrow before narrows middle read).verified semantic narrowInput narrowClosed
                have rest := allRows_resources (comparisonBound fuel) (comparisonBound_mono fuel) (comparisonBound_ge fuel)
                  (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                  (SourceMergedComparisonEffects.check_effect clear fuel ((wideId, narrowId) :: above))
                  (fun root state mass left right => check_resources clear fuel ((wideId, narrowId) :: above) left right root state mass)
                  wide narrows origin middle _ readResult.1 readFacts.2.1
                  (readFacts.1.available wide wideInput) readFacts.2.2.1 wideClosed readFacts.2.2.2 answer after later
                exact rest.mono (iterate_count_mono (row_mono _ (comparisonBound_mono fuel) (comparisonBound_ge fuel))
                  (row_ge _ (comparisonBound_ge fuel)) readResult.2 _)
termination_by fuel

/-- The literal comparison result has a bound from only its initial store and supplied fuel. -/
theorem check_bound [DecidableEq Symbol] (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat))
    (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (semantic : SemanticReady before) (stored : Stored bound before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) :
    Resources (comparisonBound fuel bound) before after :=
  check_resources clear fuel above wide narrow before before bound (Resources.refl before bound stored)
    semantic wideInput narrowInput wideClosed narrowClosed answer after done

end MicroCFTA.SourceMergedComparisonMass
