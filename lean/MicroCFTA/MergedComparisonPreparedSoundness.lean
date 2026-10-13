import MicroCFTA.MergedComparisonSoundnessReplay
import MicroCFTA.MergedSourceExposureCoverage

/-!
# Finite-term soundness of prepared ordered comparison

Successful comparison transfers each finite accepted term. Numeric ancestor
pairs refer to coherent complete records. Induction on the term height
justifies ancestor reuse after one constructor step.
-/
namespace MicroCFTA.MergedComparisonPreparedSoundness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts
open MergedColdReaderClosedInputs MergedComparisonWarmProgress Language

/-- A verified stage cannot change a cache whose available recursive records are already warm. -/
theorem ready_unchanged [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs)
    (result : Result Symbol Guard Output) (verified : Verified state result) : result.state = state := by
  rcases verified.progress with same | ⟨entry, body, depth, ordinary, available, cold, _⟩
  · exact same
  · obtain ⟨value, _, done⟩ := ready entry body depth ordinary available
    exact False.elim (cold ⟨value, done⟩)

/-- Numeric identity determines a closed available record in a coherent cache. -/
theorem identity_injective (state : State Symbol Guard) (facts : Facts state)
    (left right : Value Symbol Guard) (leftInput : Available state left) (rightInput : Available state right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (number : Nat)
    (leftId : identity left = some number) (rightId : identity right = some number) : left = right := by
  have stored (value : Value Symbol Guard) (closed : value.free = []) (id : identity value = some number) :
      ∃ entry, entryOf value = some entry ∧ entry.identity = number := by
    cases value with
    | empty => cases id
    | reference name => simp [Value.free] at closed
    | node entry | union entry | mu entry => exact ⟨entry, rfl, Option.some.inj id⟩
  obtain ⟨first, firstField, firstId⟩ := stored left leftClosed leftId
  obtain ⟨second, secondField, secondId⟩ := stored right rightClosed rightId
  exact MergedSourceExposureCoverage.identity_unique state facts left right leftInput rightInput first second
    firstField secondField (firstId.trans secondId.symm)

/-- Completed child conjunction supplies a pointwise certificate when the arities agree. -/
theorem children_certificate [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      ∀ after, compare wide narrow state = .done true after → relation wide narrow)
    (wides narrows : List (Value Symbol Guard)) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows) (lengths : wides.length = narrows.length)
    (after : State Symbol Guard) (done : MergedSourceComparison.children compare wides narrows state = .done true after) :
    All₂ relation wides narrows := by
  induction wides generalizing narrows with
  | nil => cases narrows with
    | nil => exact .nil
    | cons => simp at lengths
  | cons wide wides ih =>
      cases narrows with
      | nil => simp at lengths
      | cons narrow narrows =>
          have wideInput := wideInputs wide List.mem_cons_self
          have narrowInput := narrowInputs narrow List.mem_cons_self
          have wideFree := wideClosed wide List.mem_cons_self
          have narrowFree := narrowClosed narrow List.mem_cons_self
          have unchanged := ready_unchanged state outputs ready _
            (callback wide narrow state facts prepared wideInput narrowInput wideFree narrowFree)
          cases first : compare wide narrow state with
          | failed fault middle => simp only [MergedSourceComparison.children, first, Result.bind, reduceCtorEq] at done
          | done answer middle =>
              have equal : middle = state := by simpa only [first, Result.state] using unchanged
              subst middle
              cases answer with
              | false => simp [MergedSourceComparison.children, first, Result.bind] at done
              | true =>
                  refine .cons (certify wide narrow wideInput narrowInput wideFree narrowFree state first) ?_
                  exact ih narrows (fun value member => wideInputs value (List.mem_cons_of_mem _ member))
                    (fun value member => narrowInputs value (List.mem_cons_of_mem _ member))
                    (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                    (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))
                    (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using lengths)
                    (by simpa only [MergedSourceComparison.children, first, Result.bind, ↓reduceIte] using done)

/-- Successful cover search selects a source row with a complete child certificate. -/
theorem anyCover_certificate [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      ∀ after, compare wide narrow state = .done true after → relation wide narrow)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (after : State Symbol Guard) (done : anyCover clear compare narrow wides state = .done true after) :
    ∃ wide ∈ wides, wide.entry.key.symbol = narrow.entry.key.symbol ∧ clear wide.entry.key.constraint = true ∧
      All₂ relation wide.children narrow.children := by
  induction wides with
  | nil => simp [anyCover] at done
  | cons wide rest ih =>
      rw [anyCover] at done
      split at done
      · rename_i header
        have wideChildren := facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self)
        have narrowChildren := facts.cached.edges narrow.entry.key narrow narrowInput
        have childrenClosed := wideClosed wide List.mem_cons_self
        have unchanged := ready_unchanged state outputs ready _ (children_verified compare callback wide.children narrow.children
          state facts prepared wideChildren narrowChildren childrenClosed narrowClosed)
        cases first : MergedSourceComparison.children compare wide.children narrow.children state with
        | failed fault middle => simp only [first, Result.bind, reduceCtorEq] at done
        | done answer middle =>
            have equal : middle = state := by simpa only [first, Result.state] using unchanged
            subst middle
            cases answer with
            | true => exact ⟨wide, List.mem_cons_self, header.1, header.2.2,
                children_certificate compare callback state facts prepared outputs ready relation certify
                  wide.children narrow.children wideChildren narrowChildren childrenClosed narrowClosed header.2.1 state first⟩
            | false =>
                obtain ⟨cover, member, matched⟩ := ih (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
                  (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
                  (by simpa only [first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done)
                exact ⟨cover, List.mem_cons_of_mem _ member, matched⟩
      · obtain ⟨cover, member, matched⟩ := ih (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done
        exact ⟨cover, List.mem_cons_of_mem _ member, matched⟩

/-- Successful row conjunction supplies a certified cover from an actual demanded wide read. -/
theorem allRows_certificate [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      ∀ after, compare wide narrow state = .done true after → relation wide narrow)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows state = .done true after) :
    ∀ narrow ∈ narrows, ∃ wides cover, read fuel wide state = .done wides state ∧ cover ∈ wides ∧
      cover.entry.key.symbol = narrow.entry.key.symbol ∧ clear cover.entry.key.constraint = true ∧
      All₂ relation cover.children narrow.children := by
  induction narrows with
  | nil => simp
  | cons narrow rest ih =>
      have reader := read_verified fuel wide state facts prepared wideInput
      have unchanged := ready_unchanged state outputs ready _ reader
      cases first : read fuel wide state with
      | failed fault middle => simp only [allRows, first, Result.bind, reduceCtorEq] at done
      | done wides middle =>
          have equal : middle = state := by simpa only [first, Result.state] using unchanged
          subst middle
          have wideRows := read_edges fuel wide state facts prepared wideInput wides state first
          have wideRowsClosed := read_closed fuel wide state facts prepared wideInput wideClosed wides state first
          have narrowRow := narrowInputs narrow List.mem_cons_self
          have narrowRowClosed := narrowClosed narrow List.mem_cons_self
          have covered := anyCover_verified clear compare callback narrow wides state facts prepared
            narrowRow wideRows narrowRowClosed wideRowsClosed
          have coverUnchanged := ready_unchanged state outputs ready _ covered
          cases second : anyCover clear compare narrow wides state with
          | failed fault next => simp only [allRows, first, Result.bind, second, reduceCtorEq] at done
          | done answer next =>
              have equal : next = state := by simpa only [second, Result.state] using coverUnchanged
              subst next
              cases answer with
              | false => simp [allRows, first, Result.bind, second] at done
              | true =>
                  intro edge member
                  rcases List.mem_cons.mp member with rfl | member
                  · obtain ⟨cover, coverIn, matched⟩ := anyCover_certificate clear compare callback state facts prepared outputs ready
                      relation certify edge wides narrowRow wideRows narrowRowClosed wideRowsClosed state second
                    exact ⟨wides, cover, rfl, coverIn, matched⟩
                  · simpa only [first] using ih (fun row member => narrowInputs row (List.mem_cons_of_mem _ member))
                      (fun row member => narrowClosed row (List.mem_cons_of_mem _ member))
                      (by simpa only [allRows, first, Result.bind, second, ↓reduceIte] using done) edge member

/-- A comparison transfers all accepted finite terms through a fixed height. -/
def Bounded [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (rank : Nat) (wide narrow : Value Symbol Guard) : Prop :=
  ∀ term, term.height ≤ rank → EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) narrow term →
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) wide term

/-- Numeric ancestor pairs certify their coherent closed records through a fixed term height. -/
def Ancestors [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (rank : Nat) (above : List (Nat × Nat)) : Prop :=
  ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
    ∀ wideId narrowId, identity wide = some wideId → identity narrow = some narrowId →
    (wideId, narrowId) ∈ above → Bounded state meaning rank wide narrow

/-- Each successful prepared comparison transfers finite terms at every height justified by its ancestors. -/
theorem check_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (rank fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel above wide narrow state = .done true after)
    (ancestors : Ancestors state meaning rank above) : Bounded state meaning rank wide narrow := by
  induction rank generalizing fuel above wide narrow after with
  | zero =>
      intro term bound accepted
      have positive := term.height_pos
      omega
  | succ rank ih =>
      have originalDone := done
      intro term bound accepted
      rw [check] at done
      by_cases narrowEmpty : narrow.referenceOf = .empty
      · have same : narrow = .empty := by cases narrow <;> simp_all [Value.referenceOf]
        exact False.elim (MergedPhysicalUnion.empty_rejects state meaning term (same ▸ accepted))
      simp only [narrowEmpty, ↓reduceIte] at done
      by_cases wideEmpty : wide.referenceOf = .empty
      · simp [wideEmpty] at done
      simp only [wideEmpty, ↓reduceIte] at done
      by_cases same : wide.referenceOf = narrow.referenceOf
      · have equal := (MergedPhysicalComparison.same_record state facts wide narrow wideInput narrowInput).mp same
        simpa only [equal] using accepted
      simp only [same, ↓reduceIte] at done
      cases wideFound : identity wide with
      | none => simp only [wideFound] at done; cases done
      | some wideId =>
          cases narrowFound : identity narrow with
          | none => simp only [wideFound, narrowFound] at done; cases done
          | some narrowId =>
              simp only [wideFound, narrowFound] at done
              by_cases visited : (wideId, narrowId) ∈ above
              · exact ancestors wide narrow wideInput narrowInput wideClosed narrowClosed
                  wideId narrowId wideFound narrowFound visited term bound accepted
              simp only [visited, ↓reduceIte] at done
              have oldAncestors : Ancestors state meaning rank above := by
                intro left right leftInput rightInput leftClosed rightClosed leftId rightId leftFound rightFound member child childBound childAccepted
                exact ancestors left right leftInput rightInput leftClosed rightClosed leftId rightId leftFound rightFound member
                  child (Nat.le_trans childBound (Nat.le_succ rank)) childAccepted
              have current := ih fuel above wide narrow wideInput narrowInput wideClosed narrowClosed after originalDone oldAncestors
              have nextAncestors : Ancestors state meaning rank ((wideId, narrowId) :: above) := by
                intro left right leftInput rightInput leftClosed rightClosed leftId rightId leftFound rightFound member
                rcases List.mem_cons.mp member with equal | member
                · have ids := Prod.mk.inj equal
                  have leftEqual := identity_injective state facts left wide leftInput wideInput leftClosed wideClosed wideId
                    (by simpa only [ids.1] using leftFound) wideFound
                  have rightEqual := identity_injective state facts right narrow rightInput narrowInput rightClosed narrowClosed narrowId
                    (by simpa only [ids.2] using rightFound) narrowFound
                  simpa only [leftEqual, rightEqual] using current
                · exact oldAncestors left right leftInput rightInput leftClosed rightClosed leftId rightId leftFound rightFound member
              cases fuel with
              | zero => cases done
              | succ fuel =>
                  have callback : Callback (check (Symbol := Symbol) clear fuel ((wideId, narrowId) :: above)) :=
                    check_verified clear fuel ((wideId, narrowId) :: above)
                  have certify : ∀ left right, Available state left → Available state right → left.free = [] → right.free = [] →
                      ∀ final, check clear fuel ((wideId, narrowId) :: above) left right state = .done true final →
                        Bounded state meaning rank left right := by
                    intro left right leftInput rightInput leftClosed rightClosed final finished
                    exact ih fuel ((wideId, narrowId) :: above) left right leftInput rightInput leftClosed rightClosed final finished nextAncestors
                  have reader := read_verified (fuel + 1) narrow state facts prepared narrowInput
                  have unchanged := ready_unchanged state outputs ready _ reader
                  cases first : read (fuel + 1) narrow state with
                  | failed fault middle => simp only [first, Result.bind, reduceCtorEq] at done
                  | done narrows middle =>
                      have equal : middle = state := by simpa only [first, Result.state] using unchanged
                      subst middle
                      have readDone := read_done (fuel + 1) narrow state narrows state first
                      have exactRead := (MergedSourceExposureCoverage.actual_exact (fuel + 1) narrow state facts prepared
                        narrowInput narrows state readDone).2 meaning term
                      obtain ⟨edge, member, terms, shape, children, _⟩ := exactRead.mp accepted
                      have covers := allRows_certificate (fuel + 1) clear _ callback state facts prepared outputs ready
                        (Bounded state meaning rank) certify wide narrows wideInput
                        (read_edges (fuel + 1) narrow state facts prepared narrowInput narrows state first)
                        wideClosed (read_closed (fuel + 1) narrow state facts prepared narrowInput narrowClosed narrows state first)
                        after (by simpa only [first, Result.bind] using done)
                      obtain ⟨wides, cover, wideRead, coverIn, symbol, guard, related⟩ := covers edge member
                      have childBound : forestHeight terms ≤ rank := by
                        rw [shape] at bound
                        simpa only [Term.height, forestHeight, Nat.add_le_add_iff_right] using bound
                      have boundedChildren := (all₂_height_iff (EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning))
                        edge.children terms rank).mpr ⟨children, childBound⟩
                      have coveredChildren := MergedAlternativesSubsumption.all₂_transfer
                        (fun left right child comparison run => comparison child run.2 run.1) related boundedChildren
                      exact MergedSourceExposureLanguage.nodeEdges_sound (fuel + 1) wide state facts prepared wideInput
                        wides state (read_done (fuel + 1) wide state wides state wideRead) state (grows_refl state) meaning
                        cover coverIn term ⟨terms, shape.trans (by rw [symbol]), coveredChildren, clearTrue _ guard term⟩

/-- Successful prepared comparison contains every finite term of its narrow operand. -/
theorem check_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (outputs : List (Value Symbol Guard)) (ready : Ready state outputs)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel [] wide narrow state = .done true after)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) narrow term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) wide term :=
  check_bounded state facts prepared outputs ready clear meaning clearTrue term.height fuel [] wide narrow
    wideInput narrowInput wideClosed narrowClosed after done (by intro left right a b c d x y e f impossible; cases impossible)
    term (Nat.le_refl _) accepted

end MicroCFTA.MergedComparisonPreparedSoundness
