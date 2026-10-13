import MicroCFTA.MergedComparisonPreparedSoundness
import MicroCFTA.MergedComparisonEffectOrder

/-!
# Soundness in the actual returned comparison cache

A completed cache-preserving trace cannot contain a changing prefix.
This fact replaces global warmup in the finite-term soundness proof.
-/
namespace MicroCFTA.MergedComparisonSoundness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts
open MergedColdReaderClosedInputs MergedComparisonWarmProgress Language
open MergedComparisonPreparedSoundness (Bounded Ancestors identity_injective)

/-- Completed child conjunction supplies a pointwise certificate when the arities agree. -/
theorem children_certificate [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      compare wide narrow state = .done true state → relation wide narrow)
    (wides narrows : List (Value Symbol Guard)) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows) (lengths : wides.length = narrows.length)
    (done : MergedSourceComparison.children compare wides narrows state = .done true state) :
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
          have verified := callback wide narrow state facts prepared wideInput narrowInput wideFree narrowFree
          cases first : compare wide narrow state with
          | failed fault middle => simp only [MergedSourceComparison.children, first, Result.bind, reduceCtorEq] at done
          | done answer middle =>
              cases answer with
              | false => simp [MergedSourceComparison.children, first, Result.bind] at done
              | true =>
                  have middleFacts : Facts middle := by simpa only [first, Result.state] using verified.facts
                  have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve verified.unchanged
                  have tailDone : MergedSourceComparison.children compare wides narrows middle = .done true state := by
                    simpa only [MergedSourceComparison.children, first, Result.bind, ↓reduceIte] using done
                  have tailVerified := children_verified compare callback wides narrows middle middleFacts middlePrepared
                    (fun value member => by simpa only [first, Result.state] using verified.available _ value (wideInputs value (List.mem_cons_of_mem _ member)))
                    (fun value member => by simpa only [first, Result.state] using verified.available _ value (narrowInputs value (List.mem_cons_of_mem _ member)))
                    (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                    (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))
                  have backward : Grows middle state := by simpa only [tailDone, Result.state] using tailVerified.growth
                  have equal := MergedComparisonEffectOrder.verified_antisymm state middle (verified.effect first) backward
                  subst middle
                  refine .cons (certify wide narrow wideInput narrowInput wideFree narrowFree first) ?_
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
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      compare wide narrow state = .done true state → relation wide narrow)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (done : anyCover clear compare narrow wides state = .done true state) :
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
        have verified := children_verified compare callback wide.children narrow.children
          state facts prepared wideChildren narrowChildren childrenClosed narrowClosed
        cases first : MergedSourceComparison.children compare wide.children narrow.children state with
        | failed fault middle => simp only [first, Result.bind, reduceCtorEq] at done
        | done answer middle =>
            cases answer with
            | true =>
                have equal : middle = state := (Result.done.inj (by simpa only [first, Result.bind, ↓reduceIte] using done)).2
                subst middle
                exact ⟨wide, List.mem_cons_self, header.1, header.2.2,
                  children_certificate compare callback state facts prepared relation certify
                    wide.children narrow.children wideChildren narrowChildren childrenClosed narrowClosed header.2.1 first⟩
            | false =>
                have middleFacts : Facts middle := by simpa only [first, Result.state] using verified.facts
                have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve verified.unchanged
                have tailDone : anyCover clear compare narrow rest middle = .done true state := by
                  simpa only [first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done
                have tailVerified := anyCover_verified clear compare callback narrow rest middle middleFacts middlePrepared
                  (by simpa only [first, Result.state] using verified.edge _ narrow narrowInput)
                  (fun edge member => by simpa only [first, Result.state] using verified.edge _ edge (wideInputs edge (List.mem_cons_of_mem _ member)))
                  narrowClosed (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
                have backward : Grows middle state := by simpa only [tailDone, Result.state] using tailVerified.growth
                have equal := MergedComparisonEffectOrder.verified_antisymm state middle (verified.effect first) backward
                subst middle
                obtain ⟨cover, member, matched⟩ := ih (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
                  (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
                  (by simpa only [first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done)
                exact ⟨cover, List.mem_cons_of_mem _ member, matched⟩
      · obtain ⟨cover, member, matched⟩ := ih (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done
        exact ⟨cover, List.mem_cons_of_mem _ member, matched⟩

/-- Each successful cache-preserving row loop supplies an actual certified cover. -/
theorem allRows_certificate [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (certify : ∀ wide narrow, Available state wide → Available state narrow → wide.free = [] → narrow.free = [] →
      compare wide narrow state = .done true state → relation wide narrow)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (done : allRows fuel clear compare wide narrows state = .done true state) :
    ∀ narrow ∈ narrows, ∃ wides cover, read fuel wide state = .done wides state ∧ cover ∈ wides ∧
      cover.entry.key.symbol = narrow.entry.key.symbol ∧ clear cover.entry.key.constraint = true ∧
      All₂ relation cover.children narrow.children := by
  induction narrows with
  | nil => simp
  | cons narrow rest ih =>
      obtain ⟨wides, first, second, tail⟩ := MergedComparisonEffectOrder.allRows_fixed fuel clear compare callback
        wide narrow rest state facts prepared wideInput narrowInputs wideClosed narrowClosed done
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨cover, coverIn, matched⟩ := anyCover_certificate clear compare callback state facts prepared relation certify
          edge wides (narrowInputs edge List.mem_cons_self)
          (read_edges fuel wide state facts prepared wideInput wides state first) (narrowClosed edge List.mem_cons_self)
          (read_closed fuel wide state facts prepared wideInput wideClosed wides state first) second
        exact ⟨wides, cover, first, coverIn, matched⟩
      · exact ih (fun row member => narrowInputs row (List.mem_cons_of_mem _ member))
          (fun row member => narrowClosed row (List.mem_cons_of_mem _ member)) tail edge member

/-- Each successful cache-preserving comparison transfers finite terms at every height justified by its ancestors. -/
theorem check_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (rank fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (done : check clear fuel above wide narrow state = .done true state)
    (ancestors : Ancestors state meaning rank above) : Bounded state meaning rank wide narrow := by
  induction rank generalizing fuel above wide narrow with
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
              have current := ih fuel above wide narrow wideInput narrowInput wideClosed narrowClosed originalDone oldAncestors
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
                      check clear fuel ((wideId, narrowId) :: above) left right state = .done true state →
                        Bounded state meaning rank left right := by
                    intro left right leftInput rightInput leftClosed rightClosed finished
                    exact ih fuel ((wideId, narrowId) :: above) left right leftInput rightInput leftClosed rightClosed finished nextAncestors
                  obtain ⟨narrows, first, tailDone⟩ := MergedComparisonEffectOrder.read_allRows_fixed (fuel + 1) clear _ callback
                    wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed true done
                  have readDone := read_done (fuel + 1) narrow state narrows state first
                  have exactRead := (MergedSourceExposureCoverage.actual_exact (fuel + 1) narrow state facts prepared
                    narrowInput narrows state readDone).2 meaning term
                  obtain ⟨edge, member, terms, shape, children, _⟩ := exactRead.mp accepted
                  have covers := allRows_certificate (fuel + 1) clear _ callback state facts prepared
                    (Bounded state meaning rank) certify wide narrows wideInput
                    (read_edges (fuel + 1) narrow state facts prepared narrowInput narrows state first)
                    wideClosed (read_closed (fuel + 1) narrow state facts prepared narrowInput narrowClosed narrows state first)
                    tailDone
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

/-- A successful cache-preserving source comparison contains every finite narrow term. -/
theorem check_fixed_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (done : check clear fuel [] wide narrow state = .done true state)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) narrow term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) wide term :=
  check_bounded state facts prepared clear meaning clearTrue term.height fuel [] wide narrow
    wideInput narrowInput wideClosed narrowClosed done (by intro left right a b c d x y e f impossible; cases impossible)
    term (Nat.le_refl _) accepted

/-- A successful cold comparison is sound in every later retained source cache. -/
theorem check_later_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after view : State Symbol Guard) (done : check clear fuel [] wide narrow state = .done true after)
    (growth : Grows after view) (viewFacts : Facts view) (viewPrepared : Prepared view)
    (viewWide : Available view wide) (viewNarrow : Available view narrow)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) narrow term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) wide term :=
  check_fixed_sound view viewFacts viewPrepared clear meaning clearTrue fuel wide narrow viewWide viewNarrow wideClosed narrowClosed
    (MergedComparisonReplay.check_replay clear fuel [] wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed
      true after view done growth) term accepted

/-- A successful actual ordered comparison contains every narrow term in its actual returned cache. -/
theorem check_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel [] wide narrow state = .done true after)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) narrow term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) wide term := by
  have verified := check_verified clear fuel [] wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed
  have afterFacts : Facts after := by simpa only [done, Result.state] using verified.facts
  have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve verified.unchanged
  have afterWide : Available after wide := by simpa only [done, Result.state] using verified.available _ wide wideInput
  have afterNarrow : Available after narrow := by simpa only [done, Result.state] using verified.available _ narrow narrowInput
  exact check_later_sound state facts prepared clear meaning clearTrue fuel wide narrow wideInput narrowInput wideClosed narrowClosed
    after after done (grows_refl after) afterFacts afterPrepared afterWide afterNarrow term accepted

end MicroCFTA.MergedComparisonSoundness
