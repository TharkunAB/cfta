section ActualCapturedRowsResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

private theorem eager_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
 := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
        alternatives length selected shapes selectionMembers selectionLength reserved
      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
            supported, rfl, rfl, fun _ member => by cases member⟩
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_captured_resources
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, headResources.mono farther.1 farther.2⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved
              let result : Fold := match tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · obtain ⟨lastCaller, lastInventory, lastMemos, lastPost, lastFits, lastKnown, shape⟩ := tailResources
                refine ⟨lastCaller, lastInventory, lastMemos, post.trans lastPost, lastFits, lastKnown, ?_⟩
                cases tailOutcome with
                | complete later remaining finalCaller finalQueries =>
                    obtain ⟨sameCaller, sameQueries, retained⟩ := shape
                    refine ⟨sameCaller, sameQueries, ?_⟩
                    intro output member
                    rcases List.mem_append.mp member with old | fresh
                    · exact (outputResources output old).mono farther.1 farther.2
                    · exact (retained output fresh).post post
                | stopped later remaining current =>
                    obtain ⟨sameEndpoint, retained⟩ := shape
                    refine ⟨sameEndpoint, ?_⟩
                    intro output member
                    rcases List.mem_append.mp member with old | fresh
                    · exact (outputResources output old).mono farther.1 farther.2
                    · exact (retained output fresh).post post
end ActualCapturedRowsResources
