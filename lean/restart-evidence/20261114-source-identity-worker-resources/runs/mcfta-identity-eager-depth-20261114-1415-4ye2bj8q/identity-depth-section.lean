section ActualIdentityEagerDepthClosure
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual identity decision retains its literal zero-depth output resources. -/
private theorem identity_resume_eager_zero_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Unit) (decision : Option Next) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ outcome,
      (∀ workFuel, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel 0 metadata caller memos.query before decision = outcome) ∧
      OutcomeResources formulas solver caller seed outcome := by
  cases decision with
  | none =>
      refine ⟨.complete [⟨some metadata, before, caller, memos.query⟩] caller memos.query,
        (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inr rfl, bounded, known⟩
  | some selected =>
      cases selected with
      | done =>
          refine ⟨.complete [⟨none, before, caller, memos.query⟩] caller memos.query,
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inl rfl, bounded, known⟩
      | stuck =>
          refine ⟨.complete [] caller memos.query, (fun _ => rfl),
            caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
      | expand uv =>
          refine ⟨.stopped [] (.exhausted uv metadata before) (some (caller, memos.query)),
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context,
            bounded, known, Or.inr rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim

/-- The actual identity worker retains its resources at every finite recursive depth. -/
private theorem identity_eager_resume_complete
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerResumeWithNarrowComplete (Typing := Unit) (bits := bits)
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) formulas solver recursiveDepth := by
  induction recursiveDepth with
  | zero =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        _selectionMembers _selectionLength _initialMass _reserved
      obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
        graph checkEmpty edgesOf formulas solver inventory caller memos before metadata
        (SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before)
        seed packet bounded known
      exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩
  | succ depth ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved
      have growth := eagerFinal_ge (depth + 1) seed ceiling
      cases decision : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before with
      | none =>
          obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
            graph checkEmpty edgesOf formulas solver inventory caller memos before metadata none seed packet bounded known
          refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
          intro extra
          simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
                graph checkEmpty edgesOf formulas solver inventory caller memos before metadata (some .done)
                seed packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | stuck =>
              obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
                graph checkEmpty edgesOf formulas solver inventory caller memos before metadata (some .stuck)
                seed packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | expand uv =>
              exact identity_eager_expansion_resources graph checkEmpty edgesOf formulas solver depth ih
                inventory caller memos before metadata uv seed ceiling packet bounded known
                selectionMembers selectionLength initialMass reserved decision

/-- Original reservations give one stable actual identity outcome and every output resource. -/
theorem runEager_identity_finite_complete_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Unit)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome := by
  have complete := identity_eager_resume_complete (bits := bits)
    graph checkEmpty edgesOf formulas solver recursiveFuel
  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
    packet bounded known selectionMembers selectionLength initialMass reserved
  exact ⟨fuel, outcome, fun extra => running extra, resources⟩

end ActualIdentityEagerDepthClosure
