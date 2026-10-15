import MicroCFTA.SourceEqualitySharedTargetWorker

/-!
# Shared target function and graph agreement

Successful checked workers give actual first-force graphs. Complete graphs
supply four finite bounds. Every larger quadruple returns the same value,
full native state, and shared closure slots.
-/
namespace MicroCFTA.SourceEqualitySharedTargetWorkerProofs
open InternedConstructorTemplates SourceEqualitySharedTargetState SourceEqualitySharedTargetForce SourceEqualitySharedTargetLeaf
open SourceEqualitySharedTargetLeafComplete SourceEqualitySharedTargetWorker

/-- A successful sequence contains its exact completed first stage and continuation. -/
theorem bind_done (first : Result width Symbol Guard A) (next : A → State width Symbol Guard → Result width Symbol Guard B)
    (result : B) (after : State width Symbol Guard) :
    first.bind next = .done result after ↔ ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro completed; exact ⟨value, state, rfl, completed⟩
      · rintro ⟨actual, middle, same, completed⟩; cases same; exact completed
  | pending | unresolved | exhausted | target | native => simp [Result.bind]

/-- Four finite independent bounds suffice for identical shared results at all larger bounds. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Result width Symbol Guard A) (result : A) (after : State width Symbol Guard) : Prop :=
  ∃ projection head comparison native, ∀ p h c n, projection ≤ p → head ≤ h → comparison ≤ c → native ≤ n → evaluation p h c n = .done result after

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

/-- A successful checked force is either exact reuse or an actual demanded target receipt. -/
theorem force_graph (p h c n : Nat) (path : EqualityNormalize.Path) (before : State width Symbol Guard) (value : Value Symbol Guard) (after : State width Symbol Guard)
    (ranges : ForceRanges emptyGuard conjoin clear top record originals path before)
    (done : force emptyGuard conjoin clear top p h c n record originals path before = .done value after) :
    Force emptyGuard conjoin clear top record originals path before value after := by
  cases present : before.targets path with
  | some stored =>
      simp only [force, present] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .hit present
  | none =>
      cases actual : SourceEqualityDemandTargetWorker.target emptyGuard conjoin clear top p h c n originals
          (SourceEqualityClassTarget.operandPaths record.paths path) before.native with
      | done result native =>
          simp only [force, present, actual] at done
          have parts := Result.done.inj done
          cases parts.1; cases parts.2
          exact .miss present (SourceEqualityDemandTargetWorkerSound.target_graph emptyGuard conjoin clear top p h c n originals _ before.native
            (by simpa only [ForceRanges, present] using ranges) _ _ actual)
      | projection | merge | native => simp only [force, present, actual] at done; cases done

/-- Successful native wrapping retains its exact checked execution and shared target slots. -/
theorem step_graph (n : Nat) (target input : Value Symbol Guard) (before : State width Symbol Guard) (value : Value Symbol Guard) (after : State width Symbol Guard)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native)
    (done : step emptyGuard conjoin n target input before = .done value after) :
    ∃ native, SourceEqualityNativeScoped.Step emptyGuard conjoin target input before.native value native ∧ after = advance before native := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin n (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native with
  | done result native =>
      simp only [step, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact ⟨native, .done n ranges actual, rfl⟩
  | yielded | failed | blocked => simp only [step, actual] at done; cases done

/-- A successful checked leaf gives the actual shared force followed by its native request. -/
theorem leaf_graph (p h c n : Nat) (path : EqualityNormalize.Path) (input : Value Symbol Guard) (before : State width Symbol Guard)
    (value : Value Symbol Guard) (after : State width Symbol Guard) (ranges : LeafRanges emptyGuard conjoin clear top record originals path input before)
    (done : leaf emptyGuard conjoin clear top p h c n record originals path input before = .done value after) :
    Leaf emptyGuard conjoin clear top record originals path input before value after := by
  obtain ⟨target, middle, first, last⟩ := (bind_done _ _ value after).mp done
  have forced := force_graph emptyGuard conjoin clear top record originals p h c n path before target middle ranges.force first
  obtain ⟨native, checked, rfl⟩ := step_graph emptyGuard conjoin n target input middle value after (ranges.step target middle forced) last
  exact .apply forced checked

/-- A completed force is stable with all target slots and the entire native state unchanged on reuse. -/
theorem force_stable {path value before after} (trace : Force (width := width) emptyGuard conjoin clear top record originals path before value after) :
    StableRun (fun p h c n => force emptyGuard conjoin clear top p h c n record originals path before) value after := by
  cases trace with
  | hit present => exact ⟨0, 0, 0, 0, by intros; simp only [force, present]⟩
  | miss absent actual =>
      obtain ⟨p, h, c, n, stable⟩ := SourceEqualityDemandTargetWorkerComplete.target_stable actual
      exact ⟨p, h, c, n, by intro a b d e ep eh ec en; simp only [force, absent, stable a b d e ep eh ec en]⟩

/-- A complete shared leaf stabilizes both actual stages at one finite bound quadruple. -/
theorem leaf_stable {path input value before after} (trace : Leaf (width := width) emptyGuard conjoin clear top record originals path input before value after) :
    StableRun (fun p h c n => leaf emptyGuard conjoin clear top p h c n record originals path input before) value after := by
  cases trace with
  | apply forced actual =>
      obtain ⟨p, h, c, n, stable⟩ := force_stable emptyGuard conjoin clear top record originals forced
      obtain ⟨bound, checked⟩ := actual.stable
      refine ⟨p, h, c, max n bound, ?_⟩
      intro a b d e ep eh ec en
      simp only [leaf, stable a b d e ep eh ec (Nat.le_trans (Nat.le_max_left _ _) en), Result.bind, step,
        checked e (Nat.le_trans (Nat.le_max_right _ _) en)]

end MicroCFTA.SourceEqualitySharedTargetWorkerProofs
