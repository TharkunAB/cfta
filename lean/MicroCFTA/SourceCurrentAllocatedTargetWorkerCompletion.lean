import MicroCFTA.SourceCurrentAllocatedTargetWorker
import MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Exact bounds for current checked target workers

Each completed target graph derives five stable bounds. Projection, allocated
merge, and checked native execution use their literal intermediate states.
The result includes the entire checked state and completed merge table.
This theorem does not derive physical checks from an arbitrary native success.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedTargetGraph (Operand Fold Target)
open SourceCurrentAllocatedTargetQuery (Step)
open SourceCurrentAllocatedTargetWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Every larger five-stage bound returns the same value, checked state, and memo. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome width)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo) : Prop :=
  ∃ projection read merge selection native, ∀ p h m s n,
    projection ≤ p → read ≤ h → merge ≤ m → selection ≤ s → native ≤ n →
      evaluation p h m s n = .done result after saved

/-- A successful bind identifies the literal complete intermediate state and table. -/
theorem bind_done_iff (first : Outcome width)
    (next : Value Symbol Guard → Checked width → Memo → Outcome width)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧
        next value middle current = .done result after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual; exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

/-- Stable stages combine their five bounds at the actual returned state and memo. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Outcome width)
    (next : Nat → Nat → Nat → Nat → Nat → Value Symbol Guard → Checked width → Memo → Outcome width)
    (value : Value Symbol Guard) (middle : Checked width) (current : Memo)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (one : StableRun first value middle current)
    (two : StableRun (fun p h m s n => next p h m s n value middle current) result after saved) :
    StableRun (fun p h m s n => (first p h m s n).bind (next p h m s n)) result after saved := by
  obtain ⟨p, h, m, s, n, done⟩ := one
  obtain ⟨laterP, laterH, laterM, laterS, laterN, nextDone⟩ := two
  refine ⟨max p laterP, max h laterH, max m laterM, max s laterS, max n laterN, ?_⟩
  intro a b c d e enoughP enoughH enoughM enoughS enoughN
  simp only [done a b c d e (Nat.le_trans (Nat.le_max_left _ _) enoughP)
    (Nat.le_trans (Nat.le_max_left _ _) enoughH) (Nat.le_trans (Nat.le_max_left _ _) enoughM)
    (Nat.le_trans (Nat.le_max_left _ _) enoughS) (Nat.le_trans (Nat.le_max_left _ _) enoughN), Outcome.bind,
    nextDone a b c d e (Nat.le_trans (Nat.le_max_right _ _) enoughP)
      (Nat.le_trans (Nat.le_max_right _ _) enoughH) (Nat.le_trans (Nat.le_max_right _ _) enoughM)
      (Nat.le_trans (Nat.le_max_right _ _) enoughS) (Nat.le_trans (Nat.le_max_right _ _) enoughN)]

/-- An actual forest projection supplies stable projection and read bounds. -/
theorem projection_complete [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before : Checked width}
    {result : Value Symbol Guard} {heap : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap) (memo : Memo) :
    StableRun (fun p h _ _ _ => projection p h path values before memo)
      result (advancePhysical before ⟨heap, before.operations⟩) memo := by
  obtain ⟨p, h, stable⟩ := SourceEqualityProjectionWorkerComplete.forest_stable actual
  exact ⟨p, h, 0, 0, 0, by
    intro a b c d e enoughP enoughH _ _ _
    simp only [projection, stable a b enoughP enoughH]⟩

/-- An actual allocated merge supplies stable work and selection bounds. -/
theorem merge_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {value result : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear
      value before memo result after saved) :
    StableRun (fun _ _ m s _ => merge m s value before memo) result after saved := by
  cases actual with
  | done trace =>
      obtain ⟨m, s, stable⟩ := SourceCurrentAllocatedMergeWorkerCompletion.call_complete trace
      exact ⟨0, 0, m, s, 0, by
        intro p h a b n _ _ enoughM enoughS _
        simp only [merge, stable a b enoughM enoughS]⟩

/-- An actual operand supplies stable projection-then-merge execution. -/
theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {path : List Int} {values : List (Value Symbol Guard)}
    {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo}
    (actual : Operand path values before memo result after saved) :
    StableRun (fun p h m s _ => operand p h m s path values before memo) result after saved := by
  cases actual with
  | force projected merged =>
      exact bind_stable _ _ _ _ _ _ _ _ (projection_complete projected memo) (merge_complete merged)

/-- An actual checked request supplies stable native bounds at its exact state. -/
theorem leaf_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : Step left right before result after) (memo : Memo) :
    StableRun (fun _ _ _ _ n => leaf n left right before memo) result after memo := by
  obtain ⟨bound, done⟩ := actual.done
  refine ⟨0, 0, 0, 0, bound, ?_⟩
  intro p h m s n _ _ _ _ enough
  have stable := SourceEqualityNativeDemand.done_stable bound (n - bound) _ before after result done
  have same : bound + (n - bound) = n := by omega
  simp only [same] at stable
  simp only [leaf, stable]

/-- An actual fold supplies bounds for head, tail, and checked intersection in source order. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo}
    (actual : Fold values seed paths before memo result after saved) :
    StableRun (fun p h m s n => fold p h m s n values seed paths before memo) result after saved := by
  induction actual with
  | nil seed => exact operand_complete seed
  | cons operand rest step ih =>
      exact bind_stable _ _ _ _ _ _ _ _ (operand_complete operand)
        (bind_stable _ _ _ _ _ _ _ _ ih (leaf_complete step _))

/-- An actual target supplies stable bounds for the same complete checked state and memo. -/
theorem target_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo}
    (actual : Target values paths before memo result after saved) :
    StableRun (fun p h m s n => target p h m s n values paths before memo) result after saved := by
  cases actual with
  | nil => exact ⟨0, 0, 0, 0, 0, by intros; rfl⟩
  | nonempty fold => exact fold_complete fold

/-- One uniform bound can supply all five independently derived stage bounds. -/
theorem target_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo}
    (actual : Target values paths before memo result after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → target fuel fuel fuel fuel fuel values paths before memo = .done result after saved := by
  obtain ⟨p, h, m, s, n, done⟩ := target_complete actual
  refine ⟨max (max (max (max p h) m) s) n, ?_⟩
  intro fuel enough
  exact done fuel fuel fuel fuel fuel (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem exposure_done_stable {fuel larger : Nat} {value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after) (enough : fuel ≤ larger) :
    MergedFreshOrdinaryExposure.nodeEdges larger value before = .done edges after := by
  have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel (larger - fuel) value before
    (by simp only [actual, MergedSourceExposure.Finished])
  rw [show fuel + (larger - fuel) = larger by omega] at stable
  exact stable.trans actual

private theorem readAll_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} (values : List (Value Symbol Guard))
    {before after : InternedConstructorTemplates.State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionWorker.readAll fuel values before = .done edges after) (enough : fuel ≤ larger) :
    SourceEqualityProjectionWorker.readAll larger values before = .done edges after := by
  induction values generalizing before edges after with
  | nil => exact actual
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
      | done rows middle =>
          simp only [SourceEqualityProjectionWorker.readAll, read] at actual
          obtain ⟨more, final, rest, returned⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ edges after).mp actual
          simp only [SourceEqualityProjectionWorker.readAll, exposure_done_stable read enough,
            SourceEqualityRequiredWorker.Result.bind, ih rest]
          exact returned
      | pending | unresolved | exhausted =>
          simp only [SourceEqualityProjectionWorker.readAll, read] at actual
          cases actual

private theorem union_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} {values : List (Value Symbol Guard)}
    {before after : InternedConstructorTemplates.State Symbol Guard} {value : Value Symbol Guard}
    (actual : SourceEqualityProjectionWorker.union fuel values before = .done value after) (enough : fuel ≤ larger) :
    SourceEqualityProjectionWorker.union larger values before = .done value after := by
  obtain ⟨edges, middle, read, built⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
  simp only [SourceEqualityProjectionWorker.union, readAll_done_stable values read enough,
    SourceEqualityRequiredWorker.Result.bind]
  exact built

private theorem head_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} {input value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityRequiredWorker.head fuel input before = .done value after) (enough : fuel ≤ larger) :
    SourceEqualityRequiredWorker.head larger input before = .done value after := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges fuel input before with
  | done edges middle =>
      simp only [SourceEqualityRequiredWorker.head, read] at actual
      simpa only [SourceEqualityRequiredWorker.head, exposure_done_stable read enough] using actual
  | pending | unresolved | exhausted =>
      simp only [SourceEqualityRequiredWorker.head, read] at actual
      cases actual

private theorem rows_done_stable
    (first next : Value Symbol Guard → InternedConstructorTemplates.State Symbol Guard →
      SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
    (stable : ∀ value before result after, first value before = .done result after → next value before = .done result after)
    (index : Int) (edges : List (EdgeValue Symbol Guard))
    {before after : InternedConstructorTemplates.State Symbol Guard} {results : List (Value Symbol Guard)}
    (actual : SourceEqualityProjectionWorker.rows first index edges before = .done results after) :
    SourceEqualityProjectionWorker.rows next index edges before = .done results after := by
  induction edges generalizing before results after with
  | nil => exact actual
  | cons edge edges ih =>
      cases selected : SourceEqualityProjectionGraph.select edge.children index with
      | none =>
          simp only [SourceEqualityProjectionWorker.rows, selected] at actual ⊢
          exact ih actual
      | some child =>
          simp only [SourceEqualityProjectionWorker.rows, selected] at actual
          obtain ⟨value, middle, firstDone, later⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ results after).mp actual
          obtain ⟨more, final, rest, returned⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ results after).mp later
          simp only [SourceEqualityProjectionWorker.rows, selected, stable _ _ _ _ firstDone,
            SourceEqualityRequiredWorker.Result.bind, ih rest]
          exact returned

private theorem project_done_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    {larger readFuel largerRead : Nat} {path : List Int} {input value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityProjectionWorker.project fuel readFuel path input before = .done value after)
    (enough : fuel ≤ larger) (readEnough : readFuel ≤ largerRead) :
    SourceEqualityProjectionWorker.project larger largerRead path input before = .done value after := by
  induction fuel generalizing larger path input value before after with
  | zero => cases actual
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ remaining =>
          cases path with
          | nil => exact actual
          | cons index path =>
              cases input with
              | empty => exact actual
              | reference => cases actual
              | node entry edges depth free =>
                  obtain ⟨values, middle, rowsDone, built⟩ :=
                    (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
                  have rowsStable := rows_done_stable
                    (SourceEqualityProjectionWorker.project fuel readFuel path)
                    (SourceEqualityProjectionWorker.project remaining largerRead path)
                    (fun child state result final done => ih done (by omega)) index edges rowsDone
                  simp only [SourceEqualityProjectionWorker.project, rowsStable,
                    SourceEqualityRequiredWorker.Result.bind]
                  exact union_done_stable built readEnough
              | mu entry body depth free | union entry members depth free =>
                  obtain ⟨exposed, middle, headDone, rest⟩ :=
                    (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
                  simp only [SourceEqualityProjectionWorker.project, head_done_stable headDone readEnough,
                    SourceEqualityRequiredWorker.Result.bind]
                  exact ih rest (by omega)

/-- Increasing projection and read fuel preserves any successful forest and its complete heap. -/
theorem forest_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {projectionFuel readFuel largerProjection largerRead : Nat} {path : List Int}
    {values : List (Value Symbol Guard)} {before after : InternedConstructorTemplates.State Symbol Guard}
    {value : Value Symbol Guard}
    (actual : SourceEqualityProjectionWorker.forest projectionFuel readFuel path values before = .done value after)
    (enough : projectionFuel ≤ largerProjection) (readEnough : readFuel ≤ largerRead) :
    SourceEqualityProjectionWorker.forest largerProjection largerRead path values before = .done value after := by
  cases path with
  | nil => exact union_done_stable actual readEnough
  | cons index path =>
      cases selected : SourceEqualityProjectionGraph.select values index with
      | none => simpa only [SourceEqualityProjectionWorker.forest, selected] using actual
      | some input =>
          simp only [SourceEqualityProjectionWorker.forest, selected] at actual ⊢
          exact project_done_stable projectionFuel actual enough readEnough

/-- Increasing projection and read fuel preserves the full checked projection return. -/
theorem projection_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : projection p h path values before memo = .done result after saved)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    projection largerP largerH path values before memo = .done result after saved := by
  cases projected : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | done value heap =>
      simp only [projection, projected] at actual
      simp only [projection, forest_done_stable projected enoughP enoughH]
      exact actual
  | pending | unresolved | exhausted =>
      simp only [projection, projected] at actual
      cases actual

/-- Increasing merge work and selection fuel preserves exact operations and memo. -/
theorem merge_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {m s largerM largerS : Nat} {value result : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (actual : merge m s value before memo = .done result after saved)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) :
    merge largerM largerS value before memo = .done result after saved := by
  cases merged : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear m s value (physical before) memo with
  | done value state current =>
      simp only [merge, merged] at actual
      simp only [merge, SourceCurrentAllocatedMergeWorkerCompletion.call_done_stable merged enoughM enoughS]
      exact actual
  | failed =>
      simp only [merge, merged] at actual
      cases actual

/-- Increasing all operand bounds preserves any literal successful complete observation. -/
theorem operand_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h m s largerP largerH largerM largerS : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : operand p h m s path values before memo = .done result after saved)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) :
    operand largerP largerH largerM largerS path values before memo = .done result after saved := by
  obtain ⟨value, middle, current, projected, merged⟩ := (bind_done_iff _ _ result after saved).mp actual
  simp only [operand, projection_done_stable projected enoughP enoughH, Outcome.bind]
  exact merge_done_stable merged enoughM enoughS

/-- Increasing native fuel preserves any successful checked execution without an input plan. -/
theorem leaf_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {n largerN : Nat} {left right result : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (actual : leaf n left right before memo = .done result after saved) (enough : n ≤ largerN) :
    leaf largerN left right before memo = .done result after saved := by
  cases executed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value state =>
      simp only [leaf, executed] at actual
      have stable := SourceEqualityNativeDemand.done_stable n (largerN - n) _ before state value executed
      rw [show n + (largerN - n) = largerN by omega] at stable
      simp only [leaf, stable]
      exact actual
  | yielded | failed | blocked | constraintError =>
      simp only [leaf, executed] at actual
      cases actual

/-- Increasing all five bounds preserves a successful source-ordered fold exactly. -/
theorem fold_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h m s n largerP largerH largerM largerS largerN : Nat}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : fold p h m s n values seed paths before memo = .done result after saved)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM)
    (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    fold largerP largerH largerM largerS largerN values seed paths before memo = .done result after saved := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand_done_stable actual enoughP enoughH enoughM enoughS
  | cons path paths ih =>
      obtain ⟨head, middle, current, operandDone, later⟩ := (bind_done_iff _ _ result after saved).mp actual
      obtain ⟨tail, final, completed, restDone, leafDone⟩ := (bind_done_iff _ _ result after saved).mp later
      simp only [fold, operand_done_stable operandDone enoughP enoughH enoughM enoughS,
        Outcome.bind, ih restDone]
      exact leaf_done_stable leafDone enoughN

/-- Larger stage bounds preserve the same successful value and complete checked state and memo. -/
theorem target_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h m s n largerP largerH largerM largerS largerN : Nat}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : target p h m s n values paths before memo = .done result after saved)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM)
    (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    target largerP largerH largerM largerS largerN values paths before memo = .done result after saved := by
  cases paths with
  | nil => exact actual
  | cons seed paths => exact fold_done_stable actual enoughP enoughH enoughM enoughS enoughN

/-- Successful fuel choices identify the same value, complete checked state, and memo. -/
theorem target_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h m s n otherP otherH otherM otherS otherN : Nat}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before : Checked width} {memo : Memo}
    {first second : Value Symbol Guard} {after later : Checked width} {saved current : Memo}
    (one : target p h m s n values paths before memo = .done first after saved)
    (two : target otherP otherH otherM otherS otherN values paths before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have firstStable := target_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
    (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := target_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
    (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
