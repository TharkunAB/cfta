import MicroCFTA.UnionFind
import MicroCFTA.EnumerationDriver
import MicroCFTA.EnumerationIndexSource
import MicroCFTA.EnumerationUntil
import MicroCFTA.EnumerationCPS


/-!
# Read-only source representative lookup

The source root function follows parent entries without compression.
The finite bound exposes execution. A successful lookup leaves the input
forest unchanged and returns the earlier findRoot representative.
-/
namespace MicroCFTA.SourceUnionFindRoot

open UnionFind

/-- Follow the source parent chain without constructing a replacement forest. -/
def root : Nat → Forest → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, forest, uv =>
      match forest uv with
      | some (.parent parent) => root fuel forest parent
      | _ => some uv

/-- Pure and compressing lookup return the same representative at each bound. -/
theorem root_eq (fuel : Nat) (forest : Forest) (uv : Nat) :
    root fuel forest uv = (UnionFind.findRoot fuel forest uv).map Result.representative := by
  induction fuel generalizing uv with
  | zero => rfl
  | succ fuel ih =>
      cases lookup : forest uv with
      | none => simp [root, UnionFind.findRoot, lookup]
      | some entry =>
          cases entry with
          | root size => simp [root, UnionFind.findRoot, lookup]
          | parent parent =>
              simp only [root, UnionFind.findRoot, lookup, ih]
              cases UnionFind.findRoot fuel forest parent <;> rfl

/-- Each returned source representative has an actual finite parent path. -/
theorem root_correct (fuel : Nat) (forest : Forest) (uv representative : Nat)
    (completed : root fuel forest uv = some representative) :
    ∃ size, Reaches forest uv representative size := by
  rw [root_eq] at completed
  cases lookup : UnionFind.findRoot fuel forest uv with
  | none => simp [lookup] at completed
  | some found =>
      have same : found.representative = representative := by simpa [lookup] using completed
      exact ⟨found.size, same ▸ (UnionFind.findRoot_correct fuel forest uv found lookup).1⟩

/-- Every finite parent path gives a successful pure execution. -/
theorem root_terminates (forest : Forest) (uv representative size : Nat)
    (path : Reaches forest uv representative size) :
    ∃ fuel, root fuel forest uv = some representative := by
  obtain ⟨fuel, found, completed⟩ := UnionFind.findRoot_terminates path
  have same := (reaches_unique (UnionFind.findRoot_correct fuel forest uv found completed).1 path).1
  exact ⟨fuel, by simp [root_eq, completed, same]⟩

/-- More fuel retains every successful pure representative result. -/
theorem root_moreFuel (fuel extra : Nat) (forest : Forest) (uv representative : Nat)
    (completed : root fuel forest uv = some representative) :
    root (fuel + extra) forest uv = some representative := by
  rw [root_eq] at completed ⊢
  cases lookup : UnionFind.findRoot fuel forest uv with
  | none => simp [lookup] at completed
  | some found =>
      rw [UnionFind.findRoot_moreFuel fuel extra forest uv found lookup]
      simpa [lookup] using completed

end MicroCFTA.SourceUnionFindRoot


/-!
# Complete frames for enumeration path compression

The frame preserves every nonforest field and every root path with its size.
It makes no claim about equal lookup fuel in different forests.
-/

namespace MicroCFTA.EnumerationCompressionFrame
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- Compression changes only the forest and preserves exact root paths. -/
structure Frame (before after : State Symbol Guard) : Prop where
  /-- Compression keeps the allocation counter. -/
  counter : after.counter = before.counter
  /-- Compression keeps every stored slot. -/
  values : after.values = before.values
  /-- Compression keeps every residual obligation. -/
  obligations : after.obligations = before.obligations
  /-- Compression keeps the complete per-variable ancestry function. -/
  recursionAncestry : after.recursionAncestry = before.recursionAncestry
  /-- Compression keeps the current expansion ancestry. -/
  expansionAncestry : after.expansionAncestry = before.expansionAncestry
  /-- Every finite root path has the same representative and size. -/
  reaches : ∀ uv root size,
    UnionFind.Reaches after.representatives uv root size ↔
      UnionFind.Reaches before.representatives uv root size

/-- An unchanged state satisfies the complete frame. -/
theorem Frame.refl (state : State Symbol Guard) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Iff.rfl⟩

/-- Consecutive frames preserve the same fields and root paths. -/
theorem Frame.trans (left : Frame before middle) (right : Frame middle after) : Frame before after :=
  ⟨right.counter.trans left.counter, right.values.trans left.values,
    right.obligations.trans left.obligations, right.recursionAncestry.trans left.recursionAncestry,
    right.expansionAncestry.trans left.expansionAncestry,
    fun uv root size => (right.reaches uv root size).trans (left.reaches uv root size)⟩

/-- A complete frame preserves finite root paths for every variable. -/
theorem Frame.total (frame : Frame before after) (total : UnionFind.Total before.representatives) :
    UnionFind.Total after.representatives := by
  intro uv
  obtain ⟨root, size, path⟩ := total uv
  exact ⟨root, size, (frame.reaches uv root size).mpr path⟩

/-- A pure result changes no state field. -/
theorem pure_frame (value result : α) (before after : State Symbol Guard)
    (success : Success (pure value) before result after) : Frame before after := by
  obtain ⟨_, same⟩ := (success_pure value result before after).mp success
  subst after
  exact .refl before

/-- Reading the complete state changes no field. -/
theorem get_frame (before after value : State Symbol Guard)
    (success : Success get before value after) : Frame before after := by
  obtain ⟨_, same⟩ := (get_success before after value).mp success
  subst after
  exact .refl before

/-- The actual representative read preserves root identities and stored sizes. -/
theorem representative_frame (fuel uv root : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (success : Success (representative fuel uv) before root after) : Frame before after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro other actual size
  exact UnionFind.findRoot_reaches_iff total lookup other actual size

/-- A successful value read retains the actual root, its size, and its slot. -/
theorem getValue_frame (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (total : UnionFind.Total before.representatives)
    (success : Success (getValue fuel uv) before value after) :
    Frame before after ∧ ∃ root size,
      UnionFind.Reaches before.representatives uv root size ∧
      UnionFind.Reaches after.representatives uv root size ∧ before.values[root]? = some value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  obtain ⟨path, preserved⟩ := UnionFind.findRoot_correct fuel before.representatives uv found lookup
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, found.representative, found.size, path, preserved path, stored⟩
  intro other root size
  exact UnionFind.findRoot_reaches_iff total lookup other root size

/-- Resolving one suspended reference preserves the complete frame. -/
private theorem resolve_frame (fuel : Nat) (blocked result : List Nat) (sc : Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (resolve fuel blocked sc) before result after) : Frame before after := by
  unfold resolve at success
  obtain ⟨root, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
  exact (representative_frame fuel sc.var root before middle total reading).trans
    (pure_frame (root :: blocked) result middle after final)

/-- Scanning one value preserves every field outside the forest. -/
private theorem collect_frame (graph : Graph Symbol Guard) (fuel : Nat)
    (accumulator result : List Nat × List Nat) (entry : UVarValue Symbol × Nat)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (collect graph fuel accumulator entry) before result after) : Frame before after := by
  obtain ⟨candidates, blocked⟩ := accumulator
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ =>
      exact pure_frame (candidates, blocked) result before after success
  | unenumerated node scs =>
      unfold collect at success
      obtain ⟨blockedResult, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
      have step : ∀ sc ∈ scs, ∀ accumulator previous result next, Frame before previous →
          Success (resolve fuel accumulator sc) previous result next → Frame before next := by
        intro sc _ accumulator previous result next previousFrame reading
        exact previousFrame.trans
          (resolve_frame fuel accumulator result sc previous next (previousFrame.total total) reading)
      have middleFrame := foldlM_invariant (resolve fuel) (Frame before) scs step
        blocked blockedResult before middle (.refl before) traversed
      exact middleFrame.trans (pure_frame _ result middle after final)

/-- The complete actual scheduler scan changes only root-path representation. -/
theorem findExpandable_frame (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (total : UnionFind.Total before.representatives)
    (success : Success (findExpandable graph fuel) before result after) : Frame before after := by
  unfold findExpandable at success
  change Success (get >>= fun state => do
    let summary ← state.values.zipIdx.foldlM (collect graph fuel) ([], [])
    finishScan summary) before result after at success
  obtain ⟨current, readState, read, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨currentSame, readSame⟩ := (get_success before readState current).mp read
  subst current
  subst readState
  obtain ⟨summary, scanned, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
  have step : ∀ entry ∈ before.values.zipIdx, ∀ accumulator previous result next, Frame before previous →
      Success (collect graph fuel accumulator entry) previous result next → Frame before next := by
    intro entry _ accumulator previous result next previousFrame scanning
    exact previousFrame.trans
      (collect_frame graph fuel accumulator result entry previous next (previousFrame.total total) scanning)
  have scannedFrame := foldlM_invariant (collect graph fuel) (Frame before) before.values.zipIdx step
    ([], []) summary before scanned (.refl before) traversed
  obtain ⟨_, same⟩ := (finishScan_success summary scanned after result).mp final
  subst after
  exact scannedFrame

end MicroCFTA.EnumerationCompressionFrame


/-!
# Waiting counts indexed by current variable classes

The renamed values are a count view. They are not an executed state.
Bucket transfers describe completed count updates. They do not assert an
invariant between the native union or assimilation writes.
-/

namespace MicroCFTA.EnumerationCanonicalWaiting
open EnumerationState EnumerationSchedule

variable {Symbol Guard : Type}

/-- Rename only the suspended references used by the count view. -/
def canonicalValue (roots : Nat → Nat) : UVarValue Symbol → UVarValue Symbol
  | .unenumerated node scs =>
      .unenumerated node (scs.map fun sc => {sc with var := roots sc.var})
  | .enumerated fragment => .enumerated fragment
  | .eliminated => .eliminated

/-- Apply the actual sparse counter fold at each current class key. -/
def count (roots : Nat → Nat) (change : Int) (scs : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) : EnumerationWaitingIndex.Waiting :=
  EnumerationWaitingIndex.count change
    (scs.map fun sc => {sc with var := roots sc.var}) waiting

/-- Remove the old slot references before adding its replacement references. -/
def replace (roots : Nat → Nat) (old new : UVarValue Symbol)
    (waiting : EnumerationWaitingIndex.Waiting) : EnumerationWaitingIndex.Waiting :=
  count roots 1 (references new) (count roots (-1) (references old) waiting)

/-- Every stored count is the exact number of references to its current class. -/
def Correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) : Prop :=
  EnumerationWaitingIndex.Correct (values.map (canonicalValue roots)) waiting

/-- Redirect one old bucket to the selected target bucket. -/
def redirect (target source : Nat) (roots : Nat → Nat) : Nat → Nat :=
  fun uv => if roots uv = source then target else roots uv

/-- Delete the old key and add its full count at the distinct target key. -/
def move (target source : Nat) (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerationWaitingIndex.Waiting :=
  if target = source then waiting else
    match waiting source with
    | none => waiting
    | some waits => fun uv =>
        if uv = source then none
        else if uv = target then some (waits + (waiting target).getD 0)
        else waiting uv

/-- Transfer each supplied old bucket once in the supplied order. -/
def moveMany (target : Nat) (sources : List Nat) (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerationWaitingIndex.Waiting :=
  sources.foldl (fun previous source => move target source previous) waiting

/-- Reference renaming preserves every trie and occurrence. -/
@[simp] theorem references_canonicalValue (roots : Nat → Nat) (value : UVarValue Symbol) :
    references (canonicalValue roots value) =
      (references value).map (fun sc => {sc with var := roots sc.var}) := by
  cases value <;> rfl

/-- Renaming suspended variable IDs does not change candidate membership. -/
@[simp] theorem candidate_canonicalValue (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (value : UVarValue Symbol) : candidate graph (canonicalValue roots value) = candidate graph value := by
  cases value with
  | unenumerated node scs =>
      cases node with
      | none => rfl
      | some node => cases view : graph.node node <;> simp [canonicalValue, candidate, view]
  | enumerated fragment => rfl
  | eliminated => rfl

private theorem replace_eq (roots : Nat → Nat) (old new : UVarValue Symbol)
    (waiting : EnumerationWaitingIndex.Waiting) :
    replace roots old new waiting = EnumerationWaitingIndex.replace
      (canonicalValue roots old) (canonicalValue roots new) waiting := by
  simp only [replace, count, EnumerationWaitingIndex.replace, references_canonicalValue]

/-- A fixed class map gives exact replacement counts at a stored raw slot. -/
theorem replace_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (index : Nat)
    (old new : UVarValue Symbol) (stored : values[index]? = some old)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots (values.set index new) (replace roots old new waiting) := by
  unfold Correct at *
  rw [replace_eq, List.map_set]
  exact EnumerationWaitingIndex.replace_correct (values.map (canonicalValue roots)) index
    (canonicalValue roots old) (canonicalValue roots new) (by simp [stored]) waiting correct

/-- A fresh slot with no suspended references keeps every class count. -/
theorem allocate_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (node : Option Nat)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots (values ++ [.unenumerated node []]) waiting := by
  unfold Correct at *
  simpa [canonicalValue] using
    EnumerationWaitingIndex.allocate_correct (values.map (canonicalValue roots)) node waiting correct

/-- The initial root has no waiting reference under any class map. -/
theorem initial_correct (roots : Nat → Nat) (root : Nat) :
    Correct (Symbol := Symbol) roots [.unenumerated (some root) []] (fun _ => none) := by
  simpa [Correct, canonicalValue] using EnumerationWaitingIndex.initial_correct (Symbol := Symbol) root

/-- The stored keys are exactly the current classes named by suspended references. -/
theorem support_exact (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) (key : Nat) :
    waiting key ≠ none ↔ ∃ value ∈ values, ∃ sc ∈ references value, roots sc.var = key := by
  have original := EnumerationWaitingIndex.support_exact
    (values.map (canonicalValue roots)) waiting correct key
  constructor
  · intro stored
    obtain ⟨mapped, member, sc, present, named⟩ := original.mp stored
    obtain ⟨value, valueMember, same⟩ := List.mem_map.mp member
    subst mapped
    rw [references_canonicalValue] at present
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp present
    subst sc
    exact ⟨value, valueMember, old, oldMember, named⟩
  · rintro ⟨value, valueMember, sc, present, named⟩
    apply original.mpr
    refine ⟨canonicalValue roots value, List.mem_map.mpr ⟨value, valueMember, rfl⟩,
      {sc with var := roots sc.var}, ?_, named⟩
    rw [references_canonicalValue]
    exact List.mem_map.mpr ⟨sc, present, rfl⟩

private abbrev total (roots : Nat → Nat) (values : List (UVarValue Symbol)) (key : Nat) : Int :=
  EnumerationWaitingIndex.total key (values.map (canonicalValue roots))

private theorem occurrences_redirect (target source : Nat) (roots : Nat → Nat)
    (scs : List Suspended) (key : Nat) (different : source ≠ target) :
    EnumerationWaitingIndex.occurrences key
      (scs.map (fun sc => {sc with var := redirect target source roots sc.var})) =
      if key = source then 0
      else if key = target then
        EnumerationWaitingIndex.occurrences source (scs.map (fun sc => {sc with var := roots sc.var})) +
        EnumerationWaitingIndex.occurrences target (scs.map (fun sc => {sc with var := roots sc.var}))
      else EnumerationWaitingIndex.occurrences key (scs.map (fun sc => {sc with var := roots sc.var})) := by
  induction scs with
  | nil => simp [EnumerationWaitingIndex.occurrences]
  | cons first rest ih =>
      by_cases atSource : key = source
      · subst key
        by_cases named : roots first.var = source <;>
          simp_all [redirect, EnumerationWaitingIndex.occurrences]
      · by_cases atTarget : key = target
        · subst key
          by_cases named : roots first.var = source
          · (simp_all [redirect, EnumerationWaitingIndex.occurrences]; omega)
          · by_cases namedTarget : roots first.var = target <;>
              simp_all [redirect, EnumerationWaitingIndex.occurrences]
        · by_cases named : roots first.var = source <;>
            simp_all [redirect, EnumerationWaitingIndex.occurrences]

private theorem total_redirect (target source : Nat) (roots : Nat → Nat)
    (values : List (UVarValue Symbol)) (key : Nat) (different : source ≠ target) :
    total (redirect target source roots) values key =
      if key = source then 0
      else if key = target then total roots values source + total roots values target
      else total roots values key := by
  induction values with
  | nil => simp [total, EnumerationWaitingIndex.total]
  | cons value rest ih =>
      have first := occurrences_redirect target source roots (references value) key different
      simp only [total, List.map_cons, EnumerationWaitingIndex.total, references_canonicalValue] at *
      by_cases atSource : key = source <;> by_cases atTarget : key = target <;> simp_all
      all_goals omega

/-- The literal sparse move matches a class-map redirection without root-fixed premises. -/
theorem move_correct (target source : Nat) (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct (redirect target source roots) values (move target source waiting) := by
  by_cases same : target = source
  · subst target
    have unchanged : redirect source source roots = roots := by
      funext uv
      by_cases named : roots uv = source <;> simp [redirect, named]
    simpa [move, unchanged] using correct
  · have old : ∀ key, waiting key = EnumerationWaitingIndex.encode (total roots values key) := correct
    change ∀ key, move target source waiting key =
      EnumerationWaitingIndex.encode (total (redirect target source roots) values key)
    intro key
    have transferred := total_redirect target source roots values key (Ne.symm same)
    cases sourceValue : waiting source with
    | none =>
        have sourceZero : total roots values source = 0 := by
          have encoded := old source
          rw [sourceValue] at encoded
          by_cases zero : total roots values source = 0
          · exact zero
          · simp [EnumerationWaitingIndex.encode, zero] at encoded
        simp only [move, ite_eq_right same, sourceValue]
        rw [old key, transferred]
        by_cases atSource : key = source <;> by_cases atTarget : key = target <;>
          simp_all [EnumerationWaitingIndex.encode]
    | some amount =>
        have positive : 0 < amount := EnumerationWaitingIndex.stored_positive
          (values.map (canonicalValue roots)) waiting correct source amount sourceValue
        have sourceNonzero : total roots values source ≠ 0 := by
          intro zero
          have encoded := old source
          rw [sourceValue, zero] at encoded
          simp [EnumerationWaitingIndex.encode] at encoded
        have sourceCount : total roots values source = amount := by
          have encoded := sourceValue
          rw [old source] at encoded
          simpa [EnumerationWaitingIndex.encode, sourceNonzero] using encoded
        have targetCount : (waiting target).getD 0 = total roots values target := by
          rw [old target]
          exact EnumerationWaitingIndex.encode_read _
        have targetNonnegative : 0 ≤ total roots values target :=
          EnumerationWaitingIndex.total_nonnegative target (values.map (canonicalValue roots))
        simp only [move, ite_eq_right same, sourceValue]
        rw [transferred]
        by_cases atSource : key = source
        · subst key
          simp [EnumerationWaitingIndex.encode]
        · by_cases atTarget : key = target
          · subst key
            simp only [ite_eq_right atSource]
            rw [targetCount]
            have sumNonzero : amount + total roots values target ≠ 0 := by omega
            simp [EnumerationWaitingIndex.encode, sourceCount, sumNonzero]
          · simp only [ite_eq_right atSource, ite_eq_right atTarget]
            exact old key

/-- A transfer fold maintains the count view under the matching ghost redirect fold. -/
theorem moveMany_correct (target : Nat) (sources : List Nat) (roots : Nat → Nat)
    (values : List (UVarValue Symbol)) (waiting : EnumerationWaitingIndex.Waiting)
    (correct : Correct roots values waiting) :
    Correct (sources.foldl (fun previous source => redirect target source previous) roots) values
      (moveMany target sources waiting) := by
  induction sources generalizing roots waiting with
  | nil => exact correct
  | cons source rest ih =>
      simpa only [moveMany, List.foldl_cons] using
        ih (redirect target source roots) (move target source waiting)
          (move_correct target source roots values waiting correct)

/-- Completed assimilation keeps the counts when it moves all source references to the target. -/
theorem assimilation_correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (target source : Nat) (oldSource oldTarget merged : UVarValue Symbol)
    (different : target ≠ source) (sourceRead : values[source]? = some oldSource)
    (targetRead : values[target]? = some oldTarget)
    (mergedRefs : references merged = references oldSource ++ references oldTarget)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots ((values.set target merged).set source .eliminated) waiting := by
  unfold Correct at *
  rw [List.map_set, List.map_set]
  intro key
  have targetStored : (values.map (canonicalValue roots))[target]? =
      some (canonicalValue roots oldTarget) := by simp [targetRead]
  have sourceStored : ((values.map (canonicalValue roots)).set target
      (canonicalValue roots merged))[source]? = some (canonicalValue roots oldSource) := by
    rw [List.getElem?_set_ne different]
    simp [sourceRead]
  have mergedCount : EnumerationWaitingIndex.occurrences key (references (canonicalValue roots merged)) =
      EnumerationWaitingIndex.occurrences key (references (canonicalValue roots oldSource)) +
      EnumerationWaitingIndex.occurrences key (references (canonicalValue roots oldTarget)) := by
    simp only [references_canonicalValue, mergedRefs, List.map_append,
      EnumerationWaitingIndex.occurrences_append]
  apply Eq.trans (correct key)
  apply congrArg EnumerationWaitingIndex.encode
  rw [show canonicalValue roots (.eliminated : UVarValue Symbol) = .eliminated from rfl]
  rw [EnumerationWaitingIndex.total_set key source
      ((values.map (canonicalValue roots)).set target (canonicalValue roots merged))
      (canonicalValue roots oldSource) .eliminated sourceStored,
    EnumerationWaitingIndex.total_set key target (values.map (canonicalValue roots))
      (canonicalValue roots oldTarget) (canonicalValue roots merged) targetStored]
  simp only [references, EnumerationWaitingIndex.occurrences] at mergedCount ⊢
  omega

end MicroCFTA.EnumerationCanonicalWaiting


/-!
# Pure selection from canonical enumeration indexes

The waiting keys are representatives, as in the current Haskell source.
Selection reads the indexes and changes no forest. The older slot scan
returns the same offered list and preserves the complete compression frame.
-/
namespace MicroCFTA.EnumerationPureSelection

open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationExpandableIndex (Cached)

/-- Candidate flags and canonical waiting counts describe the stored slots. -/
structure Correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard) : Prop where
  /-- The dense slot domain agrees with the allocation supply. -/
  aligned : state.core.counter = state.core.values.length
  /-- Each flag is the actual source candidate predicate. -/
  expandable : ∀ uv, state.expandable uv = ((state.core.values[uv]?).map (candidate graph)).getD false
  /-- Each waiting key counts references to its representative class. -/
  waiting : EnumerationCanonicalWaiting.Correct roots state.core.values state.waiting

/-- Replace one raw slot and update its candidate flag and canonical counts. -/
def write (graph : Graph Symbol Guard) (roots : Nat → Nat) (uv : Nat) (value : UVarValue Symbol)
    (state : Cached Symbol Guard) : Option (Cached Symbol Guard) := do
  let old ← state.core.values[uv]?
  pure ⟨{state.core with values := state.core.values.set uv value},
    fun other => if other = uv then candidate graph value else state.expandable other,
    EnumerationCanonicalWaiting.replace roots old value state.waiting⟩

/-- Transfer the old representative counters to the final union representative. -/
def transfer (target : Nat) (sources : List Nat) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  {state with waiting := EnumerationCanonicalWaiting.moveMany target sources state.waiting}

/-- The actual initial candidate set and empty waiting map are correct. -/
theorem initial_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (root : Nat) :
    Correct graph roots (EnumerationExpandableIndex.initial graph root) := by
  refine ⟨rfl, ?_, EnumerationCanonicalWaiting.initial_correct roots root⟩
  intro uv
  cases uv <;> simp [EnumerationExpandableIndex.initial, EnumerationState.initial]

/-- Fresh allocation preserves both maintained indexes. -/
theorem allocate_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (node : Option Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state) :
    Correct graph roots (EnumerationExpandableIndex.allocate graph node state) := by
  refine ⟨allocated_supply node state.core correct.aligned, ?_,
    EnumerationCanonicalWaiting.allocate_correct roots state.core.values node state.waiting correct.waiting⟩
  intro uv
  by_cases before : uv < state.core.values.length
  · have different : uv ≠ state.core.counter := by rw [correct.aligned]; omega
    simp only [EnumerationExpandableIndex.allocate, allocated, List.getElem?_append_left before]
    simp [different, correct.expandable uv]
  · by_cases same : uv = state.core.counter
    · simp [EnumerationExpandableIndex.allocate, allocated, correct.aligned, same, correct.expandable]
    · have after : state.core.values.length < uv := by rw [correct.aligned] at same; omega
      have absent : state.core.values[uv]? = none := List.getElem?_eq_none (by omega)
      have wholeAbsent : (state.core.values ++ [.unenumerated node []])[uv]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [EnumerationExpandableIndex.allocate, allocated, same, wholeAbsent, correct.expandable, absent]

/-- A successful source slot write preserves the candidate and canonical-count equations. -/
theorem write_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (uv : Nat) (value : UVarValue Symbol)
    (before after : Cached Symbol Guard) (correct : Correct graph roots before)
    (done : write graph roots uv value before = some after) : Correct graph roots after := by
  cases stored : before.core.values[uv]? with
  | none => simp [write, stored] at done
  | some old =>
      simp [write, stored] at done
      subst after
      refine ⟨by simpa using correct.aligned, ?_,
        EnumerationCanonicalWaiting.replace_correct roots before.core.values uv old value stored before.waiting correct.waiting⟩
      intro other
      by_cases same : other = uv
      · subst other
        have bound := (List.getElem?_eq_some_iff.mp stored).1
        simp [bound]
      · simp [same, Ne.symm same, correct.expandable other]

/-- Slot and supply preservation retains the index equations at a fixed root map. -/
theorem frame_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (core : State Symbol Guard) (correct : Correct graph roots state)
    (values : core.values = state.core.values) (counter : core.counter = state.core.counter) :
    Correct graph roots (EnumerationExpandableIndex.frame core state) := by
  refine ⟨counter.trans (correct.aligned.trans (congrArg List.length values.symm)), ?_, ?_⟩
  · intro uv; simpa [EnumerationExpandableIndex.frame, values] using correct.expandable uv
  · simpa [EnumerationExpandableIndex.frame, values] using correct.waiting

/-- Counter transfer follows the partial root map through the complete transfer fold. -/
theorem transfer_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (target : Nat) (sources : List Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state) :
    Correct graph (sources.foldl (fun currentRoots source => EnumerationCanonicalWaiting.redirect target source currentRoots) roots)
      (transfer target sources state) :=
  ⟨correct.aligned, correct.expandable,
    EnumerationCanonicalWaiting.moveMany_correct target sources roots state.core.values state.waiting correct.waiting⟩

/-- Apply both empty-delta assimilation writes and retain the waiting table. -/
def assimilate (graph : Graph Symbol Guard) (target source : Nat) (merged : UVarValue Symbol)
    (state : Cached Symbol Guard) : Cached Symbol Guard :=
  ⟨assimilated state.core target source merged,
    fun uv => if uv = source then false else if uv = target then candidate graph merged else state.expandable uv,
    state.waiting⟩

/-- Completed assimilation preserves the canonical invariant at its actual endpoint. -/
theorem assimilate_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state)
    (target source : Nat) (oldSource oldTarget merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : state.core.values[source]? = some oldSource)
    (targetRead : state.core.values[target]? = some oldTarget)
    (intersection : intersectValues graph oldSource oldTarget = some merged) :
    Correct graph roots (assimilate graph target source merged state) := by
  refine ⟨by simpa [assimilate, assimilated] using correct.aligned, ?_, ?_⟩
  · intro uv
    have sourceBound := (List.getElem?_eq_some_iff.mp sourceRead).1
    have targetBound := (List.getElem?_eq_some_iff.mp targetRead).1
    by_cases atSource : uv = source
    · subst uv
      simp [assimilate, assimilated, sourceBound, candidate]
    · by_cases atTarget : uv = target
      · subst uv
        simp [assimilate, assimilated, atSource, Ne.symm different, targetBound]
      · simp [assimilate, assimilated, atSource, atTarget, Ne.symm atSource,
          Ne.symm atTarget, correct.expandable uv]
  · exact EnumerationCanonicalWaiting.assimilation_correct roots state.core.values
      target source oldSource oldTarget merged different sourceRead targetRead
      (EnumerationIndexSource.intersection_references graph oldSource oldTarget merged intersection)
      state.waiting correct.waiting

/-- The live pending-slot branch has the same complete core and correct canonical indexes. -/
theorem assimilate_source (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state)
    (target source : Nat) (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended)
    (merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : state.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetRead : state.core.values[target]? = some (.unenumerated targetNode targetScs))
    (intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
      (.unenumerated targetNode targetScs) = some merged)
    (notEmpty : hasEmptyContents graph merged = false) :
    Correct graph roots (assimilate graph target source merged state) ∧
      EnumerationState.assimilate graph target source state.core =
        [.ok ((), (assimilate graph target source merged state).core)] := by
  exact ⟨assimilate_correct graph roots state correct target source _ _ merged different
      sourceRead targetRead intersection,
    assimilate_exact graph state.core target source sourceNode targetNode sourceScs targetScs merged
      different sourceRead targetRead intersection notEmpty⟩

/-- The cached candidate list is exactly the stop test's complete pending list. -/
theorem candidates_exact (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) :
    EnumerationIndexSelection.candidates state = EnumerationUntil.remaining graph state.core := by
  unfold EnumerationIndexSelection.candidates EnumerationUntil.remaining
  rw [correct.aligned, List.range_eq_range', ← List.zipIdx_map_snd 0 state.core.values, List.filter_map]
  congr 1
  apply List.filter_congr
  intro entry member
  have stored := List.mem_zipIdx_iff_getElem?.mp member
  simp only [Function.comp_def, correct.expandable, stored, Option.map_some, Option.getD_some]

/-- Subtract canonical waiting keys without a lookup or a compression write. -/
def find (state : Cached Symbol Guard) : Option (List Nat) :=
  let candidates := EnumerationIndexSelection.candidates state
  if candidates.isEmpty then none
  else some (candidates.filter fun uv => (state.waiting uv).isNone)

/-- Apply the source preference rule to the pure candidate-minus-waiting result. -/
def next (preference : List Nat → Option Nat) (state : Cached Symbol Guard) : Next :=
  pickNext preference (find state)

/-- Execute the pure lookup through the existing source CPS state operation. -/
def findAction : EnumerationCPS.Computation (Cached Symbol Guard) (Option (List Nat)) :=
  EnumerationCPS.state fun state => (find state, state)

/-- Pure cached lookup returns one result with the complete input state unchanged. -/
theorem findAction_represents : EnumerationCPS.Represents
    (findAction : EnumerationCPS.Computation (Cached Symbol Guard) (Option (List Nat)))
    (fun state => [(find state, state)]) :=
  EnumerationCPS.state_represents (fun state => (find state, state))

/-- Canonical cached selection equals the full slot scan's mathematical summary. -/
theorem find_exact (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) :
    find state = let summary := state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])
      offered summary.1 summary.2 := by
  have candidatesSame : EnumerationIndexSelection.candidates state =
      (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).1 := by
    rw [candidates_exact graph roots state correct, EnumerationIndexSelection.candidate_fold]
    rfl
  have blocked (uv : Nat) : state.waiting uv ≠ none ↔
      uv ∈ (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).2 :=
    (EnumerationCanonicalWaiting.support_exact roots state.core.values state.waiting correct.waiting uv).trans
      (EnumerationIndexSelection.scan_blocked graph roots state.core.values uv).symm
  unfold find
  rw [candidatesSame]
  unfold offered
  dsimp only
  split
  · rfl
  · congr 1
    apply List.filter_congr
    intro uv _
    cases stored : state.waiting uv with
    | none =>
        have absent : uv ∉ (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).2 :=
          fun present => (blocked uv).mpr present stored
        simp [absent]
    | some count =>
        have present := (blocked uv).mp (by simp [stored])
        simp [present]

/-- Every successful old scan agrees with pure selection and retains the full compression frame. -/
theorem scan_agrees (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) (paths : Roots state.core.representatives roots)
    (fuel : Nat) (result : Option (List Nat)) (after : State Symbol Guard)
    (success : Success (findExpandable graph fuel) state.core result after) :
    result = find state ∧ EnumerationCompressionFrame.Frame state.core after := by
  have total : UnionFind.Total state.core.representatives := by
    intro uv
    obtain ⟨size, path⟩ := paths uv
    exact ⟨roots uv, size, path⟩
  exact ⟨(findExpandable_exact graph fuel roots state.core after result paths success).2.trans
    (find_exact graph roots state correct).symm,
    EnumerationCompressionFrame.findExpandable_frame graph fuel state.core after result total success⟩

/-- A total representative interpretation supplies a finite old scan for the same pure selection. -/
theorem scan_complete (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) (paths : Roots state.core.representatives roots) :
    ∃ fuel after, Success (findExpandable graph fuel) state.core (find state) after ∧
      EnumerationCompressionFrame.Frame state.core after := by
  have total : UnionFind.Total state.core.representatives := by
    intro uv
    obtain ⟨size, path⟩ := paths uv
    exact ⟨roots uv, size, path⟩
  obtain ⟨fuel, result, after, success⟩ := EnumerationExecution.findExpandable_terminates graph state.core total
  obtain ⟨same, frame⟩ := scan_agrees graph roots state correct paths fuel result after success
  exact ⟨fuel, after, same ▸ success, frame⟩

end MicroCFTA.EnumerationPureSelection
