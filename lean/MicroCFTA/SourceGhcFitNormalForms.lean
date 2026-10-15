import MicroCFTA.Cache

/-!
# Current GHC fit filtering by completed normal keys

This module follows the streamFits acceptance branches at main e16f3b50.
Inputs are completed checked Walk fits. Normal lookup, replacement checks,
and caller effects are explicit completed functions. No evaluator fuel or
Core translation is introduced. Equal keys define only the stated quotient
on known normal forms. They do not imply Haskell contextual equality.
-/
namespace MicroCFTA.SourceGhcFitNormalForms
variable {Program Normal Host Name : Type}

/-- A completed fit from the checked source Walk retains its original program and size. -/
structure CheckedFit (Program : Type) where
  program : Program
  size : Int

/-- The source callback receives both independent reasons to place a fit last. -/
structure Fit (Program : Type) where
  program : Program
  size : Int
  ignoresPart : Bool
  dropsArgument : Bool

/-- The source delays either kind of degenerate fit. -/
def comesLast (fit : Fit Program) : Bool := fit.ignoresPart || fit.dropsArgument

/-- Missing normal forms do not establish that an argument was dropped. -/
def dropsArgument (required : List Name) (mentions : Normal → Name → Bool) : Option Normal → Bool
  | none => false
  | some normal => !(required.all (mentions normal))

/-- The filter owns its seen normal keys and merge count; callback state stays explicit. -/
structure State (Normal Host : Type) where
  seen : Normal → Bool
  merged : Nat
  host : Host

/-- Each stream starts with an empty normal-key set and merge count. -/
def initial (host : Host) : State Normal Host := ⟨fun _ => false, 0, host⟩

/-- Source Set.insert is modeled by its exact membership effect. -/
def insert [DecidableEq Normal] (seen : Normal → Bool) (normal : Normal) : Normal → Bool :=
  fun key => if key = normal then true else seen key

/-- Events retain the order of normal lookup, insertion, part checks, and caller acceptance. -/
inductive Event (Program Normal : Type) where
  | normal (program : Program) (result : Option Normal)
  | insert (normal : Normal)
  | merged (normal : Normal)
  | parts (program : Program) (ignoresPart : Bool)
  | accepted (fit : Fit Program) (more : Bool)

/-- Count delivered stream callbacks, including the callback that stops the walk. -/
def emissions : List (Event Program Normal) → Nat
  | [] => 0
  | .accepted _ _ :: rest => emissions rest + 1
  | _ :: rest => emissions rest

/-- Sequential event lists add their delivered callback counts. -/
theorem emissions_append (first second : List (Event Program Normal)) :
    emissions (first ++ second) = emissions first + emissions second := by
  induction first with
  | nil => simp only [List.nil_append, emissions, Nat.zero_add]
  | cons event rest ih => cases event <;> simp [emissions, ih, Nat.add_comm, Nat.add_left_comm]

/-- A source acceptance call returns its continuation flag and actual local state. -/
structure StepResult (Program Normal Host : Type) where
  more : Bool
  after : State Normal Host
  events : List (Event Program Normal)

/-- Replacement checks complete before the caller receives the original program and both flags. -/
def checkParts (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (input : CheckedFit Program) (drops : Bool) (before : State Normal Host) : StepResult Program Normal Host :=
  let checked := parts input.program before.host
  let fit := Fit.mk input.program input.size checked.1 drops
  let accepted := accept fit checked.2
  ⟨accepted.1, {before with host := accepted.2}, [.parts input.program checked.1, .accepted fit accepted.1]⟩

/-- Execute the actual normal-key guard before any replacement check or caller callback. -/
def step [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (input : CheckedFit Program) (before : State Normal Host) : StepResult Program Normal Host :=
  if enabled then
    match normalOf input.program with
    | none =>
        let checked := checkParts parts accept input false before
        {checked with events := .normal input.program none :: checked.events}
    | some normal =>
        if before.seen normal then
          ⟨true, {before with merged := before.merged + 1}, [.normal input.program (some normal), .merged normal]⟩
        else
          let checked := checkParts parts accept input (dropsArgument required mentions (some normal))
            {before with seen := insert before.seen normal}
          {checked with events := .normal input.program (some normal) :: .insert normal :: checked.events}
  else checkParts parts accept input false before

/-- A disabled filter bypasses normal lookup and the seen set. -/
theorem step_disabled [DecidableEq Normal] (required : List Name) (normalOf : Program → Option Normal)
    (mentions : Normal → Name → Bool) (parts : Program → Host → Bool × Host)
    (accept : Fit Program → Host → Bool × Host) (input : CheckedFit Program) (before : State Normal Host) :
    step false required normalOf mentions parts accept input before = checkParts parts accept input false before := rfl

/-- Unknown normal forms are retained, add no key, and carry dropsArgument=False. -/
theorem step_unknown [DecidableEq Normal] (required : List Name) (normalOf : Program → Option Normal)
    (mentions : Normal → Name → Bool) (parts : Program → Host → Bool × Host)
    (accept : Fit Program → Host → Bool × Host) (input : CheckedFit Program) (before : State Normal Host)
    (unknown : normalOf input.program = none) :
    step true required normalOf mentions parts accept input before =
      let checked := checkParts parts accept input false before
      {checked with events := .normal input.program none :: checked.events} := by
  simp only [step, unknown, ↓reduceIte]

/-- A duplicate increments only merged, returns True, and calls neither parts nor accept. -/
theorem step_duplicate [DecidableEq Normal] (required : List Name) (normalOf : Program → Option Normal)
    (mentions : Normal → Name → Bool) (parts : Program → Host → Bool × Host)
    (accept : Fit Program → Host → Bool × Host) (input : CheckedFit Program) (before : State Normal Host)
    (normal : Normal) (known : normalOf input.program = some normal) (present : before.seen normal = true) :
    step true required normalOf mentions parts accept input before =
      ⟨true, {before with merged := before.merged + 1}, [.normal input.program (some normal), .merged normal]⟩ := by
  simp only [step, known, present, ↓reduceIte]

/-- A fresh normal key is inserted before both later calls, including a stopping callback. -/
theorem step_fresh [DecidableEq Normal] (required : List Name) (normalOf : Program → Option Normal)
    (mentions : Normal → Name → Bool) (parts : Program → Host → Bool × Host)
    (accept : Fit Program → Host → Bool × Host) (input : CheckedFit Program) (before : State Normal Host)
    (normal : Normal) (known : normalOf input.program = some normal) (absent : before.seen normal = false) :
    step true required normalOf mentions parts accept input before =
      let checked := checkParts parts accept input (dropsArgument required mentions (some normal))
        {before with seen := insert before.seen normal}
      {checked with events := .normal input.program (some normal) :: .insert normal :: checked.events} := by
  simp only [step, known, absent, Bool.false_eq_true, ↓reduceIte]

/-- No required argument can be dropped when the required list is empty. -/
theorem drops_empty (mentions : Normal → Name → Bool) (normal : Option Normal) :
    dropsArgument [] mentions normal = false := by cases normal <;> rfl

/-- The drop flag is exactly a missing required leaf in the completed normal form. -/
theorem drops_missing (required : List Name) (mentions : Normal → Name → Bool) (normal : Normal) :
    dropsArgument required mentions (some normal) = true ↔
      ∃ name ∈ required, mentions normal name = false := by
  simp [dropsArgument]

/-- Every attempted fit is either merged or delivered once to the caller. -/
theorem step_accounting [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (input : CheckedFit Program) (before : State Normal Host) :
    emissions (step enabled required normalOf mentions parts accept input before).events +
      (step enabled required normalOf mentions parts accept input before).after.merged = before.merged + 1 := by
  cases enabled with
  | false => simp [step, checkParts, emissions, Nat.add_comm]
  | true =>
      cases known : normalOf input.program with
      | none => simp [step, known, checkParts, emissions, Nat.add_comm]
      | some normal =>
          cases present : before.seen normal <;> simp [step, known, present, checkParts, emissions, Nat.add_comm]

/-- The current candidate supplies both known-key and earlier-key membership effects. -/
theorem step_seen [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (input : CheckedFit Program) (before : State Normal Host) :
    (∀ normal, before.seen normal = true → (step enabled required normalOf mentions parts accept input before).after.seen normal = true) ∧
    (enabled = true → ∀ normal, normalOf input.program = some normal →
      (step enabled required normalOf mentions parts accept input before).after.seen normal = true) := by
  cases enabled with
  | false => exact ⟨fun _ present => present, by intro impossible; cases impossible⟩
  | true =>
      cases known : normalOf input.program with
      | none =>
          rw [step_unknown required normalOf mentions parts accept input before known]
          exact ⟨fun _ present => present, by intro _ normal impossible; cases impossible⟩
      | some normal =>
          cases present : before.seen normal with
          | true =>
              rw [step_duplicate required normalOf mentions parts accept input before normal known present]
              exact ⟨fun _ prior => prior, by intro _ other equal; cases equal; exact present⟩
          | false =>
              rw [step_fresh required normalOf mentions parts accept input before normal known present]
              constructor
              · intro other prior
                change insert before.seen normal other = true
                simp only [insert]
                split <;> first | rfl | exact prior
              · intro _ other equal
                cases equal
                change insert before.seen normal normal = true
                simp only [insert, ↓reduceIte]

/-- A finite supplied Walk prefix retains the undemanded tail when a caller stops. -/
structure Result (Program Normal Host : Type) where
  after : State Normal Host
  events : List (Event Program Normal)
  remaining : List (CheckedFit Program)
  stopped : Bool

/-- Consume attempted fits in order and stop immediately after the first False callback. -/
def run [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host) :
    List (CheckedFit Program) → State Normal Host → Result Program Normal Host
  | [], before => ⟨before, [], [], false⟩
  | input :: rest, before =>
      let first := step enabled required normalOf mentions parts accept input before
      if first.more then
        let later := run enabled required normalOf mentions parts accept rest first.after
        {later with events := first.events ++ later.events}
      else ⟨first.after, first.events, rest, true⟩

/-- A stopping callback preserves its updated state and leaves every later fit undemanded. -/
theorem run_stop [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (input : CheckedFit Program) (rest : List (CheckedFit Program)) (before : State Normal Host)
    (stops : (step enabled required normalOf mentions parts accept input before).more = false) :
    run enabled required normalOf mentions parts accept (input :: rest) before =
      ⟨(step enabled required normalOf mentions parts accept input before).after,
        (step enabled required normalOf mentions parts accept input before).events, rest, true⟩ := by
  simp only [run, stops, Bool.false_eq_true, ↓reduceIte]

/-- Every remaining candidate is an exact suffix of the original supplied prefix. -/
theorem run_suffix [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (inputs : List (CheckedFit Program)) (before : State Normal Host) :
    ∃ processed, inputs = processed ++ (run enabled required normalOf mentions parts accept inputs before).remaining := by
  induction inputs generalizing before with
  | nil => exact ⟨[], rfl⟩
  | cons input rest ih =>
      cases more : (step enabled required normalOf mentions parts accept input before).more with
      | false => exact ⟨[input], by simp only [run, more, Bool.false_eq_true, ↓reduceIte, List.singleton_append]⟩
      | true =>
          obtain ⟨processed, same⟩ := ih (step enabled required normalOf mentions parts accept input before).after
          exact ⟨input :: processed, by simpa only [run, more, Bool.true_eq, ↓reduceIte, List.cons_append, List.cons.injEq, true_and] using same⟩

/-- Every earlier normal key remains seen throughout the actual finite prefix. -/
theorem run_seen [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (inputs : List (CheckedFit Program)) (before : State Normal Host) (normal : Normal) (present : before.seen normal = true) :
    (run enabled required normalOf mentions parts accept inputs before).after.seen normal = true := by
  induction inputs generalizing before with
  | nil => exact present
  | cons input rest ih =>
      have kept := (step_seen enabled required normalOf mentions parts accept input before).1 normal present
      simp only [run]
      split
      · exact ih _ kept
      · exact kept

/-- Delivered fits plus merged fits equal exactly the consumed supplied prefix. -/
theorem run_accounting [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (inputs : List (CheckedFit Program)) (before : State Normal Host) :
    emissions (run enabled required normalOf mentions parts accept inputs before).events +
      (run enabled required normalOf mentions parts accept inputs before).after.merged +
      (run enabled required normalOf mentions parts accept inputs before).remaining.length =
        before.merged + inputs.length := by
  induction inputs generalizing before with
  | nil => simp only [run, emissions, List.length_nil, Nat.zero_add, Nat.add_zero]
  | cons input rest ih =>
      let first := step enabled required normalOf mentions parts accept input before
      have one := step_accounting enabled required normalOf mentions parts accept input before
      have later := ih first.after
      change emissions first.events + first.after.merged = before.merged + 1 at one
      simp only [run]
      split
      · change emissions (first.events ++ (run enabled required normalOf mentions parts accept rest first.after).events) +
          (run enabled required normalOf mentions parts accept rest first.after).after.merged +
          (run enabled required normalOf mentions parts accept rest first.after).remaining.length = before.merged + (input :: rest).length
        rw [emissions_append]
        simp only [List.length_cons]
        omega
      · change emissions first.events + first.after.merged + rest.length = before.merged + (input :: rest).length
        simp only [List.length_cons]
        omega

/-- A call at the returned state skips an earlier key after intervening checks and callback effects. -/
theorem repeated_skips [DecidableEq Normal] (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Host → Bool × Host) (accept : Fit Program → Host → Bool × Host)
    (first later : CheckedFit Program) (middle : List (CheckedFit Program)) (before : State Normal Host)
    (normal : Normal) (firstKnown : normalOf first.program = some normal) (laterKnown : normalOf later.program = some normal) :
    let current := (run true required normalOf mentions parts accept middle
      (step true required normalOf mentions parts accept first before).after).after
    step true required normalOf mentions parts accept later current =
      ⟨true, {current with merged := current.merged + 1}, [.normal later.program (some normal), .merged normal]⟩ := by
  dsimp only
  apply step_duplicate required normalOf mentions parts accept later _ normal laterKnown
  exact run_seen true required normalOf mentions parts accept middle _ normal
    ((step_seen true required normalOf mentions parts accept first before).2 rfl normal firstKnown)

/-- Only programs with a completed known key belong to the intended normal-form quotient domain. -/
def NormalDomain (normalOf : Program → Option Normal) := {program // (normalOf program).isSome = true}

/-- Quotient equality compares literal completed keys and makes no contextual-language claim. -/
def NormalEquivalent (normalOf : Program → Option Normal) (first second : NormalDomain normalOf) : Prop :=
  normalOf first.val = normalOf second.val

/-- Literal known-key equality is an equivalence on its explicit domain. -/
theorem normal_equivalence (normalOf : Program → Option Normal) : Equivalence (NormalEquivalent normalOf) :=
  ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

/-- The source quota counts only delivered fits that do not come last. -/
def quotaAccept (limit : Int) (fit : Fit Program) (found : List (Fit Program)) : Bool × List (Fit Program) :=
  let next := fit :: found
  (decide ((next.filter (fun value => !comesLast value)).length < limit), next)

/-- The source does not test the quota before recording the current callback's fit. -/
theorem quota_records (limit : Int) (fit : Fit Program) (found : List (Fit Program)) :
    (quotaAccept limit fit found).2 = fit :: found := rfl

/-- A late fit leaves the good-fit quota unchanged. -/
theorem quota_late (limit : Int) (fit : Fit Program) (found : List (Fit Program)) (late : comesLast fit = true) :
    (quotaAccept limit fit found).1 = decide ((found.filter (fun value => !comesLast value)).length < limit) := by
  simp only [quotaAccept, List.filter_cons, late, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- A nonpositive quota stops at its first delivered callback, after recording that fit. -/
theorem quota_nonpositive (limit : Int) (fit : Fit Program) (found : List (Fit Program)) (nonpositive : limit ≤ 0) :
    (quotaAccept limit fit found).1 = false := by
  simp only [quotaAccept, decide_eq_false_iff_not]
  omega

/-- Stable source partition puts both kinds of late fit after every other fit. -/
def prioritize (fits : List (Fit Program)) : List (Fit Program) :=
  fits.filter (fun fit => !comesLast fit) ++ fits.filter comesLast

/-- Good fits retain their exact original order under the source partition. -/
theorem prioritize_good (fits : List (Fit Program)) :
    (prioritize fits).filter (fun fit => !comesLast fit) = fits.filter (fun fit => !comesLast fit) := by
  simp [prioritize, List.filter_filter]

/-- Late fits retain their exact original order under the source partition. -/
theorem prioritize_late (fits : List (Fit Program)) :
    (prioritize fits).filter comesLast = fits.filter comesLast := by
  simp [prioritize, List.filter_filter]

/-- The final source result restores chronological order, partitions both flags, and applies take. -/
def finish (limit : Int) (found : List (Fit Program)) : List (Fit Program) :=
  (prioritize found.reverse).take limit.toNat

/-- Nonpositive source take returns no fit, independently of callbacks that have already run. -/
theorem finish_nonpositive (limit : Int) (found : List (Fit Program)) (nonpositive : limit ≤ 0) :
    finish limit found = [] := by
  simp only [finish, Int.toNat_eq_zero.mpr nonpositive, List.take_zero]

/-- The synthesis callback owns its reversed fit list; part checks do not change that private list. -/
def synthesize [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Bool) (limit : Int) (inputs : List (CheckedFit Program)) :
    List (Fit Program) × Result Program Normal (List (Fit Program)) :=
  let observed := run enabled required normalOf mentions (fun program found => (parts program, found))
    (quotaAccept limit) inputs (initial [])
  (finish limit observed.after.host, observed)

/-- Concrete synthesis counts each consumed checked fit exactly once as delivered or merged. -/
theorem synthesize_accounting [DecidableEq Normal] (enabled : Bool) (required : List Name)
    (normalOf : Program → Option Normal) (mentions : Normal → Name → Bool)
    (parts : Program → Bool) (limit : Int) (inputs : List (CheckedFit Program)) :
    let observed := (synthesize enabled required normalOf mentions parts limit inputs).2
    emissions observed.events + observed.after.merged + observed.remaining.length = inputs.length := by
  simpa only [synthesize, initial, Nat.zero_add] using
    run_accounting enabled required normalOf mentions (fun program found => (parts program, found))
      (quotaAccept limit) inputs (initial [])

end MicroCFTA.SourceGhcFitNormalForms
