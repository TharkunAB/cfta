# Declaration schema

This file specifies declaration headers and constructor fields only.
It is not a Lean module. It supplies no function or proof body.
Use context.lean.txt before these declarations.

```lean
/-- Retain the scan lists and the current comparison control. -/
inductive Control : Type 1 where
  /-- Start a cluster with the retained rows in reverse order. -/
  | cluster (candidates keptReversed : List Edge)
  /-- Compare the pivot with the remaining rows. -/
  | scan (pivot : Edge) (remaining incomparableReversed keptReversed : List Edge)
  /-- Retain the scan frame while one comparison advances. -/
  | comparison (pivot candidate : Edge)
      (tail incomparableReversed keptReversed : List Edge) (inner : PairControl)

/-- Retain the actual state in each scan outcome. -/
inductive Outcome (width : Nat) : Type 1 where
  /-- Retain the next control and the full comparison state. -/
  | yielded (control : Control) (state : PairState width)
  /-- Return the retained rows and the full comparison state. -/
  | done (values : List Edge) (state : PairState width)
  /-- Retain the native failure and the actual state. -/
  | failed (reason : SourceRecursiveIntersectionKernel.Failure) (state : PairState width)
  /-- Retain the constraint error and the actual state. -/
  | constraintError (message : String) (state : PairState width)
  /-- Retain the blockage, exact residual control and actual state. -/
  | blocked (reason : PairBlocked) (control : Control) (state : PairState width)

/-- Advance one scan phase or one existing comparison step. -/
noncomputable def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control) (state : PairState width) : Outcome width

/-- Run at most the supplied number of scan control steps. -/
noncomputable def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control → PairState width → Outcome width
```

Append the exact comparison_lift header from proposed-signature.lean.txt.
Close the namespace after the later authorized bodies.
All local notations expand to existing public type names. No private alias is introduced.
State, Control, Outcome and Blocked with the Pair prefix refer to the existing comparison API.
The new scan declares only its own Control and list-valued Outcome.

Use the transition specification in review-inputs/proposed-control.md without a change.
Test the candidate identity first. Test the pivot identity only when the first test fails.
Promotion resumes candidate :: (reverse incomparableReversed ++ tail).
The common result is used for the tests only. It never becomes a later operand.
Yield and blockage retain the exact inner residual and the complete outer frame.
Failure and constraint error retain the reason and actual state. They add no continuation.
Zero fuel yields the exact input control and state. Each successor advances one step.
A terminal comparison step resumes the scan with a yielded outcome.

The only proposed theorem is comparison_lift. Its branch expression stays inline.
Its observation is an actual completed comparison, not a completion callback.
The witness is a consumed positive prefix bounded by the supplied comparison fuel.
A supplied upper fuel bound can exceed that prefix. It must not replace the witness.
This first slice gives no genuine-packet cluster completion theorem.
