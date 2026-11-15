# The actual forward induction case

Status: PARTIAL MAIN PROOF. The appended source proves only the forward entry
rules and their current resource facts. No resource theorem is accepted until
Root compiles the candidate. The entire task correctness theorem is OPEN.

The fixed internal resource conclusion must refer to:

    finish uv (IdentityActualSourceTask.run graph checkEmpty edgesOf
      recursiveDepth workFuel metadata uv task)

Its forecast is task.goal.forecast. Its local original caller is task.point.caller.
The outcome must satisfy IdentityEmittedCompleteResources at that caller and
forecast. The stronger joint conclusion must also produce current facts at
every actual entered prefix and retain all earlier outputs under later abort.
The original root initial hypotheses and genuine smaller-depth worker IH stay
in force. The latter always uses the SAME workFuel.

No arbitrary continuation appears in the task syntax. The only continuations
are the literal actual frames and their literal parent tails. Their mathematical
growth is identity_actual_frame_plan_ge. Growth is never inferred by unwrapping
an arbitrary function-valued tuple callback.

For the nonempty tuple case, split the SOURCE count bound as count+1. Current
input length forces this bound to be positive. The actual remaining list is
(incoming,bucket)::rest. The current tuple facts come from the original entry
or the actual earlier source prefix. They are not a future output assumption.
Use the appended forward theorem:

```lean
  obtain ⟨childOrigin, childCurrent, childSmaller⟩ :=
    identity_actual_source_cons_current graph checkEmpty edgesOf recursiveDepth workFuel
      metadata uv formulas solver root original scopeBefore allInputs point count
      incoming bucket rest origin current
```

The actual child program equals the original tuple program by
identity_actual_source_tuple_cons_run. Their mathematical forecasts are equal
by identity_actual_source_forward_forecasts. The child current predicate
contains the actual Packet/Fits/Heap/mass, full prefix ledger, captured
Shapes/Keeps, remaining input facts and node reservation. It contains no
future result certificate. childSmaller permits the genuine fixed source-task
IH to supply that child's resources and subsequent prefix facts.

In the ordinary subcase, the current genuine rank bounds the ordinary input
by h+1. Height0 is impossible. The actual ordinary branch has:

```lean
  ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true
```

Normalize the point's height to h+1. Then:

```lean
  obtain ⟨rowsOrigin, rowsCurrent, rowsSmaller⟩ :=
    identity_actual_source_ordinary_current graph checkEmpty edgesOf recursiveDepth workFuel
      metadata uv formulas solver root original scopeBefore allInputs point h
      incoming bucket rest origin ordinary current
```

This second call uses the CHILD origin/current state from the first step;
the names origin/current in the snippet mean those values after height
normalization. The runtime equation identity_actual_source_ordinary_run gives
the SAME guarded shared scan. The child and scan forecasts are definitionally
equal. rowsCurrent is produced by current-state padding and nodeReserved.2.
It does not assume correctness of an unexecuted row or callback. rowsSmaller
allows the same fixed source-task IH, with the unchanged workFuel.

At a later successful ordinary row, the actual selected frame stores the SAME
remaining count bound used in the child continuation. Its work is exactly
one plus that deferred bounded tail. identity_actual_source_selected_inner_work
proves that the corresponding inner tuple fits inside the scan work. Actual
own receipt, source membership, strict prepared-child rank and the scheduled
native row seed must still be generated before that case can be invoked.
The already checked selected-frame generation theorem and general row-entry
resource producer are the concrete operations for that next origin rule.

The main proof must now implement the fixed task correctness and source-prefix
resource induction. The current predicate is an induction entry/result, not
an external premise of the original worker theorem. It is not sufficient to
state a helper taking the desired smaller-task resources. In particular,
these producers remain OPEN:

1. Initial captured current facts, using original hypotheses and the actual
   completed earlier-row prefix IH at its exact returned native endpoint.
2. Every actual row prefix, including failed rows and the same captured cache.
3. Observed nested own entry and its new scope/full-list ledger.
4. Literal fallback completion and exact selected callback/tail entry/return.
5. Completed row restoration at the ORIGINAL next ordered row seed.
6. Every emitted output under later stop, including duplicate output offsets.
7. The complete worker and the common finite witness/history obligations.

The root origin retains the exact earlier-row output list rather than only a
set. Root's separate actual indexed output-origin producer can locate those
outputs in the same observed shared scan when it is available. It supplies
source provenance, not native resources. Its proof cannot replace any of the
current native resource producers above.
