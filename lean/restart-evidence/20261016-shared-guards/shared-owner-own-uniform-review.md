# Independent review of own-class and uniform parent envelopes

Date: 2026-10-16 23:14 CEST.

No material defect was found in the two frozen modules. This is a read-only review of all 343 source lines, the relevant precheck and numeric definitions, and the final constructed-prefix kernel. No source was changed. No build was run for this review.

## Own records from the initial raw vector

`SourceCurrentAllocatedFiniteOrdinaryGuardOwn.lean:63–92` first uses the actual successful own accessor with the initial Cached field proof. `own_verified` identifies the complete accessor payload with `sourceEqualities original`. `GuardEnvelope.effective` derives its occurrence and path-depth limits from the initial stored-field and raw-guard vector. Neither desired output bounds nor successful normalization are inputs to that envelope theorem.

The same actual live precheck at lines 80–86 supplies exactly the ordered own records. `SourceEqualityPrecheck.live_payload` states this equality. It does not return the normalized combination with inherited records. The proof uses the ordering permutation to retain the original own occurrence and depth bounds.

The class-count bound needs a positive path count for each class. It is derived from the well-formed physical own payload, not from the numeric occurrence bound alone. Member class length is bounded by the total raw path occurrences. `classSteps_eq` and `precheck_steps` then bound the complete step sum by twice the initial effective occurrence bound. Empty record lists cause no exception.

There is no inherited-size premise in these results. This is correct for the retained own class list. Inherited constraints can select contradiction and can make combined normalization expensive. These theorems do not bound that normalization work or the size of the combined inherited payload.

The receipt endpoints at lines 109–143 read `cached`, `ownRead`, and `exact` from the same allocated precheck receipt. They do not choose a second precheck return.

## Tail-first row envelope

`SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.lean:23–33` defines a common class row transformer and iterates it in the same tail-first order as the existing PassResources recurrence. The common transformer includes the original row bound in its maximum and then squares that maximum. This retains zero and positive row bounds.

The comparison at lines 50–61 distinguishes the whole Target zero-operand case from its nonempty additional-operand recurrence. It conservatively permits the full initial per-class path limit. It does not confuse that count with the exact target operand count. `pass_rows_exact` at lines 83–91 first bounds the actual tail result, then applies the head's monotone class transformer. The separate class-count monotonicity yields the initial-only parent envelope at lines 114–128.

`local_rows` at lines 131–150 unfolds the selector with the same actual precheck receipt. The unchanged and erased-child branches retain the original row bound. Only the live classes branch uses the own-record recurrence. `parent_rows` at lines 153–169 adds the literal raw rejection branch. That numeric theorem still takes a precheck receipt even though its raw rejection comparison ignores it. It is not an assertion that raw rejection executes precheck.

## Arity and sentinel

`pass_arity` at lines 101–106 bounds any number of class steps by `max arity 1`. `local_arity` at lines 174–184 checks every observed error or branch tag of the initial literal precheck selector. This is a bound on that numeric definition. It does not assert that an error is a completed local execution.

`parent_arity` at lines 187–196 includes both the original child-list count and the Empty sentinel ceiling. The explicit premise `count ≤ arity` is necessary for the stated `max arity 1` conclusion. The proof does not promise unchanged arity or an original-or-erased child shape for arbitrary constrained parents. The sentinel can have one Empty child.

## Constructed initial vector and prefix kernel

The final `own-constructed-prefix-kernel.lean` starts with an initially resident finite ordinary edge and legitimate current Ready, At, and inherited Ready. `GuardProfiles.edge_self` computes a vector from every raw nested guard. `Edge.guard` gives the bound for the original own constraint. The kernel then constructs the actual allocated prefix with `Precheck.resident_complete` before applying the row, class-step, and path-depth bounds. It takes neither a completed prefix nor a returned bound as an input. The inherited payload has readiness but no size bound.

The final logs contain 24 public axiom reports and one constructed-prefix report. Neither log contains a warning, error, sorryAx, or omitted marker. This review inspected those existing artifacts. It did not rerun them. The owner's canonical build reports 1579 jobs and terminal exit 0.

## Source and remaining scope

The source precheck order is `cfta/src/Data/CFTA/Equality/Operations.hs:206–213`. It tests own and inherited emptiness, tests combined contradiction, and selects the ordered original own classes. This supports inherited independence for the processed class list. It does not support inherited independence for combined normalization cost.

The raw constraint path bound remains the natural-index Lean model. These modules do not bound signed index magnitudes. They do not produce an actual local or parent result profile by themselves. They compare the existing deterministic row and arity envelope functions. Actual producers, cache certificates, cumulative resource recurrences, and initial headroom remain separate obligations. No outer execution or whole-root capacity Plan is constructed here. No new Haskell defect is reported.
