# Actual prefix operations and remaining field plans

Status: UNCOMPILED. One public theorem. No compiler was run.
The frozen public header is byte-identical in the source module.

The theorem extends the actual PrefixInputs result. It keeps the literal
original control, raw control, captured continuation, before and after
states, original budget, used prefix length and source heap. It requires
only the original weak Physical validity, original input and field plans,
original operation validity, source heap growth and actual bounded Steps.
It adds no predicate, semantic state invariant or completion provider.

PrefixInputs supplies the same protected physical trace, reached weak
Physical validity, exact machine Extension and both remaining input plans.
The Extension's heap growth composes with the original source heap growth.

A separate induction on that same actual Steps derives operation validity,
complete operation Grows and the bound remaining field plan. Each yielded
step uses existing SourceEqualityNativeDemandOperations.step_operations
with its current FieldsThrough head. The proof composes actual constraint
allocation Steps and both memo-table extensions. No RequiredCache.Ready
premise is used.

The raw remaining field plan is derived by induction on its same remaining
budget with actual step_bind. Fields at a code control is True. Fields at
an edgeBody control checks the same literal request, so removing a captured
continuation does not change those current checks. Yielded steps recurse
at their exact returned control and state. Done, failure, constraint error
and blocked cases terminate that plan; no successor state or future success
is supplied for them.

The public result contains these ten conjunction fields in order:

1. The exact protected Trace of the supplied prefix.
2. Weak Physical validity at the same reached native state.
3. Original-to-reached machine Extension.
4. Source-to-reached heap Grows.
5. Operation validity at the same reached state.
6. Original-to-reached complete operation Grows.
7. Remaining InputsThrough for control.bind next.
8. Remaining InputsThrough for raw control.
9. Remaining FieldsThrough for control.bind next.
10. Remaining FieldsThrough for raw control.

Every remaining plan uses exactly budget-used. The theorem concerns the
actual supplied yielded prefix, including prefixes of partial executions.
It does not claim that a blocked or failed observation is a yielded step.
The existing all-outcome execute_operations theorem remains available for
an execution endpoint that includes its terminal non-yielded observation.
No successful continuation, whole worker provenance or semantic result is
inferred from this local receipt.

The original full coupled target header is copied byte for byte. No live
source, Haskell, compiler, Git, board or temporary files were changed.
