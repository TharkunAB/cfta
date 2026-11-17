# Terminal-step Returned bridge

Status: FROZEN CANDIDATE. UNCOMPILED. No theorem credit.

The public header was frozen before the proof body. The theorem takes both
existing Returned laws at the original checked state. It takes the literal
fact that this one step does not yield. It returns both laws at that step's
actual Outcome.state. It retains arbitrary Output, width, and both laws.
It has no fuel, source-profile, physical-validity, or finish-body supplier.

The proof uses all actual native code constructors. Node and edge lookup
can publish a suspended cell. Demand can change a cell to evaluating.
returned_lookup and returned_demand preserve arbitrary Returned laws in
both cases. The proof covers all four demand observations on the same
selected and demanded states, including absent and busy blocked outputs.
The complete native state of every checked edge-body outcome is unchanged
by body_native. This includes operation-cache updates, constraint errors,
missing-field blocks, arity sentinel, and successful child compilation.
Work, entry, reads, pure, fail, and both optional-binder observations retain
the two memo tables. Both finish instructions yield, so the terminal
premise excludes them at the original step and original state.

Use this bridge after observing a done, failed, constraintError, or blocked
step. In an execute induction, yielded branches use the existing actual
prefix Returned engine. A terminal branch uses this bridge at its same
last yielded-prefix state. Forward retention alone does not prove the law
for every returned cell in the terminal state.

## Source anchors

- SourceCurrentAllocatedNativeContextCache.lean:84 defines Returned.
- The same owner:92 and :118 proves lookup and demand preservation.
- SourceEqualityNativeDemand.lean:65 defines the checked edge body.
- The same owner:87 defines the literal step; :112 defines execute.
- SourceEqualityNativeDemandOperations.lean:20 proves body_native.
- SourceRecursiveIntersectionNative.lean:36 lists all code effects.
- SourceCurrentAllocatedNativeActualPrefixReturnedInduction.lean:26 and
  :41 gives the existing lookup/yielded-step proof pattern. This candidate
  mirrors only the small terminal structural part. It copies no engine.

## Check footprint and boundary

There are two ordinary imports, one public theorem, and one private lookup
helper. PROBES.lean.txt has one public axiom query. The optional separate
INTERNAL-PROBES.lean.txt has one private owning-module query. There are no
definitions, new runtime functions, limit overrides, suppressions, axioms,
or proof placeholders. Root alone compiles and installs this candidate.
This bridge does not establish any source semantic law or model witness.
The exact one-query f677 closure and arbitrary-query induction remain open.
