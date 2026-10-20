# Independent query optional-prefix review

Candidate: SourceCurrentNativeQueryOptionalPrefix.lean.
SHA256: 01216fbec107424e43905359d209cb7fa56e9a2fefb7f7d8be87883d09d3fc4e.
Result: no material issue found in the complete 198-line statement and proof.
This review adds zero Lean jobs and zero proof pairs. It reuses two public
readbacks in the author's one FULL group. FULL2 means two heads, not attempt 2.
The selected group is query-prefix-public-1.

## Node prefix

Trace inversion excludes a zero-step request-to-optional prefix and exposes
one actual yielded query step. The returned Inputs are those of THIS crossed
query at before. They are not Inputs of the final optional instruction.

The direct arm uses lookupNode_direct to recover the original request and
complete original native state. Source-key case analysis derives None; a
Some key cannot select the direct constructor. The compiler starts at the
same checked before, including its unchanged operations. The exact native
step and remaining Trace agree after code_bind_pure removes the identity
continuation. The compiler fuel is exactly original fuel minus one.

The memoized arm retains one handle, chosen, running, captured, compilerBefore,
and innerNext. The actual demand derives suspended/evaluating cells for the
SAME captured request at the SAME handle. Lookup and demand change no source
machine; their two literal equalities derive running.machine = before.machine.
The original operations stay in compilerBefore. No physical cache-validity
or captured = queried assertion is used or returned.

The exact first query step starts compileNode captured with its protected
finishNode continuation. bound_optional_cases extracts the unbound compiler
Trace at the SAME final after, pair, and body. Its equality keeps the FULL
siteNext function as innerNext bound to finishNode handle result (pure result).
It does not identify functions from one result or use bind injectivity.

The completed-compiler alternative cannot reach the selected optional. Its
actual suffix starts at finishNode followed by pure. Either no finish step
is crossed, which has the wrong constructor, or one actual finish yields
pure and no yielded prefix can reach optional from pure. Absent and busy
demand outcomes cannot match the given yielded query step. A ready hit also
yields pure, so it cannot reach the optional in this unbound request.

## Edge prefix

The same argument keeps the actual edge lookup/demand and full captured
edge request. It derives the SAME handle's suspended/evaluating cells and
unchanged machine, while preserving original operations in compilerBefore.
It starts the ACTUAL Control.edgeBody captured pure, not the older eager
compileEdge. The bound control's finishEdge continuation is precisely the
one emitted by checked step. The optional helper returns the unbound
edgeBody Trace and FULL composed finish function at the SAME after.
Ready, absent, busy, and completed finish/pure cases are excluded locally.
The exact fuel equation again accounts for one query step.

## Scope

The theorem is a physical prefix classifier. It does not recover an enclosing
Mu owner or assume one. The direct branch is retained as a valid alternative;
its stronger eventual exclusion needs the separate key-none branch argument.
Neither theorem equates captured with queried. That equality requires the
separate physical-cache validity producer at the exact query entry.
The evaluating cell is retained at running/ compilerBefore only. It is not
claimed still evaluating at final after. No final optional Inputs, site body
availability, History, generated writer, future completion, source ancestry,
semantic output law, or global termination follows from this result alone.

The selected direct3 source matches the candidate and its log has zero bytes.
The selected public1 source appends all eight options and the exact two
#check @, #print, and #print axioms commands to that candidate. The complete
23,005,797-byte log has both full statements and proofs, no omission marker,
and only propext, Classical.choice, and Quot.sound. Selected receipts retain
Lean 4.34.1, a five-minute cap, 4 GiB max/high, and zero swap. No new Lean run
was performed. Author-owned failed attempts remain in the author's package;
this review copies only the selected strict and full receipts.
