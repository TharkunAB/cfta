# Independent optional-prefix helper review

Candidate: SourceCurrentNativeOptionalPrefix.lean.
SHA256: 4b8246104311ab09561b613a89a77955e98a97878091880848d8f8b3d8c2d175.
Result: no material issue found in the complete statement and proof.

bound_optional_cases applies the checked bind_prefix_cases to the SAME
actual Trace. Its unfinished arm keeps the unbound Trace and nonpure fact.
An edgeBody cannot bind to a code optional constructor. A code pure case
contradicts nonpure. Each other nonoptional constructor stays nonoptional
under bind. In the optional case, constructor inversion fixes the SAME pair,
body, and full function continuation. It does not use function injectivity.
The returned equality is siteNext = fun value => (innerNext value).bind next.
The completed arm is passed through unchanged, with the exact actual middle
state, fuel sum, returned value, and continuation Trace.

No initial semantic, cache-validity, owner, writer, future-completion, or
output-relation premise is introduced. The result alone does not identify
an enclosing compileMu owner. Its completed arm must still be handled by
the actual protected finish/pure or compiler branch analysis.

The selected strict1 log has zero bytes. The selected public1 snapshot
contains the complete source followed by all eight options and the exact
#check @, #print, and #print axioms commands. The existing log has the full
statement and proof, no omission marker, and only the standard three axioms.
Both existing receipts record Lean 4.34.1, max/high 4 GiB, zero swap and a
five-minute cap. This review reuses one public readback and adds no Lean job.
The supplied final candidate and installed official source match exactly.
