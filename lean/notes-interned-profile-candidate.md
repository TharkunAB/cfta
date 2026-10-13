# Actual recursive candidate profiles

`InternedProfileCandidate.candidate` composes the three recursive profile
results of a source miss. The depth call, ordinary call, and fresh-body
call each relate their actual normalized value to the pure interpretation
of the same body syntax and captured profiles.

The theorem derives the stored `InternedProfileHeap.Correct` invariant
and the returned raw or smart profile. It uses actual body availability,
the independently derived source normalization invariants, and freshness
of the allocated local among captured profile names.

The proof derives the callback form from the full body syntax. It compares
the actual smart cleanup result and the two-probe decoder with that form.
It does not assume callback key equality or a global body/probe law.
The recursive profile premises must come from the full executor induction.

The focused Lean build uses 197 jobs. The isolated audit checks 8,160
theorem dependencies in this module's import closure. Both checks pass
with the pinned Lean 4.34.1 toolchain.
