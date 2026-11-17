Status: FROZEN UNCOMPILED. Original93d and previous9575 headers, raw packets and failed logs remain immutable.

The fully pinned constructor still expects a mode match generalized over output
and preparation. The supplied original mode match is generalized over
completedCaller and preparation. The matches ignore the extra generalized field,
but do not normalize at an abstract Value. This repair converts only each
constructor mode argument with `by cases value <;> exact mode`. Both matches then
reduce at the same literal Value constructor. All existing constructor fields
remain explicit. No new mode assumption, resource, witness or semantic law is
introduced. Every original binder and premise is byte-exact.

The repaired header is not byte-exact: its constructor mode proof is normalized.
The same original preparation, mode property, opaque receipt, false callback,
suffix, output and index remain. The proof changes only the final constructor's
mode argument. All resource/held derivation code is exact from769647d1.
Shared5e48 and full public9374 remain exact. Default checking limits, runtime
fuels, budgets and linter settings do not change. No compiler or Source edits.
