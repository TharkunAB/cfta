# Lexically independent nested construction

`InternedNestedDependencies` collects each expression's original de Bruijn
input slots. `build_congr`, `buildMany_congr`, and `buildEdges_congr` prove
equality of the full source execution when environments agree on those
slots. The result includes allocation effects and pending outcomes.
`independent_replay` combines this result with completed-record replay.

`InternedNestedSpecialization` uses the actual first body execution. Its
`Independent` condition requires every immediate nested binder to ignore
the enclosing local variable. It does not restrict ordinary variable uses.
`build_specializes` derives a finite ordinary constructor template from
that execution. It replaces each nested binder by the record that the
earlier execution completed. At any later valid state that retains the
earlier records, changing the enclosing local value executes exactly that
template. The theorem preserves both returned values and all cache effects.

`InternedIndependentCompletion.Staged` applies this condition recursively
to each binder body. `build_completes` proves first-run completion from
valid complete caches. The first depth body completes by induction on the
source expression. Its trace supplies the template for the ordinary probe
and the fresh callback. Thus the fresh callback executes only finite
ordinary work while its enclosing Mu record is pending. The proof assumes
no successful first execution, probe-key stability, or whole-callback law.

`closed_completes` and `closed_not_pending` start with empty caches.
`closed_complete_record` adds derived coherence, payload coverage, cached
provenance, edge residency, result availability, and exact later replay.
The examples use repeated ancestor symbols, nested local recursion, root
union self filtering, raw and smart binders, and empty-child removal.
Their declared variables satisfy `Scoped 0`.

This fragment complements the marked fragment. It permits repeated
ancestor symbols and root union bodies. The marked fragment permits nested
callbacks that retain an enclosing local variable. Neither fragment proves
first-run completion for every closed expression. In particular, a nested
binder can read an enclosing variable that normalization later removes;
lexical independence does not accept that case. The direct discarded-edge
replay theorems remain separate. A combined arbitrary nested completion
theorem remains open.

The model starts with prepared edge guards. It does not model public guard
validation before edge construction. No source implementation change is
required by these proofs.
