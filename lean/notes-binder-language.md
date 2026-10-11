# Recursive binder language and cleanup

`BinderLanguage` interprets `Binding.Shape` as predicates on finite terms.
Each branch keeps its symbol, ordered child languages, and complete guard.
Each recursive binder denotes its least fixed point. Open references use an
explicit language environment.

`meaning_mono` proves that all syntax constructors are positive in free
references. `meaning_congr` proves that the interpretation depends only on
free names. `binder_unfold` derives the exact recursive language equation.
These facts do not assume that a binder body is productive.

`cleanup` follows the two cleanup cases in `Interned.Type.createMu`.
`cleanup_exact` proves that both cases preserve the complete language.
An unused binder has its body's language. A self-only binder has no term.

This semantic layer does not prove source identifier allocation, callback
parametricity, substitution freshness, or the SCC-based `fromFTA` schedule.
The source requires `createMu` callbacks to be parametric in reference names.
The least-language model is independent of the epsilon worklist model.
A full construction proof must relate the allocated binder graph to both.
