# Qualified typing do source review

Reviewed 2026-10-16 13:17 CEST. Incoming main is `5399d310` (PR63). The delta from `999c04a5` changes five generator paths. Three are Haskell files. `Typing.hs` changes only module documentation. The new exposed module is `Data.CFTA.Gen.Typing.Do`. No interned core, Sized, or GHC implementation path changes.

`Typing/Do.hs:64–77` defines the statement primitives directly. `each` is list identity. It preserves list order and repeated elements. `sub typ` returns one `subterm [] typ`. `under binds typ` returns one `subterm binds typ`. It preserves the binder order. The existing child/environment rules interpret the first binder at index zero.

`guard` at lines 79–81 is the list instance of `Control.Monad.guard`. True produces `[()]`; false produces `[]`. It removes the current combination and does not produce a typing error. `yields` at lines 83–85 wraps the existing `rule` in a singleton list. It does not add node-view or field validation.

The notation at lines 87–113 uses the ordinary list functions. Bind concatenates each continuation result in the order of the left list. Later choices can depend on earlier values. Independent choices produce the ordered Cartesian product, with earlier choices outside later choices. No operation deduplicates rules. `>>` repeats the right list for each left occurrence. `return` and `pure` produce singleton lists. `fmap` preserves position and multiplicity. `<*>` traverses functions first and arguments second. `join` concatenates the nested lists in order. These functions also support `ApplicativeDo`; this review does not prove compiler desugaring correspondence.

`fail` at lines 115–117 discards its String and returns the empty list. A failed refutable pattern removes that branch. It does not throw a typing error. Qualified do remains pure list construction; it does not execute a random choice or sample from the generator. Infinite input lists or divergent expressions can still prevent later combinations from being reached. The module adds no bound or termination mechanism.

The public documentation at lines 35–37 claims that the resulting explicit rule list gives the same automaton, counts, and ranks. This follows at the source interface when the expanded ordered rule list is the same. It does not assert a quotient by rule permutation. It also does not replace the existing node-view, field, bound, codec, metadata, or backend preconditions.

The new `TypingSpec` section has two regressions. The first compares generated values in order for the explicit and do-notation typed rules. The second tests dependent divisor choices and guard filtering against 35 expected fractions. The second sorts its output before comparison, so it does not independently test rule-list order. Neither test directly exercises refutable patterns or `ApplicativeDo`. The definitions remain simple list aliases, and this task adds no production tests or new Lean adapter theorem.

No concrete Haskell defect was found in this delta review. Full Haskell validation is recorded separately in `source-validation.md`. This is a source/interface review, not a complete typing-frontend or GHC/runtime correspondence theorem.
