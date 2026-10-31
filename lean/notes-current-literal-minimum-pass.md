# Current signed minimum pass and finite convergence

The full public system theorem remains open.
The new result is a total pass fixed-point producer in the finite source model.
It starts from the empty table.
It takes no finished table, iteration count, or future invariant as an input.

The checked source commits are `632cc92f303b7a1d1a0b35b0b05634d4591834da`
and `975d557b436a38c6ded6abba1668283056e87a5d` on `formalize`.
The complete sources have 417 lines.
The original source Map adapter and structural minimum semantics remain open.

## Full objective

Start from the original public inputs and configured policies.
Prove sound accepted outputs and the intended finite ordered prefix.
Derive sufficient resources from those original inputs.
Cover both recursive workers, the optimized interned core, and public adapters.
Retain constructor and equality constraints, size order, rank and unrank.
Retain exact node-count bounds and the configured size order.
Retain generic Mu, Union, and opaque source cases.
Prove Haskell and native correspondence at the stated interfaces.
A local forecast, height, cache, fixed point, or theorem total is not this result.

## Actual ordered signed pass

`SourceSizedMinimumPass.Table` maps each finite-model state to `Option Int`.
The source `Size` is `Integer`.
`transitionMinimum` reads all child sizes from the same known table.
A missing child lookup removes that transition from the available costs.
An available cost is one plus the sum of its child sizes.
Labels and guards do not change this cost.

`scan` uses a right fold over the supplied original state sequence.
It processes the suffix before the current state.
All rows for the current state read that suffix-updated table.
It selects the least available row cost, then inserts once with `min`.
It does not update the table between row costs.
An unavailable cost set leaves the table unchanged.

`pass_spec` proves unchanged lookup or a known result at a scanned state.
Any earlier known value is an upper bound for that new value.
`pass_known` proves support preservation and signed nonincrease.
These two laws permit arbitrary signed known values.
They do not claim positivity.
`pass_positive` preserves positivity when it holds in the current table.
`cold_pass` derives positivity for the actual pass from the empty table.
It does not accept a positivity or result witness from the caller.

## Total fixed-point producer

`SourceSizedMinimumConvergence.sameOn` compares actual values at the finite keys.
`sameOn_eq` uses `Input.complete` to derive full function equality.
The comparison does not use an oracle for equality of functions.

`compare_pass` proves actual equality or a strict signed lexicographic decrease.
The first component counts missing keys.
If that count does not decrease, the signed known-value sum decreases.
This signed order alone is not a well-founded order on arbitrary input tables.

The private `Working` type carries positivity for the current actual table.
The private `settle` function starts from an internally constructed empty table.
It preserves positivity by the actual `pass_positive` theorem.
It converts the nonnegative signed sum to Nat.
It recurses with the natural pair of missing keys and converted sum.
The actual failed comparison proves strict lexicographic decrease of this pair.
The iteration can increase the sum when it adds keys.
The first component decreases in that case.
No supplied bound or final result justifies the recursion.

`minimumSizes` exposes the computed table.
`minimum_spec` proves that this table is a pass fixed point.
It also proves positive values for all known entries.
Its public inputs are only the original finite `Input` and `DecidableEq Q`.
The result can contain unknown entries.
Unknown is not identified with an accepted term or an empty language.

## Source correspondence boundaries

`Input` has complete distinct states, original rows, and a root.
`Input.complete` covers every value of `Q`.
It has no Ord field or source Map scan-order equation.
The key-domain recoding and source Map representation still need a producer.
That producer must preserve child identities and the relative key scan order.
Extra empty-row scans need a no-op proof.
The checked right-fold equations do not supply that adapter.

A pass fixed point is not yet a structural minimum correctness theorem.
The next proof must connect each finite guard-erased derivation to a known bound.
An attained structural minimum also needs origin from finite derivations.
The source routine ignores guards.
A structural minimum would therefore give a lower bound for constrained terms.
It would not prove an attained minimum in the constrained accepted language.
The actual computed positive Int table still needs its Nat embedding and use
in the bounded product startup producer.

## Existing startup and recursive boundaries

The previous bounded product proof still derives the same actual root and heap.
It derives ordinary Node, height at most `bound.toNat + 1`, original guard Heap,
encode and lookup, startup Packet, initial Fits, canonical core and slot0.
Its minimum and filter parameters still need original source producers.
Startup Fits at a supplied width is not a sufficient global capacity theorem.

At each supplied finite recursive depth, paired resource/path theorems remain
available for native and prepared execution in their stated domains.
The finite carrier covers constraint, SCS and projected equality paths.
It does not bound term depth, work, fresh slots, allocation, or forecast size.
The main gap is a sufficient original bound on actual nested worker calls.
Maintain ordinary domain and height through actual slots, queries and children.
Cover terminal, alias and wakeup work and source contradictions.
Handle the sibling alternative tail by its structural list recursion.
A sibling restores the captured enumeration cache while threading native state.
A global cache-only monotone rank does not cover that restoration.
A pending profile is a proposal, not an established rank or admission condition.

Existing production callback completeness and Frame laws remain available.
The Native ordinary wrapper and the Prepared full fallback have distinct scopes.
A wrapper `None` is not a proof about an uninspected Haskell fallback.
No future Trace, run, Complete, output, rank or depth supplier closes this gap.
Accepted membership, coverage, configured order and the requested prefix remain
open at the public Haskell interfaces.

## Validation and retained evidence

Default and strict checks pass for both installed modules.
The complete Audit passes with 4,773 jobs and 83,303 theorem-dependency checks.
The public readback has 1,258 checks and 148 definition prints.
All seven new theorem reports use only `propext` and `Quot.sound`.
The prior 4,961,279 public bytes are an exact prefix of the current report.
The new tail has 125 lines and 8,549 bytes.
Its SHA256 is `f9718020f466a81fd3b7e0726aa9a8b252969eaa7d792e5d5afd392093c5cd35`.
All 572 prior protected sources retain their exact bytes.
Only the two new Audit imports change an old Lean source.
All 835 native source inputs retain their exact bytes.

Ten serial compiler commands produced nine passes and one repaired failure.
Every command used an effective 4 GiB memory limit and zero swap.
Strict checks used Lean 4.34.1, warnings as errors, and all linters.
The first failure and all source versions and repairs remain in the control area.
The final 23 input snapshots and complete raw reports remain available.
An older dependency replays its existing unused-variable warning in default Audit.
The two new strict module checks have zero output.

No Haskell source changed in this phase.
No Haskell or native execution ran.
No new Haskell defect or fix was established.
Keep any later Haskell fixes in `FINDINGS.md` for external work.
