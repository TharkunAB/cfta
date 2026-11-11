# Finite training-oracle overflow

The reproduction uses the one-term language `a(a)`, size bound 2, and
log-weight `a = 400`. Each symbol weight is finite. The correct log-partition
is 800. The expected count of `a` is 2. The current automaton oracle returns
`Infinity`. Both expectation backends return `Infinity` and `NaN`.

`expected.txt` records the confirmed failure. A successful checker run means
that the failure was reproduced. It does not mean that the numerical contract
holds. `checked.json` makes this distinction explicit.

Run from the repository root in the existing serial 4 GiB job:

```sh
python3 lean/restart-evidence/20261111-training-oracle-overflow/check.py
```

The checker uses the project Nix environment with GMP. It checks formatting,
builds the library, and runs the source reproduction. It checks the affected
source hashes before and after execution. No binary archive is required.

Repair `Train.completionsOracle` and `Train.groupedOracle`. Compute stable
log-partitions and normalized expected counts. Preserve the generic exact
`expectedCounts` API. Propagate numerical failure through unchecked fitting
and mixture training. Validate shares and a nonempty component set before
conversion to `Rational` or normalization. Add regressions to the existing
`Prefix/TrainSpec.hs`, including finite log-weights `400` and `-400` and the
direct-child equality backend. Only the positive case was executed here.

A separate bound-1025 mixture probe timed out after 3 minutes, with exit 124.
It did not return a mixture. An empty mixture and downstream exceptions remain
source-derived concerns. They are not observations from this packet.
