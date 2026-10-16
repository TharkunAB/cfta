# Local annotated native binding scope

Checked at 2026-10-17T01:29:19.927210+02:00. Production SHA256 is
`65f246aeebbfbbbe14753031079562ba03da84183d7dd03f713c3cd1b0bc65b2`.

`Bindings` retains an available source Mu, its exact reference identity, and its
local hereditary annotation for every bound domain name. An annotation of a
reference alone supplies no such payload. `extend` retains old witnesses and
adds only actual left-before-right Mu binding entries. `enter` uses the exact
allocated Environment.enter key. It requires the current domain cache's normal
validity invariant, not a completed query or future scope law.

`read` uses current Facts, actual heap growth, and issued-map extension to recover
the same complete source Mu. It returns the literal current read, source and
current availability, exact Mu reference, and original annotation. It uses no
annotation property for unrelated resident records. Body projection ignores Mu
probe annotations. Ordinary rows and actual zipped children project their own
annotations without an arity premise. No extra scope record type was introduced.

Validation:

- `native-scope-direct-3.log`: direct production check with all linters, exit 0,
  no diagnostics. Earlier failed drafts and raw logs remain unchanged.
- `native-scope-canonical.log`: canonical build, exit 0, 1002 jobs. Its only
  warning is the historical unused-variable warning in a dependency.
- `native-scope-public-1.log`: nine imported public axiom/full-signature pairs,
  exit 0, no warnings, errors, sorryAx, or truncation.
- `native-scope-kernels-2.log`: two imported integration pairs, exit 0, no
  warnings, errors, sorryAx, or truncation. Proofs, universes, and deep terms
  are explicit. The output budget is 10000000 steps.

The first kernel follows actual domain entry, then an arbitrary legitimate grown
heap. It identifies the read value with the exact encountered binding payload.
It derives current availability and the stored body's annotation. The second
starts with two actual available Mu operands and only their body annotations.
It derives both literal current Mu reads after entry. Their two probe records
remain unrestricted. The first kernel draft used an ambiguous bindings name;
the matching failed source and raw log are retained.

This component proves local source binding scope. It does not prove the native
recursive compiler's annotation certificate, complete query preservation,
termination, machine word admission, or runtime correspondence. Those components
must consume these actual local bindings and preserve their own physical facts.
