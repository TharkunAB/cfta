# Stored reconstruction review

The first module has two public theorems. `execute` constructs a successful
repaired stored execution from initial `Ready`, source availability, and
available replacements. It retains `Keeps`, including the open-depth heap,
result availability, and the actual local Mu publication history.

`mu` reads an exact stored Mu. It derives body and ordinary-probe availability
from `Facts.cached`. It constructs the body call with the selected self name
and the ordinary-probe call with its selected ordinary name. Both calls use
the same available replacement. The second call starts at the first return.
The original stored record remains present. No caller supplies either return.

The replay module has one public theorem. An initial actual history from the
empty heap supplies the original writer after both calls. Literal repaired
source replay puts both completed calls at their common final heap. The
proof keeps publication history separate from growth and issued history.
The theorem does not compare the two reconstructed results.

The integration constructs a closed raw outer Mu containing an open nested
Mu. Its replacement is the available Depth reference. It derives initial
ready data from the actual source build. It constructs both reconstructions,
retains the writer from the empty heap, and proves both exact final replays.
It has no caller premises. This is one integration, counted once.

Final source hashes are pinned in the manifest. Selected validation is
strict4 and replay-strict1 (both empty), canonical2 and replay-canonical1,
public3 (three full signature/proof/axiom pairs), and kernels4 (one pair).
All eight requested printer settings are explicit. All selected checks use
only the standard axioms. Every job reports effective memory.max=4GiB,
memory.high=4GiB, and memory.swap.max=0.

Strict1/2 and kernels1/2 failed and remain intact. Strict3, canonical1,
public1/2, and kernels3 are successful earlier checks. The sole production
change after strict3 corrected the documentation to avoid an unsupported
negative equality claim. Its historical source remains at strict3.source.
The final source is byte-identical to strict4.source. The replay source is
byte-identical to replay-direct1.source.

The shared runner and worker are retained as inputs. The owned peaks file
is a byte-identical snapshot of the shared append-only peaks file at package
creation. The manifest does not freeze that shared append-only path.

This component proves completion and exact replay. It does not prove equality
of body and ordinary reconstructions, recursive row provenance, or a global
root-prefix event embedding.
