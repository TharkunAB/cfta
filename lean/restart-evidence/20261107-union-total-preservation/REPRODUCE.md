# Union termination and common fuel

Run from the repository root.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-union-total-check \
  HEAVY_PEAKS=/tmp/mcfta-union-total-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360 \
  python3 lean/restart-evidence/20261107-union-total-preservation/check.py
```

The checker builds the actual module and checks three source/axiom reports in
shell.nix. It removes the temporary report. No private Source copy or archived
build tree is needed. Compare the reported source hash with verification.json.

link_preserves_total transforms an existing finite parent-path witness. A query
that reaches the winner stops at its new root. A query that reaches the loser
continues directly to that root. Other parent frames retain their old entries.
No assumption that either input is a root or that the two inputs differ is used.

union_preserves_total composes termination preservation through both actual
findRoot calls and the actual selected link. It applies to every successful union.

union_bounded_uniformFuel uses bound + 1 for both searches when both query IDs
are below bound. It proves success and preserves storage support, parent bounds,
and Total. The retained invariants support successive searches under that cap.

These are internal forest laws. They do not compute the complete workers' cap
from the original inputs and requested size. They do not cover all intermediate
failing prefixes, total branch work, exact worker results, or Haskell execution.

No Haskell code changed and no Haskell fix was established. No Original Source,
TYPE, or compiler-interface view occurred. All receipt histories and quotas stay
unchanged. Historical SourceProcessFAIL and Root Original-Source upperUNKNOWN
remain permanent. The new mathematical proof does not recover that old audit.
