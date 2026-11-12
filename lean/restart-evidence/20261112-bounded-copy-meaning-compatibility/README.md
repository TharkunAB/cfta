# Native bounded-copy meaning and query-coherence compatibility

The frontier contains Audit. The import graph has 5,784 live modules and
4 affected modules. Audit directly imports 4,781 modules. Three new imports
precede the complete unchanged previous Audit source. No old proof is removed.

The checker pins the affected source hashes before and after the build.
It checks the full Audit frontier under the project Nix shell and the serial
4 GiB cap. `source-audit.md` states the current contracts and remaining work.
`portable-check.json` records independent reproduction of all five new packets
from /tmp. These component results do not complete the persistent goal.

```sh
python3 lean/restart-evidence/20261112-bounded-copy-meaning-compatibility/check.py
```
