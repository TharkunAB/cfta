# Total physical tuple demand integration

The Audit target imports all nine new modules before its unchanged audit
commands. These commands reject every imported MicroCFTA theorem that uses
an axiom other than propext, Classical.choice or Quot.sound.

frontier.json records the ten affected source hashes in the current
5,292-module graph. Audit covers every affected reverse dependency.
The new modules also have separate strict own-source and public-name reports.

Reproduce from this checkout under the existing serial 4 GiB memory cap,
with memory.high=memory.max and no swap:

```sh
python3 lean/restart-evidence/20261108-total-tuple-demand-compatibility/check.py
```

The checker builds the actual project target in its Nix shell. It checks
the source hashes before and after the build. It reads the theorem count
from the Audit trace and prints a compact report. It does not write a
compiler archive or alter checked.json.

This checkpoint does not select the lazy sampler in the emptiness worker.
It does not prove native cost bounds or complete Haskell correspondence.
The earlier worker, driver and signed-rank contracts keep their own limits.
