# Finite-type probes through the source API

Four candidate Program ASTs match ordinary Haskell typing in three bounded
FirstOrder cases. Both untypable candidates are absent after stream exhaustion.
Both positive controls occur. These observations do not prove general typing or
finite-model existence. The published Lean proof remains the eager output and
partial-readback result recorded at `9318e653ebca99913f307a416b24aef0668a3678`.

| Case | Size | Candidate | Public result | Separate typed result |
| --- | --- | --- | --- | --- |
| BOUND | 3 | `sink (bound bound)` | Absent after exhaustion | Absent after exhaustion |
| SKI | 4 | `sink (s i i)` | Absent after exhaustion | Absent after exhaustion |
| SKI | 4 | `sink (s k k)` | Present | Present |
| POLY | 2 | `i i` at `Bool -> Bool` | Present | Present |

BOUND scans one public result and one typed result. SKI scans 451 public results
and 2551 typed results. Both streams exhaust in those cases. POLY finds its
candidate at the first result in each stream and stops. Its streams are not
claimed to exhaust. Counts refer to the observed streams, not distinct Programs.
The three case processes exit 0 without timeout. Their measured times are 0.02,
1.22 and 0.02 seconds. These are diagnostic times, not benchmark results.

The BOUND query supplies one rigid monomorphic `bound :: a -> b`. Library uses
are freshly polymorphic. Thus `i i` is a positive control. It is not the same
case as applying one query-bound monomorphic variable to itself. The SKI library
contains `sink :: a -> Bool` and the ordinary S, K and I types. Full inputs are
in the archived probe source and logs.

## Evidence and scope

[observations.json](observations.json) contains the exact four temporary Haskell
sources, six repository source hashes, compiler and runtime commands, process
results, complete candidate logs, and a separate source audit. The diagnostic
sources are text payloads. No test-suite or production Haskell file changes.
There is no compiled executable or large execution archive in this directory.

The probe evaluates exported `solutionsOfSize` once per case. It separately
evaluates the default typed route once per case. Its decoder matches the current
private `toProgram` definition. It does not join the two streams by position or
claim that they share one execution witness. For a typed match, it saves the
actual typed term and residual list from that run. Every saved encoding in these
runs is complete. The decoder does not run enumeration a second time.

GHC 9.14.1 checks the independent controls without importing CFTA. `Good.hs`
typechecks. `BadSKI.hs` fails with the expected finite-type incompatibility.
`BadBound.hs` fails with the expected rigid-type incompatibility. Both failures
are actual type errors, not missing-package or loader failures. Their logs and
exact sources are retained.

Every diagnostic reduced root has `reachesConstrainedMu = False`. The probe
leaves the actual checker flag and callbacks unchanged. These cases do not
exercise the flag-positive constrained-recursion path. They establish no
counterexample and no general satisfying-assignment theorem. Genuine partial
Type completions remain in scope.

The source audit records a reason to expect the raw FirstOrder restriction:
`firstOrderRaw_guards_plainMu` already proves that recursive binder bodies have
only Top guards. Ordinary ancestors may have equality guards. Preservation
through actual reduction, intersection and refolding remains UNPROVED. The audit
found no existing actual FirstOrder flag-positive example. Direct CFTA tests and
Curried examples are not substituted for that source-API requirement.

## Reproduction

Use the pinned repository source and its Nix environment. The observed main is
`e53852064d3ef5a2eafec47d754c27504b11de5f`. Check the six source hashes before a
comparison. The archive records the original command paths under `/tmp`.
Replace those paths with a new temporary directory when replaying commands.
Run each heavy operation serially through the existing 4 GiB max/high scope,
with swap 0. The runtime uses one capability and a 3 GiB RTS heap bound.

Extract the temporary source files with this small script from the repo root:

```sh
export probe_work=$(mktemp -d /tmp/mcfta-finite-type-probe.XXXXXX)
python3 - <<'PY'
from pathlib import Path
import hashlib, json, os
p = Path('lean/restart-evidence/20261113-source-finite-type-probes/observations.json')
evidence = json.loads(p.read_text())
for name, expected in evidence['source_hashes'].items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == expected
for name, source in evidence['diagnostic_sources'].items():
    data = source['text'].encode()
    assert hashlib.sha256(data).hexdigest() == source['sha256']
    (Path(os.environ['probe_work']) / name).write_bytes(data)
PY
```

The recorded successful compile selects package IDs from Cabal's actual plan.
This environment has two exposed `text` versions. A bare `-package=text` is
ambiguous. The successful package IDs are `cfta-0.1.0.0-inplace`,
`cfta-generator-0.1.0.0-inplace` and `text-2.1.3-2a27`. Use `-hide-all-packages`,
expose `base`, and expose those exact IDs. The archive retains the compile
arguments. Build the two current libraries first if their artifacts are absent.

The final executable uses the Nix glibc loader. Its first direct runs failed to
load `libz.so.1`. Selecting `/usr/bin/gcc` as the linker did not change that
loader. The successful runs set `LD_LIBRARY_PATH` on the child process only:

```text
/nix/store/6qi8skh85ci2k9gvl27nnh3kiy32qnsz-zlib-1.3.1/lib:/nix/store/k8bqvzzw3xll9sjkai15skrj7ab4f8gg-gmp-with-cxx-6.3.0/lib
```

Those paths contain the matching Nix zlib and gmp. On another store, resolve
these libraries from the same Nixpkgs environment as the executable's loader.
No system or project environment file was changed. The earlier compile and
loader failures are retained separately from the successful case results.

Run the executable with `BOUND`, `SKI` and `POLY` in separate processes. Each
recorded process uses `timeout --kill-after=3s 60s` and
`+RTS -N1 -M3072m -RTS`. The independent control commands use `-fno-code` and
`-fforce-recomp`. Their expected exit codes are 0, 1 and 1. Reproducing this
packet does not require the older `/tmp` directories.
