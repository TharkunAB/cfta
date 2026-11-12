# Public raw synthesis type collision

The public raw API returns `f x` for a query with `f : a -> B` and
`x : TCons "var1" []`. Those two argument types are distinct. Their encoded
nodes are equal. The same-variable positive control returns `f x`. The different
rigid-variable and ordinary-constructor negative controls return no program.
Both literal raw-language acceptance and actual `solutionsOfSize` output agree.

The probe uses an empty library, explicit FirstOrder encoding and size 2.
Each case has a ten-second timeout. `expected.txt` records the full output.
A successful check reproduces the defect. No production Haskell repair is applied.
The parser route and the other encoding modes are outside this runtime claim.

Run from any directory under the established serial 4 GiB heavy-management cap:

```sh
python3 /path/to/mcfta/lean/restart-evidence/20261112-type-encoding-runtime/check.py
```

The check uses the project Nix/GMP environment. It verifies exact current source
hashes before and after the run. It builds only the generator library, checks
probe formatting, runs the probe and compares its full output. The snapshot pins
six owned Haskell files. `checked.json` records the effective cgroup limits.
There are no retained binaries or build archives in this packet.

The independent Lean packet `20261112-type-encoding-collision` proves raw type
inequality, encoded equality and failure of AliasSafe for the reserved constant.
That theorem alone does not establish runtime reachability. This packet supplies
the separate public Haskell execution. See root FINDINGS.md for repair requirements.
