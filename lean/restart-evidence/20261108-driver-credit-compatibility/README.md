# Driver admission compatibility

The import graph contains 5,283 live modules. The changed source and its
reverse dependencies contain 625 modules. The three dependency roots are
Audit, SourceSizedGroupedSignedRank and SourceSizedSparseSignedCounts.
The checker builds each root in the project Nix shell. It verifies the exact
source snapshot before and after each build. It requires effective Linux
cgroup memory.max and memory.high of 4 GiB with swap disabled.

Run from the repository root in the existing serial heavy-management cap:

```sh
python3 lean/restart-evidence/20261108-driver-credit-compatibility/check.py
```

The project Audit also checks every imported MicroCFTA theorem against the
three standard axioms. Its actual R166 trace checked 86,708 theorems.
The own-source packets separately check all 111 public laws in the 39
changed proof modules, including the 42 new laws. The build and axiom counts
are verification scope. They do not prove native runtime correspondence or
end-to-end enumeration completion. No build tree or archive is retained.
