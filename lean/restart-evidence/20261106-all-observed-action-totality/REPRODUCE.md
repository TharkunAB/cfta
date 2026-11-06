# Every successful observed action state

The theorem is `MicroCFTA.SourceCurrentSelectedStepAllObservedTotal.complete`.
The source is `lean/MicroCFTA/SourceCurrentSelectedStepAllObservedTotal.lean`.
Its SHA256 is `2091d4b5c46e1300261d41fe78fea77f90fdc1389db2688f0e1df0b7aaa01488`.

The theorem keeps the existing eight caller gates, five local fuel witnesses and nine universal binders.
It proves total representatives for each successful action-list member.
The earlier theorem covers a singleton successful result.
Neither theorem proves that either complete worker terminates.
Neither theorem derives one common bound from the original inputs and requested size.

The normal temporary and repository checks both exited 0.
They used Lean 4.34.1, Nix, one Lean worker, warnings as errors and a serial 4 GiB memory limit with no swap.
All 8055 physical roles and two logical controls passed the temporary check.
All 8065 physical roles and two logical controls passed the repository check.
Each check includes a before pass, a distinct after pass and a separate final pass.
The complete report lists only propext, Classical.choice and Quot.sound.
It contains no sorryAx.
These observations do not establish strict kernel-control, full transitive or source/object correspondence.

Run this check from the repository on this host:

```sh
cd /home/tritlo/Code/mcfta/lean
env -u LEAN_SYSROOT /home/tritlo/.nix-profile/bin/nix-shell ../shell.nix --run 'exec /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -DwarningAsError=true MicroCFTA/SourceCurrentSelectedStepAllObservedTotal.lean'
```

To reproduce the type and axiom report, copy the module to a temporary Lean file.
Append these commands and check that file with the same command:

```lean
#check @MicroCFTA.SourceCurrentSelectedStepAllObservedTotal.complete
#print axioms MicroCFTA.SourceCurrentSelectedStepAllObservedTotal.complete
```

The small reports and metadata are historical observations.
Filesystem identities and timings are not reproducible source products.
No private primitive TYPE, opaque failed diagnostic, index or build tree is copied here.
The saved boundary records identify the missing compiled-type context and caller bindings.
No Haskell source changed and no new Haskell bug was established.
