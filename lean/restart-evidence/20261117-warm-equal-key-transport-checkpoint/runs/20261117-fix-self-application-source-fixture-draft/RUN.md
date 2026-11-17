# Root-owned execution recipe

This recipe has NOT been executed. Use the existing capped serial runner. Run from /home/tritlo/Code/mcfta with the current normal package environment. Do not start a second compiler while another Root job is live.

The fixture imports only normal public cfta/cfta-generator modules. An existing Cabal package environment can run it with:

```sh
nix-shell --run 'cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261117-fix-self-application-source-fixture-draft/Probe.hs public 256'
```

Run `typed-reduced 256` and `typed-raw 256` in separate capped processes with the same command. Replace only the route. Root may compile once with the current pinned GHC/package environment and invoke that executable separately. These commands do not alter package source. Initial compilation, enumeration and external timeout must be reported separately.

The argument256 limits observed output occurrences. It does not change worker work, recursive depth, emptiness budget, source size or pruning. If the stream reaches this limit, absence is unobserved. A smaller cap can reveal presence; it cannot establish rejection.

Record the exact compiler/package versions and live source hashes with logs. Keep the whole typed pair for any matched candidate. Record module exit, external timeout and process signal. Do not treat a timeout or output limit as exhaustion.
