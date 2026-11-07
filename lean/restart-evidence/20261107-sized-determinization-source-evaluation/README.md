# SourceSizedDeterminizationSourceEvaluation

Run from the repository root. The check builds the actual Lake target. It checks the source with warnings as errors. It reports the axioms of each public theorem. It uses the project Nix shell and Lean toolchain.

```sh
XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-sized-determinization-source-evaluation/check.py
```

Run heavy checks serially. `checked.json` records the checked source hash and actual compiler result. The checker removes temporary reports. No copied source or build tree is required.
