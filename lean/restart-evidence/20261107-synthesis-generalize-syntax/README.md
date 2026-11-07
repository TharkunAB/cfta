# SourceSynthesisGeneralizeSyntax

The actual Lake target and own-source theorem report passed in shell.nix with Lean 4.34.1. All 20 public laws were checked with one worker and warnings as errors. checked.json records the exact source hash and axioms. Only propext, Classical.choice and Quot.sound occur.

The port computes source variable-shape discovery, ordered occurrence paths, simultaneous replacement and the normalized root annotation. It recognizes variable-shaped constructor leaves as well as Ty variables. It keeps exact arrow child positions and does not traverse inserted type syntax. A closed input-derived reference normalizer computes eqGuard; eqGuard_eq_source identifies its payload with the checked source array-normalizer view. Native array-work realization remains separate.

These laws concern constructor instructions before native smart normalization. They do not establish complete native graph readback, cache effects, projection/intersection preservation or whole-search termination. The actual source can change the outer root after replacement; this boundary is retained.

Run from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-synthesis-generalize-syntax HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 350 python3 lean/restart-evidence/20261107-synthesis-generalize-syntax/check.py
```

The checker uses the existing build tree and removes its temporary report. No source or build archive is required.
