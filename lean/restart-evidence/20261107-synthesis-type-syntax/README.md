# SourceSynthesisTypeSyntax

The actual Lake target and own-source theorem report passed in shell.nix with Lean 4.34.1. All eleven public laws were checked with one worker and warnings as errors. checked.json records the exact source hash. Only propext and Quot.sound occur.

The port retains the actual Synthesis type, domain, defaulting, encoding, library, and query data. It computes rigid FirstOrder type nodes, the exact Fun alias, variable names, constructor discovery, and the default smart Mu type universe. Laws establish lexical scope, absence of binders in rigid types and the universe body, and top-only guard origins.

String represents source Text. Curried map entries retain input data; native map normalization and lookup are not implemented here. These are constructor-instruction laws. They do not establish native smart normalization, cache effects, lazy sharing, generalization, later intersections, or whole-caller termination.

Run from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-synthesis-type-syntax HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 350 python3 lean/restart-evidence/20261107-synthesis-type-syntax/check.py
```

The checker uses the existing build tree and removes its temporary report. No source or build archive is required.
