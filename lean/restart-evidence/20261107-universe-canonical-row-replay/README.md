# SourceSynthesisUniverseCanonicalRowReplay

The actual project Nix and Lake check passes. The own-source report treats
warnings as errors and checks every public theorem. `checked.json` records
the source hash and all axioms. The source comments state each component
contract. This packet does not prove full enumeration termination, an
original-input total-work bound, or native Haskell realization.

Reproduce from the repository root:

```sh
python3 lean/restart-evidence/20261107-universe-canonical-row-replay/check.py
```

No production Haskell behavior changes in this packet.
