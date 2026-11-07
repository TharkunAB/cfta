# SourceSynthesisUniverseMarkerIdentityInput

The source and all public theorem axioms pass the project Nix and Lake check.
The own-source report treats warnings as errors. `checked.json` records the
source hash and complete axiom list. The proof retains literal source cache
effects. This is a component proof. It does not prove full enumeration
termination, an original-input total-work bound, or native Haskell realization.

Reproduce from the repository root:

```sh
python3 lean/restart-evidence/20261107-universe-marker-identity-input/check.py
```

No production Haskell behavior changes in this packet.
