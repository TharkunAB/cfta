# Shared literal ranges compatibility

The source DAG defines the full affected frontier from R199. The additive
Audit retains all existing imports. The checker verifies source hashes
before and after the build. It checks the Audit axiom report under the
serial 4 GiB cap.

Run from any directory under the same cap:

```sh
python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261109-shared-literal-ranges-compatibility/check.py
```

This check proves build compatibility. Component theorem contracts and the
remaining original-input, complete-enumeration, native and Haskell scope
remain in the sources and root handoff documents.
