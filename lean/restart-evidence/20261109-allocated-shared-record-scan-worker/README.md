# SourceCurrentAllocatedSharedRecordScanWorker

The versioned record scan retains literal source records and duplicates. Its path projection equals the versioned shared path scan on every outcome. The proof covers recursive selection and failure paths. Parent selection remains separate.

The own-source check treats warnings as errors. It checks every public theorem in its actual namespace. It records the source SHA-256 and each theorem axiom report. Only propext, Classical.choice and Quot.sound are allowed.

Reproduce from the repository root under the existing serial 4 GiB cap:

```sh
python3 lean/restart-evidence/20261109-allocated-shared-record-scan-worker/check.py
```

This component does not prove complete original-input enumeration, native capacity, runtime, both signed rank/unrank inverses or complete Haskell correspondence. The new versioned callers do not yet replace the Parent and Incoming selectors. No Haskell source changes in this packet.
