# Shared Parent writers and actual read certificates

This packet checks the complete affected source import frontier. The new
source packets check every public theorem with warnings as errors.
The source hashes are fixed before and after the build. The Audit imports
all new modules and preserves every byte of the prior Audit.

Run the checker with the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-shared-writers-compatibility/check.py
```

The checker locates the repository from its own path. It also runs from
/tmp. The cap requires memory.max and memory.high of 4294967296 bytes
and memory.swap.max of zero. The Lean compiler uses one thread.

The actual shared Parent writer and its exact selected read certificates
are component results. Whole-prefix writer origins, strict owner rank
descent, original-input shared completion, full enumeration and native
Haskell correspondence remain open. No Haskell source changes occur.
