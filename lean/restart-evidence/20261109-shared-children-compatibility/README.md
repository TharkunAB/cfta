# Actual shared children and zero-depth hook compatibility

The checker builds the affected import frontier and the complete Audit.
It checks all affected source hashes before and after every build. It
requires the serial 4 GiB memory limit, zero swap and one Lean thread.

Reproduce under that cap from any working directory:

```sh
python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261109-shared-children-compatibility/check.py
```

Old Audit bytes remain unchanged after the added imports. This check
does not prove positive-depth adequacy, complete source enumeration
or complete native Haskell correspondence.
