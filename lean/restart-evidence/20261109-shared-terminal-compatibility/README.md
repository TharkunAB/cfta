# Actual shared terminal compatibility

The checker builds the affected import frontier and the complete Audit.
It checks source hashes before and after every build. It requires the
existing serial 4 GiB memory limit, zero swap and one Lean thread.

Reproduce under that cap from any working directory:

```sh
python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261109-shared-terminal-compatibility/check.py
```

The affected frontier covers all changed modules. Old Audit bytes remain
unchanged after the added imports. This check does not prove complete
enumeration or complete native Haskell correspondence.
