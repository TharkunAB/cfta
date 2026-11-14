# Unused source binder names in the selected Mu step

The ff09 repair elaborates with standard axioms. Its strict check rejects only
the unused public binder names accepted and built. This repair prefixes those
two binder names with underscores. Every premise type and proof-body byte
remains unchanged. This is alpha renaming of a new helper header. The original
full and coupled goal headers remain unchanged. No linter is disabled. No unused
proof is added. The old failed packets remain immutable. This new input is
UNCOMPILED until the root check passes. No Haskell behavior changes.
