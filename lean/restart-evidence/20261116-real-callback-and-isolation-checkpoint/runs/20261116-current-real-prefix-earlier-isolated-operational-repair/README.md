Created: 2026-11-16 01:00 CET

# Earlier-isolation operational proof repair

Status: UNCOMPILED. The original 232-line input failed Root check 82589 and has no theorem credit. The original packet and diagnostic log remain unchanged.

The complete public header, preamble and probe are byte-exact copies of the first frozen packet. No premise, conclusion, worker operation or runtime fuel changed.

The repair addresses every diagnostic in `20261116-native-repaired-callback-isolation-and-small-check/earlier-isolation.txt`:

- Actual native handles are `entry.identity + 1`, as defined by `encodeNode`. The private helper now uses those exact encoded handles.
- Remove a command after a solved stopped goal. Remove only the redundant case equations reported by the strict unused-simp linter.
- Prove explicit stopped RESULT equations before rewriting the outer isolation predicate. This keeps the split at the actual getValue/checkRepeated scrutinee.
- In a non-singleton action branch, generalize the actual raw result first and inspect its List/Except/Unit constructors. The singleton success is contradicted by the existing negative observation. Every other constructor has no returned candidate.

The original all-fuel scope and checked/candidate endpoints remain intact. This is an operational proof repair. It introduces no semantic provider, linter change, compiler-budget change or Haskell fix. Root owns strict validation. No compiler was invoked here.
