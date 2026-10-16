# Initial finite ordinary keys validation

Validated at 2026-10-16 17:59 CEST.

Source: `SourceCurrentAllocatedFiniteOrdinaryKeys.lean`, 243 lines.
SHA256: `a874e8a86e08dae6b7404b78606b0e6077167a7161a180c3f3e73db4b9e7fd89`.

The final direct pinned Lean check passed with exit status 0 and no warnings (`keys-direct-3.log`).
The parent canonical build compiled this exact Keys source successfully in `keys-code-build-1.log`. That batch later failed in the separate WordCode draft. The repaired dependency batch `code-outer-build-2.log` passed with 1522 jobs. Only the historical unused `inputs` dependency warning remains.

The final imported public probe passed with exit status 0. It prints all 33 public axiom and full-signature pairs, including the mutual types and their six constructors (`keys-public-1.log`).
The final imported kernel probe passed with exit status 0 and no warnings (`keys-kernels-6.log`). It checks four independent integrations:

- Literal edge/node constructor effects build two nested ordinary nodes. Source construction derives the domain, Facts, and availability. The actual node counter equals 2, so `bits=1` exercises equality at the new inclusive supply bound. The theorem derives the complete empty-domain native key.
- Actual joined row membership and zipped child membership derive both edge and child key safety from the original recursive certificates.
- The last ordinary identity before the tag boundary is safe, and the first identity after the boundary repeats the first packed key.
- Reset to the empty domain and swapping operands retain complete key safety.

The final probes depend only on `propext`, `Classical.choice`, and `Quot.sound`. They contain no `sorryAx`, error, or warning. Earlier failed logs remain available as raw diagnostic history. The large intermediate kernel logs record an incomplete simplification; the final proof uses the standard `List.eraseDups_cons` equation and requires no unchecked evaluation axiom.

No older source or evidence file was changed. No Lake, Haskell, Git, or network command ran in this validation. Canonical builds ran under the parent agent. Temporary derived output is removed after imported checks.
