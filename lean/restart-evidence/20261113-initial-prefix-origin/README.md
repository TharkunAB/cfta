# Initial prefix source origin: restart packet

This packet stores source bytes and captured compiler evidence. It contains no build archive.
The proposed installation path is `lean/restart-evidence/20261113-initial-prefix-origin/`.
No compiler, live edit, Git operation, Haskell change, or board action was used to assemble this packet.

Run `python3 check.py` to reconstruct the exact stages. This command requires Python 3 and GNU patch.
It reads only packet files. It applies six ordered GNU unified diffs with zero fuzz and rejects offsets.
It verifies source hashes, exact compiler-input hashes, original frozen metadata, and captured checker results.
It does not run Lean, Nix, or Liquid Haskell. A fresh compiler run needs the original pinned repository and environment.
The original compiler runner is preserved under `checker/`; its historical paths remain unchanged.

## Exact source stages

| Raw stage | Lines | SHA256 | Recorded status |
| --- | ---: | --- | --- |
| `internal-227` | 227 | `10124a5cd299e318c68922d43d80356d3b4416cf743fe71c2c57f30e4cf49dfd` | uncompiled-internal |
| `failed-first-231` | 231 | `3f1c19c266e082d26102f64dd71327a200c8ff1dc4054ac0e3edf0fa521fe019` | strict-failed-check1 |
| `failed-repair-235` | 235 | `12056cb2eb907c9ad73dc08dd07370f6f9703399ecdb32a4c71b848c06677ecb` | strict-failed-check2 |
| `checked-final-235` | 235 | `8eba0fbcb07666c58a73cb0df08ef2bdaab1e6af959428fc234ba20dc790861c` | strict-pass-check3-private |

The internal 227-line draft was not compiled. Its provenance records the preflight changes that produced the 231-line handoff.
Check1 failed on that 231-line source. The 235-line focused repair failed at check2.
Root's final 235-line repair retained the actual `checkEq` receipt in all eight result branches.
Check3 passed on that exact repaired source. Its instrumented input is SHA256
`353eab06125ad7b83eef05fb14262462b58ec6214a2db2ff5727c7685059056b`.

One base and six patches reconstruct four raw stages and three exact strict inputs.
Every original checker script is byte-identical, so it is stored once. The manifest records all three original locations.
All three compiler reports, complete diagnostics, exact instrumentation patches, and original repair patches are retained.
The 150485-byte first failure log is preserved in full.
The final printed axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The actual compiler report records exit 0, memory.max=4 GiB, memory.high=4 GiB, and memory.swap.max=0.
These are recorded checks. The packet replay does not rerun them.

The approved 48-line header has SHA256 `4e9e9b8c55ab0c419a351e249bb84ed9e844868dc3db34f8aecc095ad1abc00a`.
The approved 14-line preamble has SHA256 `c2117e0be90a1701a17c019aecea74ca427e3e734b2a51dc95598de703d30a2e`.
Both remain byte-identical in all four raw source stages. The original 70-line plan and all source pins are retained.
Draft notes can say “uncompiled”; later compiler reports record the actual check outcomes.

## Checked scope and next unproved step

`initial_prefix_narrowed_rows` is one PRIVATE checked observer. No public law is added.
Its inputs include the successful current source expression, SAME completed native build and decoded root handle,
plus the actual prefix configuration, metadata, fuels, and query memos.
On the actual narrowed prefix branch, it retains the exact root read and false repeated-check receipts, compression Frame,
actual Action.prepare and OuterNarrow calls, reached caller, unchanged query memos, ordinary=None, and full source-row inclusion.
Other prefix outcomes retain True. The theorem does not assert that a narrowed branch occurs or that any output exists.

The next Entry/SelectedPreparation header and plan arrived before packet freeze and are stored under
`UNPROVED-entry-preparation-plan/`. Its 52-line header is SHA256
`9e1193a1b98dbdfc0a4bca7948b986738521d1f1d840a7748c9a7aa10656f868`.
Its 80-line plan is SHA256 `b20cc7127f8bfed408c893d55a562521691aff49c00e40e30402b40cc73f967f`.
The result header, preamble delta, original frozen metadata, and source pins are also preserved exactly.
This is UNPROVED planning material. It has no body and was not compiled.
Do not count it as a checked preparation or eager row-scan attachment.

The earlier primary/shared versus secondary/nonshared distinction still applies.
This observer follows the actual eager prefix. It does not invent the nonshared native Parent call used by the old ancestor observer.
The source family does not establish satisfying Type assignments, Program typing, output existence, later-sibling history,
or whole default synthesis completeness.

## Unchecked Liquid contract proposals

`UNCHECKED-liquid-contract-proposals/contracts.md` and `pins.json` are advisory material only.
No Liquid Haskell check was run. The pins identify the production source reviewed for those proposals.
They are not proof assumptions, checked contracts, Haskell fixes, or evidence that any proposed refinement holds.
The note keeps local constructor, narrowing, and CPS contracts separate from the missing joint completion claim.
It records no new Haskell defect. Repeated-name Liquid work remains externally owned.

`manifest.json` records exact source provenance. `replay-checked.json` records the source-only replay.
`SHA256SUMS` covers every packet file except itself.
