# Old returned edge profiles after equal-key entries

Status: FROZEN UNCOMPILED. Root must run the compiler. Static packet checks do not give proof credit.

The new theorem is `MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload.old_returned_edge_profiles_after_equal_key_entries`.
The first header was frozen before the proof. Its SHA-256 is `3d65b4488459429ca8aa942584e28332c12c82e2a9babc324e324bd954568dc9`.

## Contract

The theorem uses one actual old cold-source trace, one authentic original entry, and one returned edge cell. It uses one later full warm-query trace that starts at that exact old snapshot. Every ordered zipped input pair must have a closed qualification or a mixed qualification from that same later trace. These are the input qualifications of the existing `EdgeResult` law. The theorem does not derive these qualifications for all worker calls.

The result gives the old qualification for every input pair, a `Profile` for every child of the returned row, and retention of the exact edge cell at the actual later endpoint. It retains the original later trace and its supplied count bound.

## Proof route

1. Derive the old node and edge laws from the existing cold-source theorem. No returned-result law is supplied as a premise.
2. For each mixed input, extract its authentic entry from the same full later trace. Split that actual trace at its entry. The entry can occur anywhere within the supplied count.
3. Apply the existing warm equal-key identity theorem with the old start specialized to the original initial state. This identifies the complete old and new patterns and their domains.
4. Rebase each mixed qualification to the single supplied old entry. Keep its original operand, height bound, strict reference bound, and either operand order. Closed qualifications pass through unchanged.
5. Apply the old edge law to all rebased inputs. Use native memo retention on the same later trace to retain the exact returned row.

The original pattern can be any pattern admitted by `AuthenticEntry`. No `Profile` or only-U restriction is added for that pattern. Both real universe-entry orders and both mixed request orders remain in scope. The proof changes no runtime fuel, trace count, compiler limit, or linter setting.

## Premise classification

- Original source admission: accepted `firstOrderRaw`, original build, stored universe, machine validity and source growth.
- Old physical execution: original `InputsThrough`, `FieldsThrough`, operations validity, and the bounded actual cold trace.
- Old source event: one `AuthenticEntry` and one actual returned edge cell. The edge domain key equals the old entry key.
- Later execution: one full actual trace from the exact old snapshot and its original bound.
- Internal edge contract: all original ordered zipped requests are closed-qualified or mixed-qualified in that full later history.

No future row law, result law, model, alternate old entry, independent child history, or caller qualification producer is supplied. General warm semantic chronology, native inhabitance, class compatibility, and one finite accepted-root completion remain open.

## Layout and verification

`SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean` contains the exact 26,430-byte current owner followed by one newline and `APPEND.lean.txt`. The old owner SHA-256 is `35d8435e20a4273842887f966e52334c06ed2acfcc8966fb47ae1d9e07fca16a`. There are no new imports. Append `PROBES.lean.txt` only to the compiler check copy. It contains one public axiom probe.

`SOURCE-PINS.json` records all 6,250 non-Audit Source files and the three Lean package files. The normal Source and old packets were read only. No compiler, tests, Git, board, temporary cleanup, or active Work mutation was run.
