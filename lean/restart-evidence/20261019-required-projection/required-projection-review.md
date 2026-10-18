# Joint Required and projection origins

Frozen production: `SourceCurrentRequiredProjectionOrigins.lean`, SHA256 `ebf430e8c217d2f6083ea23447ae56df5f4ede03a67341d407e002eca2abdc67`.
The sole public head is `project_read`.

The theorem takes the existing inductive Required `Origin original prepared` relation.
The false primary node trace still names `original` at its historical gate heap.
The actual projection names `prepared` at its real entry heap.
The actual final row read names the supplied reader and its own returned heap.
The conclusion retains an ordinary source `Route`, full row symbol/guard/arity, and ordered child `Origin` pairs.
It does not require a false prepared gate, complete row equality, unchanged children, or bounds on rebuilt child mass.
The theorem needs the original semantic, normal, and availability facts; the projection entry semantic/cost/availability/guard facts; and final reader semantic/guard support plus exact `Keeps` from the projection return.
It needs no reader cost heap or growth from the historical gate return to the projection entry.
The historical gate proves structural path safety at its own heap.

The new joint step transports that safety through Required's row maps and signed ordered child selections.
A mutual origin induction preserves hereditary plainness where needed.
An actual projection/read induction then excludes recursive plain regions from nonplain output rows and retains ordinary rows through union normalization.
This is not a restatement of structural `Origin.nonplain`: it follows the actual projection and potentially unfolding final read.
The caller must still derive `Origin` from its literal Required call and connect the forest index.
The root-owned caller composition and fixture are outside this component.
Earlier class-edit phases and full renewal remain separate work.

Selected checks:

- `required-projection-direct-2`: exit 0; strict raw log is exactly zero bytes.
- `required-projection-canonical-1`: exit 0; target 1142/1142 builds. The log replays the unchanged `InternedFreshOrdinaryClosedCompletion.lean:24:5` unused-inputs warning.
- `required-projection-public-1`: one full signature/proof/axiom pair, all eight options, standard three axioms, no omissions. The shared `verify-probes.check_group` check passes.

Direct attempt 1 retains its recursor-binder and case-name errors. All four runs retain immutable sources where applicable, raw logs, metadata, and effective 4GiB max/high and zero-swap receipts.
The shared runner, worker, peaks, root fixtures, and root review files are not manifest pins.
