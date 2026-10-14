# Original physical input views and finite bounds

Proof checkpoint: `6d64cb4a`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Type.hs:freeVars`, original node, Mu, and union payloads,
and `Interned/Operations.hs:intersectOpen`.

## Exact physical view

`SourceRecursiveIntersectionInputView.payload` reads the actual issued-key
and payload maps. It checks both the requested constructor tag and the
canonical identity. An alias reservation cannot select an unrelated payload.
Missing or incompatible payloads have an empty default.

`payload_readback` derives the exact original record for every available
complete input. Rows retain actual symbols, executable guards, and ordered
children. Mu reads use the original stored body. Union reads use original
members. `copy_readback` retains complete original syntax without probe
metadata. The view does not replace actual constructor execution.

`free_readback` retains the actual cached interned free-name field.
`free_correct` derives every semantic free-name equation from coherent
physical records. No `FreeCorrect` premise is supplied.

`Original` states that original payload syntax contains only interned
references. It checks actual bodies and children, not stored probe metadata.
`Original.free_interned` derives this property for coherent cached free fields.
`closed_readback` then identifies semantic closedness with the actual source
test. `physical_step` derives physical branch agreement with the semantic
schedule. It supplies neither codec nor closedness equations as assumptions.
`Original` and availability remain explicit input premises. General source
construction has not yet been proved to supply `Original` for every result.
Unresolved placeholders retain the separate native bypass path.

## Copied free names

`SourceRecursiveIntersectionInputCopy.shape_free` derives exact interned
free-name membership for copied available records. `copy_free_all` extends
the result to every input of the total view, including empty defaults.
`copy_closed` derives `CopyClosed` without a supplied copy contract.
This is a free-name result. It does not establish the independent
`FiniteInput.copy_exact` language equation.

## Physical structural rank

`SourceRecursiveIntersectionInputRanks.weight` uses the size of the actual
tagged payload. It is a proof witness. It does not replace source execution.
`weight_readback` retains exact record size. `weight_le` handles placeholder
defaults. Original Mu bodies, row children, and union members strictly
decrease the rank. `localWeight` derives every local schedule decrease for
the total physical view.

These results do not assume numeric allocation order. Mu reservation can
precede body completion. Stored probe metadata can contribute to the size
witness. It does not become an original payload dependency.

## Finite original inventory and closed roots

`OriginalInput` retains an actual available original record and its complete
codec. `inventory` is a finite tagged carrier bounded by the actual issued
counter. It is a superset. It does not declare all constructor tags at one
identity valid or assign them different canonical representatives.

`inventory_available` derives membership for every complete available input.
`payload_reach_original` retains original syntax through actual containment.
`closed_reach_original` uses derived free-name scope to retain availability
through full reference unfolding from closed roots. No binder readback or
reference-availability contract is supplied for those reachable references.
`closed_reach_inventory` places all these inputs in the finite carrier.

`SourceRecursiveIntersectionInputBounds.closed_reach_below` places every
reachable input at the root rank or below it. `closed_pair_inventory` derives
the finite pair carrier for two closed original roots. These statements do
not assume an intersection result, a completed native trace, or memo provenance.

## Next obligations

Connect the actual canonical representative at each reachable identity to the
physical map. Establish the independent copied-language equation with
`InputDerivation`. `copy_closed` alone does not prove that equation.
The existing `FiniteInput` record includes this semantic premise even when
the termination argument uses only its structural fields. Do not discharge
that premise with an empty copy or a supplied equivalent language contract.

Use the concrete view, actual finite carrier, derived free equations, and
physical ranks to connect actual source requests to the semantic schedule.
Derive sufficient first-run native bounds. Retain original constructor and
domain effects, pending publication, busy observations, and explicit checked
word ranges. Completed native correspondence remains conditional on actual
completion. General open nested constructor completion and preparation of
new Mu bodies remain open.

Derive `ProductReadback.members` and `.rejected` from actual child/row traces
and canonical output readback. Then apply `product_exact`. Do not supply
equivalent product-row or product-language contracts.

## Validation at this checkpoint

All five new modules pass focused checks. The aggregate pinned Lean 4.34.1
build passes 1,257 jobs and 41,315 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-input-view-20261014-audit.log`.
No Haskell source changed. The prior Nix and formatter results remain the
source validation checkpoint. All 1,515 original manifest files remain.
Only the five previously intended audit and coverage files differ. All
marked drafts and the retained counterexample have their original bytes.
