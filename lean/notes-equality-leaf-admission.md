# Physical admission and exact leaf cache readback

The generic finite row inventory includes a canonical literal `Bottom` row.
The source `mkEdge` removes that row. Thus a physical decoder cannot be
injective over every unrestricted abstract row set: a Bottom-only row set
and an empty row set both lower to EmptyNode. The progress theorem remains
valid, but its physical instance must account for constructor admission.

`EqualityLeafProjectionRows` restricts canonical rows to non-Bottom guards.
It proves that source conjunction preserves this restriction and filters
the generated finite inventory. The inventory remains complete for every
retained row and has at most `2 ^ originalAtomCount` entries.

The source also checks positive equality paths against edge arity.
`EqualityLeafProjectionAdmission` includes this check for nullary edges
with an empty stored equality field. An admitted guard is Top or has no
all-positive equality extraction. The actual staged `sourceEqualities`
operation then returns the stored empty field. The proof shows that
positive extraction depends only on outer atoms, so source conjunction
preserves admission. The restricted carrier retains associativity,
commutativity, and the individual-row self law.

These conditions concern source representation. They are not solver truth
conditions. For example, an admitted residual can be `Not Top` or an outer
conjunction containing Bottom and another non-positive atom. Such rows can
have empty logical meaning while remaining source constructor rows.

`EqualityLeafProjectionLeafCache` constructs every selected admitted row
through the actual separate edge and node caches. The edge key contains the
symbol, empty child-reference list, and complete pair of equality field and
guard. `completed_rows` derives resident nullary output records and their
exact keys after sequential edge construction. `build_read` proves that
canonical parent construction decodes to precisely the original row
predicate, including duplicate inventory occurrences.

`identity_iff` connects the physical whole-node identity test to equality of
the complete admitted leaf domain. Both completed builds must be present in
a common coherent cache. The forward direction uses complete resident
record uniqueness and exact decoding. The reverse direction uses actual
cache replay. No per-symbol self-intersection shortcut is introduced.

The temporary source probe `/tmp/mcfta-leaf-admission.hs` checks six admitted
canonical guards and all 36 pairwise conjunctions. It also checks literal
Bottom removal and rejection of a positive equality between absent nullary
children. The log is `/tmp/mcfta-leaf-admission.log`.

The physical intersection product and projection-union equations still need
composition with this leaf constructor. These modules establish admission,
exact decoding, and the whole-node identity branch. They do not establish
a state-independent pure constructor interface for all cache histories.
