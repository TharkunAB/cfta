# Composable language updates

Update a language value with a typed expression. Do not require the caller to
edit a stored file or rebuild a state row. Compose constructor and fact changes
with named exclusions, then apply the complete expression once:

```haskell
update before $
    define (at "Atom" "two") two []
        <> relax (at "Pair" "pair") "positive"
        <> without "zero-pair" (wholeTerm zeroPair)
```

Add `Data.CFTA.Language`. A `Language state` retains a checked source document
and a map of named exclusions. An `Update state` is an ordered sequence of
first-order operations. It supports `Semigroup` and `Monoid`, so callers can
name and combine reusable changes without host callbacks. A production
reference contains its source state and stable production name.

`define` installs a complete production with no facts. It replaces a production
with the same name in place or appends a new one. Use `require` after `define`
to supply facts. Use `require` or `relax` alone to change one existing fact.
`remove` removes the selected production. `editSource` exposes the checked
source edits for state-row changes. Source edits retain their order and validate
the final graph. The initial state remains fixed.

`without name exclusion` adds or replaces one named exclusion. `wholeTerm`
excludes that exact term only at the root. `subterm` excludes every term that
contains it. `AtRoot` and `Anywhere` also accept the existing templates with
holes and prefixes. Match complete symbols, including refinements. `restore`
requires an existing exclusion name and removes only that exclusion. It does
not restore a removed production or a relaxed fact.

`update` returns one checked result. Invalid source edits or missing exclusion
names leave the original value available. Updates are reusable expressions,
not patches prepared against a particular version. The existing document patch
API provides the latter check. Source edits and exclusions are independent;
resolve the ordered source edits first, then the ordered exclusion operations.

Compile the source facts, then apply the root exclusions and subtree exclusions
through `Template`. Keep the editable source unchanged. Generated transitions
are query data; copied annotations do not become source identities. Renumber
compiled states in their existing ascending order to give the result one simple
state type. The compiled graph retains constraints. Use a constraint-aware query
route to enumerate it. Editing invalidates prepared query indexes and cursors.

Store the language as `cfta-language` version 1 in the optional JSON package.
Store the complete source document and all named exclusion expressions. Reject
unknown fields, versions, tags, malformed operands, and duplicate keys. Do not
store a lowered graph in place of the source. A reader must be able to remove a
saved exclusion and recover the original source language. Query plans, cursors,
and serialized update requests remain separate work.

Provide a complete in-memory example and a save/reopen/update example. Verify
constructor and fact composition, false-fact restoration, root versus subtree
exclusion, recursive inputs, source retention after transition splitting,
multiple exclusions and selective restoration, complete refined symbols,
failed atomic updates, all template forms, malformed files, and fresh-process
rank replay. Compare bounded results with independently filtered source terms.
Measure compiled graph size and instruction/allocation cost. Run the normal
capped PR gates. Exact term addition and union, quoted update syntax, portable
constructor types, and query checkpoints remain separate items.
