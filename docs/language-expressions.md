# Composable language updates

Update a language value with a typed expression. Do not require the caller to
edit a stored file or rebuild a state row. Compose constructor and fact changes
with named exclusions, then apply the complete expression once:

```haskell
update before $
    define twoRef twoSymbol []
        <> relax pairRef positive
        <> without zeroPairRule (wholeTerm zeroPair)
```

Add `Data.CFTA.Language`. A `Language state` retains a checked source document
and a map of named exclusions. An `Update state` is an ordered sequence of
first-order operations. It supports `Semigroup` and `Monoid`, so callers can
name and combine reusable changes without host callbacks. A production
reference contains its source state and stable production name. Use an ADT for
states. `ProductionName`, `FactName`, and `ExclusionName` are distinct identifier
types. Declare names once, then reuse typed references and bindings. Text stays
at declaration and codec boundaries. A fact identifier cannot select a production
or exclusion by mistake.

`define` sets the constructor symbol and child states at a named production.
It changes an existing production in place and retains its facts, or appends a
new production with no facts. Use `require` and `relax` to change facts explicitly.
Constructor edits cannot silently remove an existing obligation.
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

Store the complete source document and named exclusion expressions with
`printLanguage` and `parseLanguage` in `Data.CFTA.Serialization.Text`. The format
starts with `language 2;`. Reject unsupported versions, malformed operands and
duplicate identities. Do not store a lowered graph in place of editable source.
Query plans, cursors and serialized update requests remain separate work.

Provide a complete in-memory example and a save/reopen/update example. Verify
constructor and fact composition, false-fact restoration, root versus subtree
exclusion, recursive inputs, source retention after transition splitting,
multiple exclusions and selective restoration, complete refined symbols,
failed atomic updates, all template forms, malformed files, and fresh-process
rank replay. Compare bounded results with independently filtered source terms.
Measure compiled graph size and instruction/allocation cost. Run the normal
capped PR gates. Exact term addition and union, quoted update syntax, portable
constructor types, and query checkpoints remain separate items.

## Initial validation (before the text-format replacement)

The fresh all-component build passes at `-O0 -Werror`. All six suites pass,
with 798 examples and the hole-fit golden suite. Fourmolu, HLint, cabal-gild,
and package metadata checks pass. The complete example runs both in memory
and in separate save, query, restore, and query processes. Its count pairs are
`[2,3]`, `[2,2]`, and `[3,3]`.

Thirty ordinary and equality cases compare the compiled language through size
seven with direct filtering of source terms. These cover every template form,
root and subtree scope, overlapping patterns, combined scopes, recursive input,
complete refined symbols, and absence of duplicate retained terms. Selective
restoration retains other exclusions. Removing all exclusions restores the
exact source value and source term order. Invalid source or exclusion updates
return errors without changing the old value.

A separate solver-backed check retains liquid guards while applying root,
subtree, and prefix exclusions through size five. All source formula and guard
fixtures round-trip with every template form. Eighteen malformed language files
are rejected with the expected locations or source errors. The previous document
probe still passes after sharing its JSON encoder. A writer and two fresh readers
with different prior symbol interning reproduce the same ranks and rank inverses.

Production, fact, and exclusion identifiers have distinct types. The example
uses an ADT for states and reuses typed references. Three negative compilation
checks reject identifiers used in the wrong role. The example's saved and
restored JSON bytes remain identical after introducing the typed identifiers
and state ADT. The semantic, malformed-file, and fresh-process replay probes
still pass. All six suites, strict builds, and format checks pass again.

Constructor redefinition uses `Document.DefineTransition`. It retains every
existing fact while changing the symbol and children. A focused check confirms
that equality still rejects unequal children until explicit relaxation. A
solver-backed check also confirms that a redefined constructor retains its
liquid guard. Missing states and ambiguous production names remain errors.
The final six existing test executables are byte-identical to the passing runs;
focused expression checks exercise the new operations separately.

## Cost

All eight standard benchmark checksums match main `c0cc8a05`. The six
executables are byte-identical. After the final changes, rebuilding them gives
the same hashes. Instruction differences are below 0.11%, and allocation
differences are below 0.01%.

The 10,000-state graph JSON round trip remains 1,437,836 bytes. It takes
6,137,964,819 instructions and 1,719,841,536 allocated bytes, within 0.02% of
the preceding implementation. The 100-fact edit probe takes 8,489,931,307
instructions and 1,513,080,688 allocated bytes, within 0.01%.

The new filter probe starts with one recursive state and four transitions:
`a`, `b`, `f(s)`, and `p(s,s)`. It adds named whole-term exclusions for even
length unary chains and subtree exclusions for odd length chains under `p`.
It forces the complete compiled graph. It does not enumerate terms or use a
solver. The new interface retains its original source in every case.

| Exclusions | Compiled states | Transitions | Instructions | Allocated bytes |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 4 | 799,112 | 129,752 |
| 4 | 12 | 51 | 2,286,887 | 532,264 |
| 16 | 36 | 159 | 41,919,017 | 8,079,592 |

These cells show the cost of compilation, including state numbering. General
overlapping templates can cause exponential growth; these measurements do not
bound that case. All jobs run serially through heavy-management with 12 GiB
process caps and 4 GiB RTS caps. Measurements use GHC 9.14.1 at `-O2`.
