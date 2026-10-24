# Generated scalar node views: incorporation and proof boundary

Updated: 2026-10-24. Main: `c4f7319acf84213fccc8ea389487d4176e4f0b62`.
Merge: `a7d667f628ee060501126efaf9d19bfe37ecfb72`.
Previous formalize: `6bc2c8c6a121adf73f489cfd1a59f267d18a54a7`.

## Incorporated functionality

PR #113 adds the optional cfta-th package. deriveNode reads a source datatype
and declares a scalar NodeView. Each source constructor keeps its position
and field count. Each field becomes the same fresh child parameter. Records
lose their selectors. Source parameters, field types and strictness annotations
are absent from the view. A source newtype also produces an ordinary data view.
The generated declaration derives Generic and has a default NodeView instance.

The producer accepts ordinary data and newtype declarations. It rejects
datatype contexts, existential or constrained constructors, GADTs, symbolic
names, synonyms, families and generated-name collisions. Generated names append
Node to the source base name. The type and value namespaces have separate
collision checks. Constructor checks run in source order. Reification, source
form, datatype context and generated type-name checks precede that traversal.
The actual source HasFTA instance and all existing field checks remain required.
Records of measures still need a suitable manual view.

The merge changes ten paths. Seven paths are new. The three existing paths are
README.md, cabal.project and .github/workflows/ci.yml. The core runtime,
generator implementation and all previous Lean sources remain byte-identical.
The optimized interned core and every earlier tracked proof, counterexample,
repair, marked draft and sealed evidence directory remain present.

## Current validation

The focused node-views suite passed inside nix-shell with GHC 9.14.1,
warnings as errors and one Cabal job. It ran four Hspec examples. Its test
module contains six successful derivation splices and five rejection checks.
The typed example compares all 38 terms, their ranks and generated rank/unrank
roundtrips with a manual view. The scalar refinement example compares value
lists and unrank results at indices zero through three. Its test title mentions
ranks, but its body does not call the refinement rank function. No stronger
refinement rank coverage is inferred from that title.

The shape example covers a parameterized record, a newtype, a named infix
constructor, constructor order, an empty datatype and record field order.
The rejection example checks a GADT, a constrained existential, a symbolic
datatype name, a synonym and a generated type-name collision. These checks
establish failure, not the exact diagnostic text. Other source branches remain
outside these finite examples. The upstream design note describes additional
historical validation. Those results are separate from this fresh four-example
run.

fourmolu, cabal-gild and cabal check passed for the new package. Three independent
source, test and formal-coverage reviews found no concrete new defect. No local
Haskell repair was needed. FINDINGS keeps the external repair index first.
All five listed repairs, including both LPO repairs, remain incorporated.

No Lean source or Audit import changes in this integration. The preceding
strict source checks and aggregate Audit apply to the same exact Lean bytes.
They were not repeated for the package addition. The preceding Audit passed
3675 jobs and 75838 dependency checks, with one older unused-variable warning.
This is retained validation evidence. It is not a proof of the new producer.

## Formal coverage and new obligations

SourceDeriveNodeViewNames proves the later positional prefix check and its
shape-before-name error order. SourceTypingFieldValidation and the typing-row
modules cover resolved fields and rows. Generic.Codec and DatatypeDecoder prove
decoding and rank laws under explicit codec and metadata premises. These results
can support a new frontend bridge. They do not already prove deriveNode.

The new bridge must establish the accepted declaration and exact error order,
then the emitted scalar metadata: constructor order, suffix names, arities and
Scalar fields. It must also establish valid-position buildNode/nodeFields laws.
At a valid constructor position and exact arity, building must consume children
in order and reading must return that position and those children as Just values.
An empty view has no valid position. Do not assert totality on arbitrary inputs.
Template Haskell reification, fresh names, name lookup, GHC Generic elaboration
and native character classification remain extraction boundaries.

Original HasFTA metadata and source encode/decode laws remain explicit. The
splice generates none of these laws. Corresponding manual and generated view
functions must also produce the same translated rules or invariant annotations.
Equal accepted languages imply equal counts and a reversible rank translation.
Unchanged numeric ranks require the same ordered enumeration and decoder.
Finite comparisons do not establish this for every datatype or every rule set.

## Strongest combined statement and next work

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined result. For a covered closed construction, a valid initial cache and
the original guard-allocation history, each requested finite number of modeled
node calls succeeds at sufficient mathematical width and fuel. The constructed
trace preserves exactly the formal finite-tree language with empty inherited
payload. It excludes withoutRedundantEdges and does not assert convergence,
fixed native resource bounds, or end-to-end Haskell and solver correspondence.

The latest callback result remains the concrete templateOracle frame, agreement,
fuel-retention and finite-transport theorem. Read notes-current-template-oracle.md.
The next callback target is recordTypes and typedTypes with their ordered node
observations. Complete canonical mutation histories, selected-current protection,
the cached driver, semantic pruning and phase 4 remain open. The new producer
adds the scalar-view frontend obligations above. H23 remains queued. The whole
formalization goal remains active and incomplete.

Evidence is in restart-evidence/20261024-generated-node-views. It retains the
exact upstream diff, fresh validation, independent reviews, baseline identities
and prior publication receipts. Its verifier checks every baseline blob and
mode. It permits only the exact upstream changes and nine status insertions.
This record precedes the evidence commit and authorized push to formalize.
