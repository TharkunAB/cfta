# Generated scalar shape contract and name repair

Updated: 2026-10-24. Start: `2c8b42421d0f395141a00fdc172a4660acebd9ba`.
Main: `c4f7319acf84213fccc8ea389487d4176e4f0b62`, incorporated.
Haskell repair: `07229ca7f3208385a52c442965d8f2dcf73f7d99`.
Proof: `78f985d26b423108396cf8db36bc559eded73dfd`.

## Checked source model

SourceGeneratedNodeViewShape models the scalar-shape projection of deriveNode.
Its inputs retain the observed reified declaration, constructor forms and field
counts, source base names, character classification and separate type/value
lookup-presence maps. Native reification failures remain explicit string errors.
The descriptor is a projection of TH syntax, not a verified extraction of it.

ValidName states three independent input tests: an uppercase initial character,
no trailing hash, and no generated-name collision in the selected namespace.
ValidConstructor also requires a supported constructor form. Neither predicate
assumes that generation succeeds or that the desired shape is returned.

derive_data_success gives an exact success equivalence for an empty-context
data descriptor. The output has the suffixed type name and the complete ordered
map of constructor shapes. Each constructor keeps its suffix name and arity;
each field is a plain scalar slot. Named infix constructors have two slots.
The newtype equation gives the same checks on a singleton constructor list.
The empty constructor list remains empty. Unsupported constructor projections
cannot be returned under the independently checked validity conditions.

The model preserves validation order. Reification failure precedes all checks.
Unsupported declarations precede name checks. Datatype contexts precede the
type name, which precedes constructor traversal. Constructor form validation
precedes its value-name check. Both namespace checks test the first character,
then the trailing hash, then the suffixed-name lookup. Hash errors precede
collisions. A symbolic name keeps its earlier symbolic-name error.

constructors_first_error states a conditional first-error law. A valid earlier
prefix and one actual failing constructor force the complete traversal to return
that exact error, regardless of the later suffix. Earlier traversal success is
derived from independent validity. The theorem is not a converse that classifies
every possible error. Existing name-check results compose through the literal
Node suffix witness. This prefix theorem does not establish native lexical
validity or successful GHC declaration checking.

## Concrete Haskell repair

The original producer admitted legal MagicHash names ending in #. Appending
Node produced Constructor#Node or Hashy#Node. GHC rejected both generated names
with GHC-55017. An ordinary-name control compiled. The two new recover checks
in the existing rejection example returned False against the unchanged producer.
This establishes that the regression distinguishes the defect.

The repair adds one shared suffix check before either namespace lookup. It
uses Data.List.isSuffixOf from base and the existing unsupported-feature path.
Both source forms now report the intended manual-view diagnostic. The ordinary
control still compiles. The documented suffix naming rule remains unchanged.
The refusal lists and changelog identify this extra unsupported form. No core
runtime or generator algorithm changes. FINDINGS keeps the external repair
index first and records the exact upstream import action. The first five repairs
are already on main; this sixth repair is on formalize.

The focused suite passes all four Hspec examples and all seven recover checks.
The six successful derivation splices remain. All 38 typed terms retain their
tested values, ranks and roundtrips. The scalar refinement test still checks
values and unrank only. fourmolu, cabal-gild and cabal check pass. HLint passes
at the CI warning threshold. Its initial unfiltered run reported the existing
Amount newtype suggestion. That diagnostic remains; the fixture is unchanged.
Only the remaining checks were continued after that suggestion stopped the
first driver. No successful suite or formatter check was repeated.

## Remaining obligations

The proof concerns the observed declaration-to-shape algorithm. Native Q
reification, fresh-name effects, name lookup, nameBase, Unicode isUpper, field
counts and GHC elaboration remain extraction boundaries. ValidName is not a
complete lexer for arbitrary strings. The actual descriptor must come from a
legal source declaration. The model does not emit or verify the full TH AST.

Generic metadata, valid-position buildNode/nodeFields laws, original HasFTA
metadata and source codecs remain open. Corresponding view functions must
produce the same translated typing rules or invariant annotations. Equal
languages alone establish a rank translation, not unchanged numeric ranks.
This checkpoint adds no general codec, language, count or rank theorem.

The next callback work is the pure program/type-position helpers and recordTypes.
The retained source plan identifies a prerequisite for the complete typedTypes
callback: narrow and emptyAt exempt Mu alone, while partial rendering recognizes
a broader recursive boundary that also includes union. The current enumeration
graph combines these forms. A concrete node view must retain that distinction,
the actual nodeEdges closure and smart constructor behavior. Keep ascending raw
open-hole reads, both ancestry fields and actual compression on rejected results.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains strongest
combined. Its covered closed construction, valid initial cache, original guard
allocation history, empty inherited payload and sufficient mathematical width
and fuel yield finite repeated node calls with exact finite-tree language
equivalence. It excludes withoutRedundantEdges. Full canonical mutation histories,
selected-current protection, the cached driver, semantic pruning, phase 4,
resources, practical width, Haskell/solver correspondence and convergence remain
open. H23 remains queued. The full goal is active and incomplete.

## Validation and preservation

The final 298-line source passed pinned Lean 4.34.1 with warnings as errors and
all linters. The registered target built. Aggregate Audit passed 3676 jobs and
75963 dependency checks, with the older unused-variable warning at
InternedFreshOrdinaryClosedCompletion.lean:24 and no new-source warning.
All 27 public signatures and 13 axiom reports were read. Each report uses only
the standard propext, Classical.choice and Quot.sound axioms. No project axiom
or proof-limit override is added.

The frozen pre-repair draft, adapted failed strict input, complete failure log,
proof-only elaboration repairs, independent reviews and all native red/green
receipts remain retained. The failed check required public declaration docs,
precise Except reduction, a directed equality proof and rewriting the actual
first-error induction hypothesis. Executable definitions and public statements
did not change during that elaboration repair.

Evidence is in restart-evidence/20261024-derived-scalar-shape. Its verifier checks
every baseline blob and mode, the five exact Haskell/package changes, external
repair-index update, nine status insertions and single Audit import. Earlier
proofs, counterexamples, repairs, marked drafts and optimized interned code
remain. The preceding sealed evidence is unchanged. This note precedes the
evidence commit and authorized push to formalize.
