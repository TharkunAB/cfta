# Incoming source review: 8f85ddb6 to ccebf0f7

Read-only audit. No Haskell defect was verified, no source fix is proposed,
and no build or test was run by this reviewer. Root owns Nix validation.
The exact diff and commit list are preserved beside this note.

## Commits and scope

Local merge history identifies PR56 type-domains (ad0adef2), PR57 typing-inputs
(ccebf0f7), PR58 typing-lta (769f7189), and PR59 typing-binders (4d18ea91).
There are 20 changed files in cfta-generator and cfta-ghc: 961 insertions,
299 deletions. There is NO change under cfta/, including Interned, Equality,
Enumeration, and Sized. The completed core recursive-caller theorem remains
about unchanged source. No Lean file is part of the incoming source delta.

## Public type domains and GHC defaults (PR56)

Synthesis.hs:243–285 changes Curried to carry Map Text Domain. Domain is
HeadDomain Bool [Type] or TypeDomain [Type]. The Bool belongs to each head
domain. OnlyDefault no longer takes a key map. These are public source API
changes, not backward-compatible wrappers.

Synthesis.hs:489–537 computes domainNodes before replacing generalized
variables. It starts with references mapped to all types, then performs
ONE deeper step (domainDepth=1). A referenced key missing from an inner
iteration falls back to all types. This is a bounded overapproximation,
not the exact recursive domain fixed point. The source comments reject a
recursive Mu domain for performance. Generalization still ties repeated
variables by path equalities.

Synthesis.hs:557–586 adds ?any to every TypeDomain, regardless of defaulting.
The node of all types also carries it when any TypeDomain is present
(:795–796). Current narrowHeads checks ?any FIRST and retains exactly its
leaf occurrences. Only if absent does it use the old ? / ?nodefault / List
branches. Leaf tests require both the exact symbol and no children. Filtering
retains complete physical edge records, source order, and multiplicity.

A concrete changed law: on [?any leaf, Int leaf] the current filter returns
[?any leaf], even though no ? leaf is present. Historical
SourceCurriedDefaulting.narrow_no_open does not describe that current case.
Its old filter agrees with the source only when ?any is absent. This is a
Lean adapter gap, not a Haskell bug. The additive current adapter is now
kernel-checked; see frontend-defaulting-validation.md.

Fits.hs:326 makes optionTypeDomains True by default. CLI and plugin options
change from type-domains to no-type-domains; the benchmark environment
variable changes from HECTARE_GHC_TYPE_DOMAINS to HECTARE_GHC_NO_TYPE_DOMAINS.
The old spellings are not compatibility aliases. No-type-domains sets only
that flag; it does not force the curried encoding. Existing first-order mode
still bypasses the curried encoding.

Fits.hs:603–673 follows decided unary class restrictions in instance contexts.
For a constructor argument it adds a restriction only when lookupInstEnv
finds exactly one matching instance AND no possible unifier. It substitutes
the instance context, selects unary class predicates on that exact argument,
and retains only decided classes. Multiple matches/unifiers add no such
restriction. Referenced class-key domains are discovered in a seen-map
worklist, inserting each key before processing further references. Runtime
GHC instance selection, type erasure, key faithfulness, and conservative
pruning are not proved by this source inspection. Map combination at
:455–456 is left biased, with HeadDomain entries before TypeDomain entries.

The proposal trace and hole golden order change. GHC still checks proposals;
a domain marker is not evidence that a concrete type inhabits the domain.
For example, TypeDomain [] still contributes ?any. That prevents any theorem
that treats every unknown marker as a witness of a listed domain type.
It is not a confirmed source bug; final fit checking remains separate.

## Typed root inputs and binder bounds (PR57, PR59)

Typing.hs:154–199 makes inputs real root variables and implements Binders.
TypingError.NotImplemented is removed. Goal keeps Maybe remaining: Just for
Nesting, Nothing for Binders. Root inlines rows at Goal inputs typ remaining
(:240), preserving deduplicated root-type order. Inputs occur after the
innermost binders. Child binders prepend to env (:264), so input indices
increase under binders. Static Arg rules remain a distinct mechanism whose
indices do not move under binders.

For every Subterm, allowed requires remaining positive when present and
length binds + length env - length inputs <= binderLimit for Binders
(:255–265). Inputs do not consume the binder bound. Children without a
Subterm pass this test, including at negative bounds. Nesting decreases on
Subterm edges. Binders has no nesting decrease: recursion without additional
binders can cycle. The reachable state graph can still be finite with finite
rules, finite callback outputs, and bounded environments; its accepted term
language may be infinite. The generator then counts by size and requires
unambiguous runs. A finite graph is not a finite language or a fixed nesting
bound.

Error order remains exact: all unknown rule/schema names are checked first
(:215–216), then ALL ordinary Rule field shapes in rule order (:217), even
unreachable ones. The close traversal inserts each state before putting its
children before the pending tail (:233–238). Variable callbacks are checked
only for selected reachable env/type instances and after allowed filtering
(:242–263). Ordinary rules precede variable schemas; each schema scans env
positions in order. A failed later row is not converted into a valid partial
map. Haskell callback divergence remains outside finite total row proofs.

## Refinement generators on an automaton (PR58)

Derive.hs:476–502 exports deriveLTAOn/deriveLTAOnFrom. The outer From wrapper
first runs invariantAnnotations, including the node-view checks. Internal.hs
exports deriveLTAOnWith. It runs shared derivation validation before checking
the actual automaton (:325–330). Shared order is metadata reach/type limit,
unknown annotation names, missing atoms in type order, annotation arity and
measure checks, then unmeasured read fields (:372–436).

The automaton is TRIMMED first. A cycle in the trimmed graph is rejected
before a nontrivial constraint is rejected (:326–337). The latter reports the
first constructor name in ascending state-map order and transition order.
Unreachable or removed rows are not checked here. Only literal noConstraint
is accepted; a semantic tautology is not the stated test.

Acyclic rows use a lazy generator map over child states. Transition order
is retained; zero/one/many alternatives use empty/the sole generator/oneof.
Non-atomic transitions reuse the actual constructorGenerator and existing
contract/measure/named-measure path (:339–355,455–491). Atomic replacement
transitions enumerate their finite automaton terms and make a leaf for each.
The ranks follow these LTA generators, not fromConstructorAutomaton ranks.

Important atom semantics: atomInteger is decodeTerm followed by toLiteral
(:161–163). It is NOT membership in atomGenerator. Valid Int terms outside an
atom's enumerated generator can still have an integer. The automaton controls
which atomic terms occur in this new API. The explicit integerOf/decodeValue
error branches remain for malformed codec terms. There is no extra general
validation that arbitrary manually built Constructor automata match the
HasFTA grammar, arity, and field types. That codec/row domain must be explicit
in a correctness theorem. Do not report a missing atom-generator member as
a bug or silently claim arbitrary constructor automata are safe.

## Incoming tests and validation targets

TypingSpec adds input-environment recurrence counts through nesting 6,
well-typed distinct values at nesting 2, static-argument correspondence,
Binders size counts through size 12 for limits 0/1/2, input counts with a
binder limit, and typed distinct size-bounded values with binder-depth checks.
TypedArithmeticLanguage is shared fixture code added to the test component
module lists. It is not a new exposed generator library module.

TypedLanguageSpec adds measured and named-measure equality with filtered
well-typed languages at bound 2, a productive cyclic automaton error, and a
constrained If transition error. SynthesisSpec tests one typed run for each
of three programs with an undetermined TypeDomain variable. FitsSpec tests
rigid Ord rejection and nested-pair instance-context propagation. Hole golden
results change under default-on type domains.

Root validation should include strict all-component compilation, the changed
generator/refinement/GHC suites, the hole golden, Fourmolu, and cabal-gild.
Those checks are root-owned. No extra test source or broad duplicate build
was created here. The new tests do not establish generic GHC context pruning,
constructor-codec adequacy, cyclic generator rank completeness, or all error
precedences. No source repair or FINDINGS issue is justified by this review.
