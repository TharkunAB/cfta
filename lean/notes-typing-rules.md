# Typed-rule semantics and finite row construction

The current source comparison is in notes-main-c52d5c3e.md.
This component proves the language of finite completed candidate rows.
It does not assert correctness of the whole Haskell fromTypingRules API.

## Independent rule-relative semantics

SourceTypingRules retains ordered ordinary rules and variable schemas.
Typed, FieldTyped, and FieldsTyped are independent inductive judgments.
They do not call the row compiler or its acceptance relation.
A variable rule needs an actual matching de Bruijn environment position.
Its field schema still comes from the caller. Object-language index fidelity
is not derived merely from the existence of that schema.

Subterm requires positive remaining nesting. It prepends all declared binders
in their original order and decreases remaining once. Fixed fields retain
the complete literal encoded tree. They do not consume typing nesting.
Root inlines the rows of deduplicated requested types in the empty environment.
The proof distinguishes this source policy from a bound on all encoded nodes.

The fixedAllowed predicate describes the independent fixed-tree domain.
LawfulFixed requires it for ordinary fixed fields and every variable schema
index/type. It is a sufficient global rule law. Successful reached-only source
validation does not establish that whole premise.
The permissive specialization uses fixedAllowed = True and needs no such law.
Do not infer object-language closedness or valid callback indexes from it.

SourceTypingRulesLanguage.accepts_denotes proves completed row acceptance
iff the independent judgment. Term induction handles positive Subterm
descent, literal Fixed equality, actual selected alternatives, matching
environment indexes, and root type membership after duplicate removal.
The typed and root endpoints retain the explicit LawfulFixed premise.
The fixed and permissive endpoints state the weaker unconditional results.

## Finite actual traversal

SourceTypingFinite derives a decreasing lexicographic rank.
A typed goal has primary rank remaining.toNat + 1. Fixed trees have primary
rank zero and secondary rank tree height. Root is above its inlined rows.
This permits an arbitrarily tall finite fixed tree below a typed goal.
No finite universe of types or environments is assumed.

The computed occurrence inventory follows every literal row child.
It includes duplicate occurrences. inventory_iff characterizes all reachable
goals by this finite list. Each state contributes one plus its child weights.
The sum of pending weights therefore decreases for both a visited skip and
a new row insertion followed by its ordered children.

close computes the actual finite visited-map traversal on candidate rows.
close_graph derives its Close receipt. close_complete derives a cold table
with the literal start row, exact rows for all entries, and child-key closure.
Warm-table results retain old reads and distinguish old rows from new rows.
The proof does not supply a complete map as an initial assumption.

The Language.close_denotes and close_root endpoints derive finite-map
acceptance from that actual close result. Their row correspondence and
child closure follow from close_complete. They are not compiler oracles.
close_permissive retains the explicit weaker fixed-tree interpretation.

## Repaired field predicate

SourceTypingFieldValidation uses the existing Child type.
Its fits definition follows the two source runtime field checks.
The encodedType argument is the runtime type of the encoded root constructor.
recursive_iff proves that a target-datatype field accepts exactly Subterm.
value_iff and fixed_root_other prove the exact fixed-root type exclusion.
foreign_subterm rejects Subterm at a different runtime field type.

A kernel example retains a nested external fixed tree that contains a target
subtree. The direct root-type check alone does not establish LawfulFixed.
The runtime metadata, supported type-family domain, codec laws, and caller
schema laws remain explicit obligations.

## Remaining work

Connect source name lookup, static checks, reached callback validation, first
errors, and constructor metadata to the completed candidate rows.
Connect native Map/nubOrd/Int storage, lazy import, labels, and value codecs.
Repair or otherwise resolve the observed helper declaration-order mismatch.
Do not claim the rank convention from a local term/value round trip.

The full-library targets remain unchanged. Continue the native equality-cache
field history and new conjunction memo/Scan adapter, general constrained
completion, runtime demand/publication, and every separate Sized contract.
Keep the optimized interned core and all older constructor/equality proofs.

## Validation

The pinned full audit passes 2,242 build jobs and 55,122 theorem dependency
checks. It permits only the three standard Lean foundations. The preexisting
unused-input warning remains. Forty-five public axiom probes, nine endpoint
signatures, and thirty kernel examples pass. These checks cover the four new
modules. Every earlier non-Audit Lean file retains identical bytes.

Evidence uses /tmp/mcfta-typing-*. The source and proof reviews record the
rule-relative scope and the stronger global fixed-field law. No whole-library
completion claim follows from this component result.
