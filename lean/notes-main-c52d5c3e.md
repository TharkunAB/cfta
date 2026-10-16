# Typed-language source refresh

Source main c52d5c3e adds the typing API. Merge 727fa870 retains the formalize history.
The source adds Data.CFTA.Gen.Typing and eight generator examples.
It changes no core constructor, equality, conjunction, or Sized algorithm.
All earlier Lean definitions remain unchanged except additive Audit imports.

Main 894a74af then merges the same recursive-field repair as local 2e25be03.
Merge 73475670 retains both histories. All generator files have identical
bytes before and after that merge. The earlier runtime checks still apply.

## Actual source construction

A goal is Root, an environment/type/remaining triple, or one fixed encoded
tree. Root inlines the rows of the distinct requested types in an empty
environment. Ordinary alternatives precede variable alternatives.
Variable alternatives visit each matching environment position in order.
Subterm prepends its binders and decreases remaining by one.
It is admitted only at a positive bound. Fixed fields keep a literal tree.
The visited map inserts each new row before prepending its ordered children.

Unknown constructor names fail before ordinary-rule field checks.
Ordinary rules are checked even when unreachable. Variable callbacks are
checked only at reached environment positions. A callback and each list
that the proof reads must terminate and be finite.

## Reproduced recursive-field defect and repair

The initial source accepted a fixed value in a field of the target datatype.
That field did not use the environment or remaining nesting bound.
The temporary reproduction uses Expr = Zero | Var Int Ty | Wrap Expr.

At bound zero, the rule Wrap [value (Var 99 I)] I produced:

    Right 1
    [Wrap (Var 99 I)]
    [Nothing]
    [1]
    [Right 0]

The independent environment lookup rejects that term. Its nesting is one.
A fixed Wrap (Wrap Zero) produced Wrap (Wrap (Wrap Zero)), with nesting
three at the same bound zero. Both terms had a successful local rank zero.
Rank round trips therefore did not establish the advertised typing domain.

Repair 2e25be03 rejects Value when the declared field type is the target
datatype. Recursive fields must use Subterm. Fixed values in other field
types remain available. The existing field-mismatch example now checks
both an ill-scoped fixed subtree and a closed fixed recursive subtree.
No new test case or package test suite was added.
Both original executable inputs now return FieldMismatch "Wrap".

The repair establishes a direct runtime-type exclusion. It does not prove
codec correctness, faithful index encoding in caller callbacks, or validity
of every nested fixed tree. Unsupported mutually recursive helper types
and arbitrary custom HasFTA instances still need explicit domain laws.

## Reproduced helper-order defect remains open

The same two-value language has different helper-constructor order:

    fromDatatype:    Right [Lit Z,Lit A]
    fromTypingRules: Right [Lit A,Lit Z]

Helper declares Z before A. Typing.positions records only constructors of
the root datatype. Other labels use position zero and then label text.
The fromDatatype order records positions in every reachable type row.
This contradicts the advertised shared declaration-order convention.
The local term/value inverse can still hold. Do not replace the rank-order
target with that weaker property. No ordering implementation was changed.

## Other source boundaries

Nonpositive remaining admits alternatives without Subterm fields.
Negative bounds therefore retain leaves. A literal nonnegative nesting
contract needs a nonnegative input domain or a specified clamping rule.
Several binders can be added by one field. The source environment-count
estimate assumes more than the general API enforces.

The proof models resolved labels and finite completed candidate rows.
Runtime TypeRep comparison, Ord/Eq laws, reached field-validation errors,
machine Int indexes, constructor labels, codecs, lazy import, and generator
rank transfer remain source adapters. Caller rules must encode the intended
object-language constructors and variable indexes faithfully.

## Validation

The strict Nix build covers all libraries, executables, tests, and benchmarks.
All six upstream suites pass: 763 examples plus golden.
After the repair, all 224 generator examples pass again.
The other five suites are reused because the repair changes only Typing.
Fourmolu checks all three changed Haskell files. Cabal-gild checks all four
active packages. Both executable counterexamples were run in the current
local package environment.

Evidence uses /tmp/mcfta-typing-main-c52d-*, /tmp/mcfta-typing-repair-*,
and /tmp/mcfta-typing-haskell-validation-20261016.json.
The two reproduction sources are marked external artifacts:
/tmp/mcfta-typing-self-value-repro-20261016.hs and
/tmp/mcfta-typing-helper-order-repro-20261016.hs.
Their source and before/after logs are retained in the closing snapshot.
The exact proof scope is in notes-typing-rules.md.
