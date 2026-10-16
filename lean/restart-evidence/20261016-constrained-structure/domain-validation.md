# Finite ordinary input domain

Source frozen: 2026-10-16 16:09 CEST.
`SourceCurrentAllocatedFiniteOrdinaryDomain.lean`, 197 lines.
SHA256: `3baa598702654d271749988e85edfcbbeac0dcabe4b2580ce035c7e6395d937c`.

## Public domain and constructor laws

Node contains Empty and ordinary nodes. Rows and Children retain the
complete ordered edge and child payloads recursively. Edge is Children
of the edge's actual children. Mu, explicit union, and bare reference
records are excluded throughout. Symbols, guards, equality classes, and
cached depth/free metadata have no extra domain restriction.

The module derives row and child membership, a child's strict ordinary
height bound, and exact edge height as the maximum child height.
Raw makeEdge retains the domain and any supplied child-height bound.
Normalized makeNode retains the domain and a bound from its supplied
resident rows. OrdinaryUnion retains the domain and the maximum operand
height. The proofs follow actual edge/node cache readback, filtering,
canonical ordering, and returned payloads. No historical execution or
semantic callback is transferred.

makeEdge uses initial Coherent, Cached, and available children. makeNode
uses initial Coherent, Linked, and resident rows. OrdinaryUnion uses initial
Coherent, Linked, and resident operands. These representation premises
identify a warm result with its literal requested child payloads. No future
coherence, returned-domain, or completion premise is supplied.

## Checks

- Focused direct pinned Lean: domain-direct-2.log, exit 0, no warnings.
- Root canonical domain-build-1.log: exit 0, 172 jobs. Root explicitly
  confirmed terminal completion and no running canonical handle.
- Imported final domain-checks-3.log: exit 0, no warning, error, or sorryAx.
- 29 declared public axiom/full-signature pairs pass. This count includes
  the three inductive types, six constructors, Edge, and 19 theorems.
- Five external integration theorem pairs pass. They cover a literal
  nonempty source equality class with an arbitrary residual guard; the pure
  cached-free metadata boundary; actual makeEdge then makeNode at its
  returned heap; a constructed row bounded independently by each operand;
  and ordinary union closure, height, and exclusion of explicit union output.
- Reported axioms are standard foundations only. The domain predicates,
  constructors, and pure membership laws have no semantic assumption.

Earlier numbered logs retain external elaboration diagnostics. Only
`domain-checks-3.log` is the final accepted imported check.

## Boundaries

Pure Node does not imply that the cached free list is empty. The external
metadata fixture proves this distinction. Current coherence and residency
must justify metadata equations before a caller uses physical closedness.

The module does not prove that every actual native intersection returns a
domain value, nor that an arbitrary warm native cache has this property.
In particular, a nonempty seen list can select the literal repeated branch
and return a reference for ordinary operands. A later producer theorem must
retain its explicit empty-seen or full-empty-domain condition. Constructor
closure alone does not discharge that condition.

The domain permits nonempty effective equality classes. It does not prove
normalized field storage, arity admissibility, selected-path support,
constrained edit preservation, or general outer completion. Those are
separate current source obligations. No Haskell repair or defect is claimed.
