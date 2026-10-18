# Reader-relative observation foundation

Final production source: SourceCurrentReaderObservations.lean.
SHA-256: 69d39460b5bec5e0dbea7032d9e352b25a5e5ce085e4bd24b8ab866234315b5e.
Review time: 2026-10-18 10:58 CEST.

The module defines Related view first second. It requires physical Empty
agreement and Same depth view [first] [second] for every finite depth. The
view is one fixed heap. The relation does not quantify other heaps. Its
definition requires no view validity or execution premise. Actual clients
must supply the semantic support that their own execution needs.

Related.refl, Related.symm and Related.trans prove the equivalence laws at
that same view. of_uniform restricts the existing all-view relation to the
chosen view. It does not prove the reverse direction or reader transport.

makeNode takes two literal row lists, two actual constructor entry heaps,
Facts and resident Edges at those heaps. Bidirectional row occurrence
matching retains the complete symbol and full guard, with ordered immediate
children related at the chosen view. The constructor's actual physical
Empty tests agree because every paired immediate child has physical Empty
agreement. Thus the paired raw row survives exactly when its match does.
The fixed-view OpenObservationConstructors.makeNode theorem then supplies
all finite Same observations for the actual run(makeNode ...) results.
Source row order and multiplicity need not agree. Output identities and
canonical row positions are not equated.

makeUnion takes Normal and available member lists at the two actual entry
heaps, with ordered All2 Related view members. The actual makeUnion Empty
readback reduces physical emptiness to all-member emptiness. Its fixed-view
constructor theorem supplies Same for each finite depth. The conclusion
relates the two literal constructor result values. No future constructor
outcome or result relation is supplied as a premise.

Arbitrary nested Mu values can occur among the children or members. No
BinderFree, Cap, closedness, Original, or unused-local restriction is added.
Same can execute stored Mu unfolds at the supplied view. This module does
not prove that those unfolds complete, transport their origins to another
heap, or align a retained winner with another callback. Physical Empty
agreement is required for each immediate paired constructor child. Same
alone does not assert physical Empty agreement recursively.

The implementation reuses the exact actual constructor readback and
fixed-view observation laws. The small private list inductions adapt the
existing all-view survival proof. No old source or evidence file changed.
No binder, lexical binding, root-filter, publication, cross-reader, or
termination theorem is claimed. The earlier checked rootErase boundary
continues to prevent removing BinderFree from that source transformation.

Selected strict: reader-observations-direct-1. Its log is literally zero
bytes. Selected canonical: reader-observations-canonical-1. It terminates
zero, builds 563 jobs, and reports no warning. Selected full public group:
reader-observations-public-1, seven declaration/proof/axiom pairs. Every
public definition and theorem is covered, including Related itself. All
eight required options are present. The hardened checker rejects diagnostics,
proof printer failures, omitted terms, and nonstandard axioms. It passes.
Only propext, Classical.choice and Quot.sound are allowed in axiom reports.

Every execution records memory.max = memory.high = 4294967296 and
memory.swap.max = 0 under the five-minute capped runner and pinned Lean
4.34.1. All three first attempts pass. There are no failed attempts to
preserve. This component adds seven public pairs and no constructed pair.
The parent owns any subsequent integration or generalized lexical theorem.
