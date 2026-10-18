# Local weak simulation for open observations

Final source: SourceCurrentOpenWeakSimulation.lean.
SHA-256: 363b1f97c4e4d376c53049a12d8a1fad8c13a4a70a1103e26dc2c7968aaa03c1.
Review time: 2026-10-18 11:28 CEST.

The module imports the final counted epsilon paths from OpenOriginSteps.
It fixes one reader heap and a relation on complete physical values.
Forward requires three local laws for each related pair:

- A literal left reference has that reference origin on the right.
- Each physical left row has a complete right row origin. Its complete
  symbol and guard match. Children satisfy the relation in source order.
- Each immediate left epsilon successor is related to one value reached
  by any finite right epsilon path.

These premises do not supply all-depth observation equivalence. They are
local simulation obligations for the chosen value relation. The module
does not derive a simulation instance for source execution or Mu callbacks.
It assumes neither a desired output equation nor future completion.

Forward.path inducts on the actual left Path step count. Zero steps retain
the original right value. A successor step uses the local epsilon law and
composes its right reachability with the induction result. The right path
can be empty or longer than the left path. The theorem does not claim a
right step count or a bound on recursive worker execution.

Forward.reference extracts a counted path from the actual reference origin.
It transfers the path, applies the local literal-reference law at the
related endpoint, and composes the two right reaches. Forward.row extracts
a path to the actual physical source row. It transfers that path and uses
the endpoint's local physical-row law. Origin.from_seeds then returns the
matched row origin to the original right seed. Both retain the SAME reader.

same takes Forward for the relation and Forward for its flipped relation.
The depth-zero case transfers reference origins in both directions. At a
successor depth, complete row transfer supplies full fields and ordered
related children. The depth induction maps those children to Same. In the
reverse row direction, each child pair is flipped. The proof uses the
original induction hypothesis followed by Same.symm. It does not assume
that the value relation is symmetric.

related adds physical Empty agreement as an explicit premise and derives
ReaderObservations.Related. Epsilon observations alone do not supply that
physical test. The theorem therefore does not infer it from simulation.

No reader growth, cross-view rebasing, source syntax induction, publication
winner comparison, global source ancestry, or termination theorem is stated.
The epsilon Path count decreases inside its own finite derivation. It does
not decrease at every possible recursive worker call. A general used-Mu
proof still needs to derive these local laws for a concrete relation,
including actual filtered callbacks and older keep-first winners.

The dependency OpenOriginSteps retains strict front-step counts. Ordinary
rows occur at count zero. Union and Mu exposure remove one counted step.
Mu exposure derives the actual stored execution and its returned heap.
Its shorter origin tail remains at the ORIGINAL reader. These facts do
not imply availability of every generated value at that reader. The weak
simulation proof does not add or use such an availability implication.

Selected strict: open-weak-simulation-direct-1, literal zero-byte log.
Selected canonical: open-weak-simulation-canonical-1, terminal zero and
565 jobs with no warning. Selected full public group:
open-weak-simulation-public-1, six complete declaration/proof/axiom pairs.
Forward is printed as a definition. All other five heads are theorems.
Every probe has the eight required options. The hardened checker rejects
proof printer failures, omitted terms, diagnostics, sorryAx and axioms
outside propext, Classical.choice and Quot.sound. It passes all six pairs.

Every run uses pinned Lean 4.34.1, a five-minute cap, effective memory.max
and memory.high 4294967296, and memory.swap.max 0. Each effective limit is
read inside its worker. All three first attempts pass. There are no failed
attempts. No previous source or evidence was edited. This component adds
six public pairs and no constructed or auxiliary pair. The parent owns
integration coverage from separately checked actual source fixtures.
