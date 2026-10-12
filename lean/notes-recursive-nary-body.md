# Typed n-ary recursive source bodies

`RecursiveNaryBody.lean` extends the typed single-knot body algebra to an
arbitrary finite ordered family of alternatives. Intermediate application
values can have different types. Each choice uses the original branch
number. A binary lowering does not add private binary choice wrappers.

The source correspondence is `Gen.Internal.Recursive.choiceRecursive` and
`choiceTerms`. Both functions use the complete alternative list. A singleton
retains `Choice 0`. `Gen.Internal.Flat.chooseLanguage` removes explicit
`EmptyGenerator` alternatives before it constructs this list. It rejects
an empty list. A branch with an empty current size class stays in the list
when the branch has members at another size.

The Lean syntax has a raw empty choice. Its language, counts, and sampling
mass are empty. This models the internal operation. It does not claim that
the public constructor accepts an empty generator. The kernel examples
check an empty choice, a singleton wrapper, and a recursive branch numbered
two after a branch that is empty at the current size but nonempty later.

The body module proves ordered value and term projection from a correlated
index. It proves equal class counts, decoder projection, guard metadata,
minimum metadata, and complete bounded rank coverage. The recursive
`paired_exact` theorem relates each shared value and term rank to the finite
derivations of the lowered source algebra. `alternatives_derives` identifies
these choice derivations with exactly one source child. No branch-size or
branch-count bound appears in these statements.

`RecursiveNaryMass.lean` proves the full value and term mass projections.
`RecursiveNaryRankMass.lean` also retains the sampled rank. Equal user values
do not conceal a change in the rank law. Both modules cover class records
and bounded size prefixes. Closed atomic sources retain their declared
finite distributions. Recursive alternatives and product splits use counts.

`RecursiveNarySource.lean` constructs independent value, term, and paired
records with flat source choices. It proves that every flat record has the
same ordered member list, value sampler, and complete ranked sampler as its
lowering. The proof uses `RecursiveChoiceAssociativity.lean`; it covers
zero-count branches and singleton choices. A coherent zero-count child has
no sampled runs. This fact justifies the singleton shortcut in the lowering.

The three knot theorems derive the full flat source record equations from
the accepted recursive guard. They include the private root in the term and
paired equations. They do not assume count, selector, or mass knot equations
as postconditions. Equal member lists also give decoder equality at every
valid and invalid rank.

`RecursiveFieldCombinators.lean` reuses the existing pay, application, and
label callback proofs through finite child fields. A finite field has a
finite class at each size. Its set of sizes can be unbounded.
`RecursiveFieldBounds.lean` and `RecursiveNaryFieldBounds.lean` restrict the
required child inverse laws to the height of the current requested forest.
The root induction supplies these local laws. It does not assume a complete
inverse law for the recursive knot.

`RecursiveNaryFields.lean` compiles the complete typed n-ary body into these
source fields. Its class tables agree with the independent term compiler.
`RecursiveNaryInverse.lean` supplies the recursive root counts and selector
from the actual value and term indexes. It proves that the requested forest
height gives enough recursion fuel. Every true checked row is a decoder
preimage. Every decoder preimage occurs with a true flag in all three views.

`RecursiveNaryCandidates.lean` proves bounds, order, and distinct positions
for all candidate rows. These results include false flags.
`RecursiveNaryCausality.lean` proves exact row-list equality for any two fuel
amounts that cover the requested height. It then derives the source callback
equation without a fuel parameter. The theorem preserves false flags and
original row order. A private recursive root consumes one level of the
requested forest. All body operations request forests no taller than their
input. A malformed root request returns no rows.

`RecursiveNaryQuery.lean` connects this source callback to the final replay
filter. It proves exact class and bounded global inverse results. The final
queries retain source order and have no duplicate positions. The rank range
uses the actual value-index class counts and their size-major prefixes.

`RecursiveNaryExamples.lean` checks complete private terms from branch two
in every view. It also records a necessary contract distinction. The body
`label N (choice [pure, occurrence, occurrence])` has two size-two members
with the same constructor term. A label removes the private choice wrappers.
Both source ranks remain valid, and the inverse returns both. Generator
member ranks therefore need not be a distinct-term quotient. The separate
`fromAutomaton` distinct-term path carries the one-rank-per-term contract.

A temporary Haskell comparison checked a three-branch public recursive
generator against an independent exact-rational recurrence. The branches
were a 9:1 atomic choice, a twice-paid leaf, and a binary recursive node.
The eight size classes had 132 members in total. The comparison checked
every bounded and unbounded value decoder, term decoder, and inverse rank.
It also checked class and bounded probability distributions and support
acceptance. The middle branch had empty early classes. This check passed
on `bbeb7be` with the local source repairs. It supplements the proofs; it
does not establish Haskell-to-Lean extraction.

The syntax has one recursive root. It does not model mutually recursive
heterogeneous runtime families. It also does not prove Haskell lazy
productivity, runtime container behavior, arbitrary callbacks, or extraction
from Haskell. Unequal recursive branch weights remain outside this accepted
count-weighted source slice. These boundaries do not weaken the stated
class, rank, guard, or probability theorems.
