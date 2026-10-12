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

The completed binary-body inverse remains in `RecursiveCallbackAPI.lean`.
`RecursiveNaryChoice.lean` proves a local arbitrary-choice inverse from child
field contracts. These modules do not yet prove the inverse of this complete
n-ary recursive syntax. A direct binary callback translation is insufficient:
`LabelledView` removes private wrappers, and a flat source branch number does
not equal a nested binary path. A complete inverse requires a corresponding
n-ary callback interpreter and its forest-height termination proof.

The syntax has one recursive root. It does not model mutually recursive
heterogeneous runtime families. It also does not prove Haskell lazy
productivity, runtime container behavior, arbitrary callbacks, or extraction
from Haskell. Unequal recursive branch weights remain outside this accepted
count-weighted source slice. These boundaries do not weaken the stated
class, rank, guard, or probability theorems.
