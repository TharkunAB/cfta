# Source review of the pre-repair candidate

Status: SOURCE_ONLY_PRE_REPAIR_UNCOMPILED_PROPOSAL. This is an author self-review.
I read all 220 candidate lines, the complete 73-line native source and the complete
96-line existing names model. I read the retained standard-library cuts at the
repository's v4.34.1 toolchain path. I did not run Lean, a native probe or a build.

The candidate derives a shape from independent syntax and observed name tests.
ValidName does not assume a desired generation result. ValidConstructor excludes
the three rejected constructor forms. The success proofs retain list order and
exact scalar arity. Unsupported scalarShape branches cannot be returned under
the constructor success condition. The newtype equation preserves its singleton.

The reification error precedes modeled checks. Unsupported declarations precede
all name checks. A nonempty datatype context precedes type-name and constructor
errors. The generated type-name check precedes constructor traversal. Each
constructor form is classified before its generated value-name check. Except
mapM retains the first constructor failure. This last fact is present in the
exact definitions; this candidate does not yet state a general first-error
characterization for an arbitrary earlier successful constructor prefix.

The existing checkNames theorem checks a character prefix. Appending Node
provides its concrete suffix witness. It does not prove that the generated name
is a valid GHC identifier. Type-name and value-name scopes remain distinct.

Root's retained controlled probes confirm a native defect: Constructor compiles,
but legal MagicHash constructor Constructor# passes the native uppercase test
and produces illegal Constructor#Node (GHC-55017). The report and both source/log
pairs are retained byte for byte. Their recorded source and raw hashes match.
This reviewer did not execute those probes. The candidate models this exact
pre-repair acceptance behavior. Its success result is a scalar-shape result,
not a theorem that GHC accepts the emitted declaration. Root will repair the
native guard. These source bytes must remain unchanged as the pre-repair draft.

The model projects TH syntax. It does not extract actual Q executions. Native
reification, lookup stability/effects, fresh child-name hygiene, nameBase and
Data.Char.isUpper remain explicit extraction boundaries. Scalar slots erase
field types, strictness and labels. The generated Generic derivation, default
NodeView methods and original HasFTA metadata are not yet linked to this shape.
No codec, language or rank theorem follows from this proposal alone.

I found no additional concrete source/proof error during static review. Lean
elaboration and all-linter acceptance remain unverified. There is no compiler
receipt or proof-success claim for this candidate. The native name defect and
the missing general constructor first-error theorem are explicit next steps.
