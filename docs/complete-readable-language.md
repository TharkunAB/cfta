# One complete readable format

Replace the JSON codec with `Data.CFTA.Serialization.Text` for graphs, documents,
and languages. The parser builds typed values directly. Keep graph-reference,
arity, state-identity, production-name and fact-name validation. Retain cycles,
empty/dead rows, repeated alternatives, transition order, complete refinements,
separate facts and named exclusions. No solver runs while reading.

Use version 2 to distinguish the complete format from the earlier readable
prototype. There is no legacy decoder. Graphs use `graph 2;`, documents use
`document 2;`, and languages use `language 2;`. Each has `start STATE;` and state
blocks. Source transitions retain their names and facts. Graph transitions use
`SYMBOL(CHILDREN) where CONSTRAINT;`; omit `where` only for exact `noConstraint`.
Languages also retain `exclude NAME = root TEMPLATE;` or `anywhere` exclusions.

The laws are `parse (print value) == Right value` and stable canonical output.
Comments and whitespace are presentation. The state codec must preserve equality
and ordering. `StateCodec state` contains a typed encoder/decoder for state labels.
Default functions use derived `Show` and `Read`. `With` functions use an explicit
codec for portable labels or custom state types. The label is quoted when needed;
structured states need no second embedded data format. Names and string labels
support Unicode and escaped control characters. No Aeson instance is required.

Every formula has a readable form: true/false, and/or/not, all six comparisons,
forall/exists with named sorted bindings. Keep the concise `v == 0` form for the
exact distinguished-value comparison. Terms include integers, named variables,
applications, negation, all arithmetic constructors, conditionals and casts.
Sorts include integer, real, boolean and function sorts. Preserve raw constructor
structure: `negate(1)` differs from `-1`; `and()` differs from `true`.

Guards include true/false, same, entails, satisfies, holds, substitutions,
not/and/or. Substitution pairs retain actual path first, formal path second.
Constraints retain their equality field and guard separately. Keep `equal(...)`
for one equality class and `impossible` for equality contradiction with a top
guard. Use `constraint(CLASSES, GUARD)` for other combinations; CLASSES is a list
of path classes or `impossible`. Preserve empty/singleton classes, class order,
and invalid-but-stored paths. Reject child indexes outside machine Int bounds.

Update all three executable examples and CI to use explicit UTF-8 text IO and
one save/reopen workflow. Remove the public/internal JSON modules, direct Aeson,
attoparsec-aeson and vector dependencies, JSON-only example modes, and obsolete
format documentation. Keep the typed update API and source semantics unchanged.

Verify every old graph/document/language fixture through the new format, exact
state codecs, duplicate/error cases, all logical constructors, huge integers,
Unicode, source preservation, and independent-process ranks. Compare the complete
examples with the previous outputs. Run the standard capped build/format/test
checks; reuse measured tests/benchmarks only when rebuilt executables are identical.
Measure the new text path against the previous text and JSON baselines on the
same values. Record useful follow-ups as pending. The typed-language/Lean spike
remains pending; finish this format change, publish its PR, and stop.
