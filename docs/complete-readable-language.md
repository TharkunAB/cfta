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

## Validation and cost

The fresh all-component `-O0 -Werror` build passes. Six rebuilt suite executables
are byte-identical to the passing base (798 examples plus the golden suite).
Focused checks cover all logical forms, exact graph/document/language values,
128 unusual-name/constraint cases, generic and explicit state codecs, all template
forms, malformed inputs, typed source errors, and edits after reopening. Two
fresh readers with different prior symbol interning reproduce the writer's terms,
counts, ranks and inverses. The complete language workflow matches the previous
implementation. UTF-8 also round-trips under `LC_ALL=C`, and malformed Unicode
escapes report their specific cause. Format, lint and package metadata pass.

The six rebuilt `-O2` core benchmark executables equal main. All eight standard
cells therefore retain their measured checksums and costs. No core query code
or existing benchmark changed.

| Workload | Format | Encoded bytes | Instructions | Allocated bytes |
| --- | --- | ---: | ---: | ---: |
| 10,000-state graph | Previous JSON | 1,437,836 | 6,137,964,915 | 1,719,841,536 |
| 10,000-state graph | Complete text | 297,795 | 688,285,874 | 238,896,040 |
| Same chain as an editable language | Previous text | 737,798 | 2,154,434,344 | 655,248,568 |
| Same chain as an editable language | Complete text | 617,798 | 1,065,608,795 | 356,649,568 |
| Refined pair language | Complete text | 283 | 1,365,875 | 384,504 |

The graph and chain cells include the same source construction, encoding,
decoding and exact value comparison. Complete text reduces the editable-language
round trip by 50.5% in instructions and 45.6% in allocation versus the previous
text implementation. It needs 16.3% fewer bytes. The small pair cell first loads
a text fixture; its setup differs from the previous JSON-based fixture load, so
its instruction/allocation numbers are not a direct comparison with that cell.
These are complete-process costs, not isolated parser or query costs.

All builds, probes and measurements run serially through heavy-management.
Process caps are 12 GiB and program RTS caps are 4 GiB. Measurements use
Cachegrind instructions and RTS allocation with GHC 9.14.1 at `-O2`.

Pending follow-ups include Liquid-style authoring notation and measures, named
pattern bindings, serialized update expressions, portable state/constructor
schemas, query checkpoints and the typed-language/Lean spike. The complete
format preserves the existing logic; it does not supply a new type checker.
