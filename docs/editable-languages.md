# Editable languages

`Data.CFTA.Document` and `Data.CFTA.Language` keep a language in a form that
you can edit. A query needs a compiled graph. An edit needs the names of the
source productions and their separate facts. The two modules keep the source,
and compile a new graph after each change.

## Source documents

A `Document state` is an FTA whose transitions carry an `Annotation`:

- `annotationName`: the name of the production. The name is unique in its state.
- `annotationFacts`: the named constraints of the production.

`mkDocument` checks the graph structure. It also rejects a duplicate state row
and a duplicate production name in a row. `fromGraph` imports a plain graph. It
names the productions `t0`, `t1`, and so on in each row, and gives each
production one fact, `imported`, that holds its constraint.

`compileGraph` conjoins the facts of each production into one constraint. A
production with no facts gets `noConstraint`. Compilation keeps all states and
alternatives. It does not run a solver and does not prune.

## Patches

A `Patch` is a list of edits and the document that the edits were prepared on.
`applyPatch` returns `StalePatch` when the current document is a different
document. It applies the edits in order, and checks the graph references and
arities after the last edit. Thus an edit can refer to a state that a later
edit in the same batch adds. The initial state does not change.

| Edit | Effect |
| --- | --- |
| `PutRow state transitions` | Replace or add the row of the state. |
| `DeleteRow state` | Remove the row. The state must have a row. |
| `PutTransition state transition` | Replace the production with the same name, or append it. |
| `DefineTransition state name symbol children` | Change the symbol and children of a production and keep its facts, or append a new production with no facts. |
| `DeleteTransition state name` | Remove the production. The row stays, also when it becomes empty. |
| `SetFact state name fact constraint` | Add or replace one fact. |
| `RemoveFact state name fact` | Remove one fact. The fact must exist. |

Removing a fact removes that obligation. It does not negate the constraint.

## Language updates

A `Language state` is a source document and a map of named exclusions. An
exclusion is `AtRoot template`, which rejects matching whole terms, or
`Anywhere template`, which rejects terms with a matching subterm.
`wholeTerm` and `subterm` make an exclusion from one complete term. They match
complete symbols, refinements included.

An `Update state` is a list of operations. Updates combine with `<>`:

```haskell
changes :: Language.Update State
changes =
    Language.define (Language.at Atom "two") "two" []
        <> Language.relax (Language.at Expr "pair") "positive"
        <> Language.without "no-zero" (Language.subterm zero)
```

| Operation | Effect |
| --- | --- |
| `define ref symbol children` | `DefineTransition` on the production. |
| `remove ref` | `DeleteTransition` on the production. |
| `require ref fact constraint` | `SetFact` on the production. |
| `relax ref fact` | `RemoveFact` on the production. |
| `editSource edit` | Any other source edit. |
| `without name exclusion` | Add or replace a named exclusion. |
| `restore name` | Remove a named exclusion. The exclusion must exist. |

`update` applies all source edits of an update as one patch, and then the
exclusion operations in order. An `Update` has no expected document. Use a
`Patch` when you need the stale check.

`Language.compileGraph` compiles the facts, then removes the root exclusions
with `Template.excludeFTA`, then the subterm exclusions with
`Template.excludeAnywhereFTA`. It numbers the compiled states from 0. Template
exclusion keeps an unambiguous graph unambiguous. Overlapping templates can
make the compiled graph much larger than the source.

## Ranks

The compiled graph is a new graph. Its state numbers and ranks belong to that
compilation. An edit can change every rank, so build the query again after an
edit. `FTA.terms` ignores constraints. Use a query that solves constraints, such
as `Sized.sizedUpTo` with a solver, when the facts matter.

## Limits

- `applyPatch` compares the complete documents, and compiles the complete graph
  again. It does not reuse count tables.
- An update cannot add one complete term to a language.
