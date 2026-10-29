# Editable languages

`Data.CFTA.Document` and `Data.CFTA.Language` keep a language in a form that
you can edit. A query needs a compiled graph. An edit needs the names of the
source productions and their separate facts. The two modules keep the source,
and compile a new graph after each change.

## Source documents

A `Document state` is an FTA whose transitions carry an `Annotation`. A
transition with its annotation is a production:

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
document. It applies the edits in order, and checks the graph references after
the last edit. Thus an edit can refer to a state that a later
edit in the same batch adds. Only `SetStart` changes the initial state, and
the new initial state must have a row after the last edit.

| Edit | Effect |
| --- | --- |
| `SetStart state` | Make the state the initial state. The last `SetStart` of a batch applies. |
| `PutRow state transitions` | Replace or add the row of the state. |
| `DeleteRow state` | Remove the row. The state must have a row. |
| `PutProduction state production` | Replace the production with the same name, or append it. |
| `DefineProduction state name symbol children` | Change the symbol and children of a production and keep its facts, or append a new production with no facts. A kept fact can refer to a child that the new production does not have. An equality on such a child holds for no term, so the production has no terms. What a guard on it gives depends on the query. |
| `DeleteProduction state name` | Remove the production. The row stays, also when it becomes empty. |
| `SetFact state name fact constraint` | Add or replace one fact. |
| `RemoveFact state name fact` | Remove one fact. The fact must exist. |

Removing a fact removes that obligation. It does not negate the constraint.

## Language updates

A `Language state` is a source document and a map of named exclusions. An
exclusion is a `Template.Exclusion`: `AtRoot template`, which rejects matching
whole terms, or `Anywhere template`, which rejects terms with a matching
subterm. A checkpoint uses the same exclusions.
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
| `define ref symbol children` | `DefineProduction` on the production. |
| `remove ref` | `DeleteProduction` on the production. |
| `require ref fact constraint` | `SetFact` on the production. |
| `relax ref fact` | `RemoveFact` on the production. |
| `start state` | `SetStart`: the state becomes the initial state. |
| `editSource edit` | Any other source edit. |
| `without name exclusion` | Add or replace a named exclusion. |
| `restore name` | Remove a named exclusion. The exclusion must exist. |

`update` applies all source edits of an update as one batch, as `applyEdits`
does, and then the exclusion operations in order. An `Update` has no expected document. Use a
`Patch` when you need the stale check.

`Language.compileGraph` compiles the facts, then applies the exclusions with
`Template.excludeAllFTA`: the root exclusions, then the subterm exclusions. It
numbers the compiled states from 0. Template
exclusion keeps an unambiguous graph unambiguous. Overlapping templates can
make the compiled graph much larger than the source.

## Differences and merges

`Data.CFTA.Merge` compares and merges versions by their stable names.

`diff base other` gives an `Update` such that `update base` of it gives
`other`. `diffDocument` gives the `Patch` of the source documents. The edits
are by name where they can be: `DeleteProduction`, `PutProduction`, `SetFact`,
and `RemoveFact`. They keep the order of the old productions of a row and
append the new ones. A row with another order is one `PutRow`. When the
initial states differ, the first edit is `SetStart`, so `diff` and
`diffDocument` are total.

`merge3 base left right` merges two versions that come from `base`. The keys
are the initial state, the state rows, the production names in a row, the
fact names in a production, and the exclusion names. The symbol and child
states of a production are one value, and the order of a row is one value.
For each key, the merge takes the version of the two sides when they agree,
or the version of the side that changes it. A key that the two sides change in
different ways, or that one side deletes and the other side changes, is a
`Conflict`. A conflict holds its key as data, for example a `ProductionRef`
with a state and a production name, and the versions of the base, the left
side, and the right side. `merge3` reports all conflicts.

The order of a merged row:

1. When one side keeps the names of the base row in their order, the merged
   row has the order of the other side.
2. When the two sides have the same names in the same order, the merged row
   has that order.
3. Otherwise, the merged row has the names of the base in their merged order,
   then the new names of the left side, then the new names of the right side.
   Two different new orders of the names of the base are an `OrderConflict`.

The order matters, because the ranks follow the order of the rows. Thus
`merge3 base left right` and `merge3 base right left` can have different
orders in case 3. A merge without conflicts can still give an invalid
document, for example a production that uses a state that the other side
deletes: the result is `InvalidMerge`. Two versions are the same when they are
equal, and equal versions have the same text in the text format.

## Ranks

The compiled graph is a new graph. Its state numbers and ranks belong to that
compilation: a rank is valid only for the graph that gave it. An edit can
change every rank, so build the query again after an edit. `FTA.terms` ignores
constraints. Use a query that solves constraints, such as `Sized.sizedUpTo`
with a solver, when the facts matter.

A checkpoint of `Data.CFTA.Sized.Checkpoint` saves a position in the listing
of a language. It holds the compiled document and the exclusions:

```haskell
Checkpoint.start bound (Map.elems $ Language.exclusions language)
    (Document.compileGraph $ Language.source language)
```

It lists the terms of `Language.compileGraph language`. `Checkpoint.resume`
rejects the checkpoint for an edited language: `StaleRow` or `StaleStart` after
a source edit, and `StaleExclusions` after an exclusion changes.
`Checkpoint.relocate` gives a checkpoint of the edited language at a term. The
new listing can repeat or skip terms of the old listing.

## Limits

- `applyPatch` compares the complete documents. A query of the edited language
  builds its count tables again.
- An update cannot add one complete term to a language.
- A production name identifies a production in one document. After
  `DeleteProduction`, `define` with the same name makes a new production with
  the old name. Neither an update nor a patch records that the name was
  deleted.
- An update has no expected document, so it cannot detect that the language
  changed after the update was written. A patch can.
