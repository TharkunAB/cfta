# 3. Terms are small-arity trees

## Context

Both packages built and read terms as `Data.Tree.Tree symbol`: a root and a
list of children. Most nodes have few children: in the standard cells a node
has at most two children, except the three-child `if` of the typed
expressions. A list spends a cons cell and a pointer for each child. A path
read walks the list, a decoder that fills children by index builds and reads
a map of slots, and every match on a node pattern-matches a list.

## Decision

A term is a `Term symbol` (`Data.CFTA.Term`) with one constructor for each
small arity: `Leaf`, `One`, `Two`, `Three`, and `Many` for four or more
children. The pattern `Node symbol children` is a complete view, and most code
builds and matches terms through it, so code that reads a term as a root and a
list of children does not change. The enumerators, which build terms in their
inner loops, use the constructors directly, so that they build no list of
children. `Data.Tree` stays only for display (`drawTree`) and the `toTree`
views.

Two pragmas keep literal symbols constant: `NOINLINE fromString` for
`Symbol` (#76), and `INLINE Node` with `INLINE [0]` on its view, so that GHC
inlines the view in the module of a match and not into the exported matcher.

## Why

Against the list version, cachegrind instructions: `enumeration-speed 1`
-25.0%, `lta-eq 3` -9.7% (allocation -15.3%), `lta-automaton 4` -1.2%; the
other standard cells move by less than 0.03%, and every sample checksum is
equal. A node with up to three children needs no separate spine, and a
decoder places its children without a map of slots.

The `Node` view keeps the code as readable as before. With the pragmas, a
match on a list of known length, such as `Node symbol [left, right]`, compiles
to a match on the constructor, so the decoders are as fast through the view.
A list of children of unknown length is a cost: when the enumerators build
their terms with the constructors, `enumeration-speed 1` needs a further 10%
fewer instructions, with equal checksums.

## Consequences

- The term type is in every public signature that carries a term, so this is
  a breaking change of the API (there is no release yet).
- The `Show` text of a term changes: a term shows as `Node` builds it, as in
  `Node "add" [Node "zero" []]`.
- A match on the `Node` view gives the children as a list. Code that needs
  more speed can use the folds and index reads of `Data.CFTA.Term`.
- A literal symbol in a pattern stays a constant only through the pragmas
  above. A `Text` literal given to the `Symbol` constructor is not covered.

## Discussion points

- Measured alternatives for the children, against lists: an `IntMap`
  (`lta-eq 3` -8.4%, but enumeration +2.3% and path reads +8% to 9%), a
  `SmallArray`, a boxed `Array`, and a boxed `Vector` (each slower on at least
  one standard cell). The pull request that added the type has the
  measurements.
- Arities: `Three` covers constants, function application, and `if`, which is
  most of the terms the packages build.
- `Many`: a `Seq` (`containers`). With `Three`, no standard cell builds a
  `Many`, and `Seq` and `SmallArray` measure the same; `Seq` needs no
  `primitive` dependency. A four-child node takes 14 words with `Seq`, 9 with
  `SmallArray`, and 15 with a list. The constructors stay hidden behind
  `Node`, so the choice can change later.
- Path compression of one-choice nodes was measured and rejected: the flat
  edge loses the sharing of subterms (up to 3.6 times the instructions).
- Strict fields were measured and rejected: every field strict gives
  `enumeration-speed 1` +1.2%, and a strict symbol alone +1.3%, with no gain
  elsewhere. The children stay lazy, as in `Data.Tree`, so a reader of the
  root does not build the subterms. No field can be unpacked: the symbol is a
  type variable, and the children and the `Seq` are sum types.
