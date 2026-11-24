# 13. A mask is a value, and the mask of texts is in the library

## Context

A guided search takes its scores from outside the library, for example from
a language model. After each prefix it must offer exactly the tokens that
have an accepted completion. `Data.CFTA.Sized.Prefix` gives these tokens for
the preorder of a term. A model writes text, in the units of its tokenizer,
and not term tokens.

One way to give a model a language is to export a grammar of its texts to a
decoding engine. A grammar has the productions only. It cannot express the
equality constraints, the guards, or the verdicts of a solver, so an export
must leave them out. For expressions with an equality on the two children
of `+`, a grammar of the texts offers `a` and `b` after `a+`, and the
language has only `a`.

## Decision

A mask is a value. `Mask token term` (`Data.CFTA.Mask`) is a record with the
prefix, the offered tokens with their probabilities, the undecided tokens,
the mask after a token or the reason for the refusal of the token, and the
accepted terms that the prefix is. `completionsMask` gives the mask of a
`Completions` value.

A mask over another kind of token is made from a mask. `textMask` gives the
mask of characters from the texts around the children of each symbol.
`vocabularyMask` gives the mask of the entries of a vocabulary, where an
entry is a list of tokens. The end of a text is an explicit token. The
guided search reads only the record. The library has no tokenizer: the
caller gives the vocabulary.

## Why

- The mask of a text comes from the completions, so it keeps what they keep:
  the constraints, the exclusions, and the verdicts. It refuses `b` after
  `a+`.
- A mask belongs to one language and one prefix, and both exist only at run
  time. `textMask` and `vocabularyMask` take a mask and give a mask. A
  record of functions does this directly. A type class would need an
  instance for each language and a wrapper type for each layer.
- One search then serves term tokens, characters, and vocabulary entries.
- A text can be complete and also continue: `a`, and then `a+a`. With an
  explicit end token, "stop here" is a token that the scorer scores as it
  scores the others. Thus the accepted terms of a prefix are a list.

## Consequences

- The text mask holds the readings of a text prefix: the prefixes of term
  tokens that have this text. In a notation where the text of a symbol
  starts with a child of the same kind, such as infix notation, a text
  prefix has one reading for each depth of that child. The first masks then
  cost more. In the comparison of #216, the first batch of infix prefixes at
  size 15 took 6.3 CPU seconds, and the first batch in prefix notation took
  21 ms. A warm query took about 1 µs in both.
- A mask is exact for the completions up to the size bound of the
  `Completions` value. It says nothing about a larger term.
- A syntax filter in front of the mask can reduce the cold cost. #222
  measures one.

## Discussion points

- Text outside the library: export the grammar, let an engine make the
  masks, and check the finished text against the language. The engine then
  offers tokens that no accepted text continues, and a wrong text is found
  only at its end.
- A type class in place of the record. It gives nothing that the record
  does not give, and a mask that is made from a mask needs a new type for
  each layer.
