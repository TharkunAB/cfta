# 12. A revision identity is the SHA-256 hash of the canonical language text

## Context

`cfta-store` keeps the revisions of an editable `Language`. A revision has a
language, its parents, its origin, and its metadata. A revision needs an
identity that a caller can keep, compare, and use as a file name, and that is
the same in each process and on each machine. `cfta-serialization` has a
canonical text for a language (`printLanguageWith` with a state codec): equal
languages have equal texts. `Data.CFTA.Language.Merge.merge3` compares
languages directly and needs no identity.

## Decision

A `RevisionId` is the SHA-256 hash, in hexadecimal, of the UTF-8 canonical
text of the language. The hash covers the language alone. It does not cover
the parents, the origin, or the metadata. `cfta-store` depends on
`cryptohash-sha256`. `cfta` and `cfta-serialization` do not.

## Why

- The canonical text is already the identity of a language. Its hash is a
  name of fixed length for that identity, and the name is fit for a file name
  and for a reference in another record.
- The identity is a function of the language. Two processes, or two branches
  of one history, give the same identity to the same language without
  coordination.
- A cryptographic hash makes a collision of two different languages
  negligible. Thus the store can treat equal identities as equal languages,
  and it can check the language of a revision file against the name of the
  file.
- The dependency is in the one package that needs it.

## Consequences

- Equal languages share one revision. The first successful write gives the
  revision its parents, its origin, and its metadata. A later write of the
  same language returns the identity and changes nothing. Thus two branches
  that reach one language share a revision, with the history of the branch
  that wrote first.
- The identity depends on the canonical text format and on the state codec.
  A change of either one changes each identity. Open a store again with the
  same codec.
- The hash verifies the language of a revision file. It does not verify the
  header: the store trusts the parent links, the origin, and the metadata
  that it reads.
- An identity has 64 characters.

## Discussion points

- The canonical text as the identity, without a hash. This needs no
  dependency. But the identity is then as long as the language, and it is not
  fit for a file name.
- A hash of the language and its parents, as the identity of a Git commit is.
  Each history then has its own identity, so one language on two branches is
  two revisions, and the question "is this language in the store" needs a
  second index.
- A shorter hash that is not cryptographic. A collision would then join two
  different languages, and the store would not see it.
