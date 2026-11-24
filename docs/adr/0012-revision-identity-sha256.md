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
- The store needs two properties of the hash. The function must have one
  definition, the same on each machine and in each release, because an
  identity is kept on disk. And it must have enough bits that two different
  languages do not get one identity by accident, because `putRevision`
  returns an identity that exists without a comparison of the texts. SHA-256
  is a standard with 256 bits, so it has both.
- The store does not need the cryptographic strength of SHA-256. It trusts
  its own directory, so nobody makes a collision on purpose. The strength
  costs little: the hash is 4 to 5% of the time to make an identity, and the
  rest is the time to print the canonical text.

  | Canonical text | Print the text | SHA-256 |
  |---|---|---|
  | 0.6 MiB | 30 ms | 1.3 ms |
  | 6.3 MiB | 332 ms | 13 ms |
  | 21.5 MiB | 1,100 ms | 56 ms |

  One evaluation each, CPU time, GHC 9.14.1 with `-O1`, on a Ryzen 9 7950X
  under WSL2.
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
- A fast hash with 128 bits that is not cryptographic. It has the two
  properties that the store needs. It saves about half of the 4 to 5%, and it
  needs a dependency as SHA-256 does.
- FNV-1a with 64 bits, written in the package, with no dependency. For a
  million revisions, two languages get one identity by accident with a
  probability of about 3 in 100 million. `putRevision` would then have to
  compare the texts when an identity exists, so that a collision is an error
  and not a silent join of two languages.
