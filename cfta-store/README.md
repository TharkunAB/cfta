# cfta-store

`cfta-store` keeps revisions of an editable `Language` in memory or on disk.
Each revision records its parents, how it was made, and its metadata. Its
`RevisionId` is the SHA-256 hash of the canonical language text produced by
`printLanguageWith` and the store's state codec.

Open a store with `newMemoryStore codec` or
`openDirectory codec "language-history"`. Use `genesis store language mempty`
to save a first revision. Use its ID with `applyUpdate store` to make a child,
or use `merge3 store base left right` to merge two languages from a common
base. The write operations return either a store error or a revision ID.

Equal languages share a revision ID. The first successful write supplies the
parents, origin, and metadata for that ID. An update or merge that reproduces an
existing language returns its ID.

The directory store writes one portable text file per revision. Opening a
directory reads its revision files and builds the parent index in memory. Use
one open store handle per directory and reuse the state codec when reopening.
Let the store manage its revision files. The hash verifies the language, and
the directory supplies the parent links, origin, and metadata.

To resume a size-ordered listing, save its checkpoint with the revision ID.
Load that revision with `getRevision`, call `compileGraph` on its language,
and pass the resulting graph and the saved checkpoint to
`Data.CFTA.Sized.Checkpoint.resume`.
