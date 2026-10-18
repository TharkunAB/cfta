# Actual retained-writer source generators

Final review at 2026-10-18 14:37 CEST.

## Result and interface

`SourceCurrentRetainedMuDirectedCase.lean` has source SHA256 `05d0aee93c334dac44fbf924590677885608657b352cfa7cb9eb14dd7b345282`.

`Generated reader` is an inductive relation. Its first constructor retains equality. Its second constructor retains two actual reconstructions of one source expression. That constructor includes historical source contexts, exact raw build and filter calls, actual growth to the fixed execution reader, exact warm build and filter replays, actual warm stored calls, reader Ready, filtered input availability and replacement availability. It also includes the source's live alias tests and exact tests against both root-filter names.

`Inputs reader` is mutually inductive with `Generated`. Empty inputs retain the maps. A reference slot retains BOTH generated directions between the resolved values. An identical capture retains equal maps on its free names. The private embedding uses the existing ReaderReplacementSlots.Paired relation with mutual Generated membership. This representation satisfies kernel positivity. It does not weaken the lexical slot contract.

The public `binder` theorem takes an actual source binder build, its initial source Context, an actual later Keeps receipt and an actual Path from empty tables to the reader. It recovers the selected record and its earlier writer. The same returned writer retains its missing-record condition and all four actual history cuts. The theorem constructs both stored reconstructions, their final warm calls, initial and final Mu epsilon membership, output availability and Keeps. It derives Generated membership in BOTH directions between the two reconstructed outputs.

The generator membership comes from the earlier writer's actual expression and captures. The writer expression is not equated with the current requester's expression. No selected writer, output relation, Same theorem, BodyIH or completed reconstruction endpoint is supplied by the caller. Reflexive membership supplies the same selected Mu replacement at both local input slots. Shared sparse substitutions preserve both actual stored calls. Actual raw callback replay supplies the source and root-filter generator data.

## Scope and remaining proof

This module proves source-generator membership. It does not prove Directed for all Generated pairs. The local source/filter clauses, ordinary row survival, active nested-binder clauses and global source-generated simulation remain separate proof obligations. The generator includes no literal Below seed. Generated remains a directional relation; lexical reference slots explicitly require both directions.

Growth transports the actual source and constructor calls. The proof does not transport an observation relation between readers. The original unfolding can allocate. The generated pair uses its actual later reconstruction heap, where both stored calls and both raw source/filter calls replay without heap changes. There is no new physical Empty preservation theorem for every generated pair.

Actual history supplies the earlier writer. Grows alone does not establish publication chronology. The public theorem retains the current requester's original successful binder equation and finish behavior. A smart returned value is not assumed to be the raw selected Mu.

## Constructed integration

The source author is `binder false (node [row 7 [var 0]])`. The witness proves that the stored body contains its own interned name. The selected Mu is therefore genuinely used. Its initial Ready state and actual growth Path are derived from this source's build from empty tables.

A later requester uses the syntactically different body `union [node [row 7 [var 0]], Empty]`. Its literal warm binder call returns the existing Mu at the unchanged reader. The witness invokes the new public binder theorem and retains both generated reconstruction directions, the actual original and final unfold calls, Keeps and output availability. This validates the interface on an earlier writer with a different later requester. It does not claim a changing-capture fixture or accepted finite inhabitation.

The private checked witness has an exact explicit public statement alias. The selected full printer source includes the complete checked fixture. No future context, history, endpoint or output relation is an input to the fixture.

## Validation and preserved attempts

- Selected production strict: `retained-directed-direct-6`, exit zero and literal zero-byte log.
- Selected canonical: `retained-directed-canonical-2`, clean terminal zero, 599 jobs.
- Selected public: `retained-directed-public-2`, eight full signature/proof/axiom pairs, including all five handwritten constructors.
- Selected constructed strict: `retained-directed-kernels-3`, exit zero and literal zero-byte log.
- Selected constructed full probe: `retained-directed-kernels-public-2`, one full pair.
- Every selected source uses linter.all. Every selected full probe uses all eight required printer options. Only propext, Classical.choice and Quot.sound occur as axioms.
- All selected checks record effective MemoryMax and MemoryHigh of 4294967296 bytes and MemorySwapMax of zero. They use pinned Lean 4.34.1 and a five-minute wrapper. Final recorded peak is 220 MiB or less.

All earlier attempts remain pinned. Direct1 exposed the nested-inductive positivity restriction. Direct2 through direct4 retain elaboration and equality-conversion failures. Direct5, canonical1 and public1 are successful historical checks of the earlier one-direction lexical reference constructor. The final direct6/canonical2/public2 selection uses mutual lexical reference membership. The first fixture attempt left a concrete List.Mem goal; its corrected checks remain separate snapshots. The fixture strict and full probes were repeated only because the production dependency changed.

Counts: eight public pairs, one constructed pair, zero auxiliary pairs. No prior frozen source, evidence, shared metadata, Haskell file or authority document was changed.
