# Recover an authentic base key from auxiliary equality

Status: FROZEN UNCOMPILED proof candidate. Root owns checks and normal Source integration. No compiler or test was run. All three full FIRST headers were frozen before their bodies. The initial header-only packet remains preserved; the selected FIRST headers change only indentation inside existing shape binders, with identical tokens.

## Three laws

`auxiliary_key_eq_recovers_singleton_base` is pure. It takes the exact four possible auxiliary shapes for each side:

- Kb = extend K [u] e.
- Kb+d = extend (extend K [u] e) [u] d.
- Kd = extend K [u] d.
- Kt = extend (extend K [u] d) [u] e.

Here K is EXACTLY extend emptyKey [u] parentPair. The lemma permits ANY old/new combination among those shapes. It requires only that the OLD parentPair differs from e and d. The proof finds oldParent in the old seen set, transports that membership through the observed full key equality, and excludes e/d on the new side. The remaining member is newParent. Base-key equality is then ordinary congruence. It never cancels extension of an arbitrary domain.

`source_parent_pair_avoids_auxiliary` derives those two exclusions from actual resident records in ONE coherent reader. Its U is the literal available Mu whose stored B is an ordinary node with free [.interned u]. Its P is available and closed, with its actual identity and node/union tag.

The proof derives B availability from U's actual children. SourcePreparedSharedRows.read_identity reads B even though B is OPEN. P and B cannot have the same identity: coherent readback would identify their full values, contradicting closed P versus B's singleton free list. P and U cannot share an identity: full readback would identify their values, contradicting P's ordinary/union tag versus Mu. The existing sorted pair's fixed-owner injectivity then gives parentPair != pair(b,u) and parentPair != pair(u,u).

`source_auxiliary_key_eq_recovers_full_pattern` is the source wrapper. It DERIVES both exclusions internally, applies the pure exact-shape law, obtains pOld = pNew, and applies same-reader closed identity injectivity to conclude FULL oldP = newP and exact original base-key equality. It takes no cancellation or noncollision premise. The new pattern need only be closed, available, and identified; a new ordinary-kind premise is unnecessary. No closedness premise is imposed on B.

## Honest source inputs

The source wrapper uses only Facts for one actual reader, the actual available stored U/B shape, full old/new pattern availability and closedness, their actual control identities, the original ordinary-kind fact, and the two exact auxiliary-key shapes with observed equality. These facts are produced by the existing source body classification, authentic entry receipts, and real old-to-reader growth. AuthenticEntry already retains each pattern's closedness, identity, and node/union tag.

Use one common physical reader for all four values. Existing ordered-entry/common-reader laws and the checked arbitrary-start equal-key transport provide that reader and growth route. Do not attach availability from a different existential reader merely because a Prop index agrees.

No additional semantic qualification beyond those actual availability/closedness/kind facts was needed. The helper does not assume Profile, a body/result law, OnlyU, future model, or a new entry record. The source U/B depth/ordinary fields and row list remain literal inputs.

## Why the exclusions matter

Arbitrary extension cancellation is false. If an old parent pair is one auxiliary pair and the new parent is the other, extensions can produce the same two-element seen set with different parents. The source record proof excludes precisely that collision. This is a key-algebra observation, not an accepted-source counterexample.

The wrapper proves equality of structural BASE KEYS and full patterns. It does not assert equality of arbitrary interned domain handles. Actual represented-domain uniqueness can be applied later in the same reader where its existing hypotheses hold. It also does not assert that the auxiliary family tags are equal: Kb+d and Kt can have the same canonical set. Both authentic shapes remain covered.

## Use in the next warm proof

The checked returned-cell full admission now exposes an original base-entry bundle for every auxiliary clause and every zipped row child. At a later reuse, identify the old/new concrete Kb, Kb+d, Kd, or Kt expressions from those actual bundles. Their actual key equality and common-reader records instantiate this source wrapper. The recovered base K equality permits the existing fixed-family PastEntryNextQueryInnerLaws transport to be applied at the original full P and cutoff.

This closes only that key/physical identity step. It does not create the chronological source producer, semantic payload law, or warm NoNewMu induction. All old retained-cell, native Type/Marker, every-event compatibility, and ONE accepted finite-completion obligations remain as before.

## Check layout

Compile the standalone normal candidate SourceCurrentNativeAuxiliaryBaseKeyRecovery.lean with its two ordinary existing imports, then append PROBES. Expect three public axiom reports. The module has two small private proof helpers. There is no heartbeat override, linter suppression, new runtime, or datatype. No normal Source, old packet, Work, Git, board, or temporary file was changed.
