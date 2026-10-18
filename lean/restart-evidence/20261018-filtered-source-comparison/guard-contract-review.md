# Original root filtering and a stronger payload contract

Read-only design review: 2026-10-18 19:31 CEST. No Lean job or production change belongs to this review. Definitions below are proposed contracts, not checked new declarations.

## Exact observation

`InternedConstructorTemplates.withoutSelfReference` (line 329) tests original `Value.referenceOf`. It removes the selected bare reference only from a root union. A standalone reference remains unchanged. A Mu root remains unchanged, even if its stored reconstruction later returns a reference. `cleanup` (line 631) is a separate operation: it reads the stored body's free names and its exact bare-self tag.

`SourceCurrentLiteralFilterParts.literal` gives the exact literal-atom rule, including the standalone exception. Its `row` theorem retains every complete original ordinary row. Neither theorem unfolds Mu atoms. `InternedStoredSubstitution.encode` instead rebuilds an OPEN Mu as a smart binder, and captures a CLOSED Mu unchanged. A denotation can therefore expose names that the original root filter never tests.

Consequently, `StoredMuProfileContract.Correct` cannot alone justify moving root filtering through a comparison. It compares all assigned denotations, but does not retain which reference alternatives were direct in the original records. Deleting a name from the final assigned profile is invalid: it also deletes names supplied by replacements or exposed by a reconstructed Mu.

## Reviewed implementation

The reviewed `SourceCurrentStoredFilteredProfile.lean` has SHA256 `36d7af210f1bb4314813017a31d02ed74e54943a3c1e43f0ba7001c6a68d8be0`. Its `filtered` definition keeps the original-record distinction before interpretation. Its `reference` theorem preserves standalone self. Its `mu` theorem retains Mu as an original root atom. `congr` and `absent` use exact free-name metadata and actual availability. `filter_profile` correctly derives the actual result from `StoredProfileComposition.makeUnion`.

No material issue was found in these proof bodies. The actual correspondence endpoint explicitly requires Ready at the ORIGINAL filter entry. Context-only source hypotheses do not supply that premise automatically. This review does not remove it or assume readiness at a later heap can be transported backwards.

## Recommended contract

Use a pure unconditional deletion observation `Delete(value, cuts, assignment)`. It removes only ORIGINAL direct root references in `cuts`:

```text
Delete Empty cuts rho = some []
Delete (reference n) cuts rho = if n belongs to cuts then some [] else rho n
Delete (node ...) cuts rho = denote (node ...) rho
Delete (Mu ...) cuts rho = denote (Mu ...) rho
Delete (union members) cuts rho = combineMany (members.map (Delete cuts rho))
```

The recursion follows root unions only. It never applies deletion inside an ordinary row, a Mu body, or a replacement profile. Normal/Available facts are needed when connecting this pure fold to an actual resident union and its closed shortcut.

For own-name renaming, use symbolic root labels `local | external reference`. Tag a direct name as local exactly when it equals that side's own name. Let `q = interned entry.identity` and `r = uninterned (ordinaryLevel depth)`. Require, for every finite set of symbolic deleted labels, every outer assignment rho, and every local profile t:

```text
Equivalent
  (Delete body     (names n whose q-tag belongs to cuts) (shadow q t rho))
  (Delete ordinary (names n whose r-tag belongs to cuts) (shadow r t rho))
```

Use the tag-membership test directly. Mapping local and external labels back to concrete names first can identify an external name with the local and delete the wrong atom. Also retain exact bare-root parity under the same renaming. For the binder's own exception this is `body = reference q iff ordinary = reference r`. `PublicationBareParity.bare` already derives this fact for an actual publication. For a general reusable deletion observer, retain the original bare-root label, rather than infer it from a possibly Empty non-reference denotation. The empty cut recovers ordinary denotation comparison in normal available records. The local singleton cut supplies the missing union-member comparison. External cuts are necessary for enclosing binders.

A structural implementation can retain (1) the finite set of tagged ORIGINAL direct root references, (2) the assigned denotation of all non-reference root alternatives, and (3) the exact bare-root tag. The remainder includes ordinary rows and literal Mu atoms, interpreted with `denote`; it is not a constant opaque flag. Those data reconstruct every Delete observation. The bare tag restores the standalone exception. Original non-reference presence plus the direct-reference set is an alternative way to derive the bare tag under normal-form facts. Do not assume a remainder's future Empty profile proves it had no original non-reference parts.

Testing only `filtered q body` against `filtered r ordinary` is not the useful strengthening. Installed payloads have already passed their own filters (`InternedStoredSelfFilter.Clean` and actual callback filtering). That test can reduce to the old Correct condition. The new observation must retain direct-root reference support for EXTERNAL names too.

## Constructor and induction consequences

Unconditional deletion is the useful union homomorphism. Canonical flattening, duplicate removal, Empty removal, and ordinary-only merging preserve its profile up to Equivalent. The actual normalization proofs can reuse complete literal membership and the new StoredProfileComposition laws. An ordinary node has no direct root references, so its Delete observation is its existing denotation. Its child comparisons need the empty-cut profile and the exact ordered survival test. The standalone exception must be restored after parent normalization; filtering each input member separately is incorrect when several bare references normalize to one standalone reference.

The causal publication step must DERIVE this stronger contract from actual source callbacks and earlier resident payload contracts. Heap induction transports a derived contract; it does not establish that semantic step. The source induction also needs exact live alias tests for own/external labels. Equal assigned profiles alone do not preserve those alias classes. Retained-winner lookup must keep the actual earlier writer and its complete probes; it cannot replace that writer with the current requester.

This proposal compares filtering BEFORE stored interpretation. It does not assert that filtering a later reconstructed result commutes with reconstruction: a Mu may produce a new direct reference, and normalization may change a union into a standalone reference. A separate actual execution theorem would be needed for that different order. The proposal is a root-profile contract, not row-language equivalence, recursive termination, or a Haskell defect. No new counterexample is claimed by this review.
