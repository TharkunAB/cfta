# Joining held protection and one causal ledger

Status: READ-ONLY AUDIT. The prospective header is OPEN and UNCOMPILED. This packet has no proof, axiom, sorry, new runtime, datatype, or theorem credit. Existing Source and frozen packets were not changed.

## Result

Do not combine the two existing existential producer results by identifying their hidden histories. Public 9374 returns an actual history with a Held qualification. The joint-ledger producer constructs a qualified history internally and then returns an indexed event list. The same output index does not identify hidden rows, receipts, callback blocks, or tail witnesses. Even putting QualifiedHistory h and HeldHistory h under one Prop proof index h would not establish identity of their hidden constructor data.

The smallest reuse route is an internal adapter that recurses on ONE Held qualification derivation. At each constructor, it uses that constructor's actual fields to derive Canonical/Total, build the joint-ledger constructor, and prove held protection for the visible outer operation entries in that same event list. It must not independently eliminate a QualifiedHistory proof to obtain those fields. At a captured constructor, extract the callback invocation from that same actual conjunct once and build its nested SelectedLedgerAt from that invocation. The resulting visible events and their R property form one bundle. No new proof datatype is needed.

## What the current theorems establish

- Owner 30502–30529: RealOuterHeldEntriesAtDepth quantifies over every actual OutputHistoryAt under the original Packet, forecast, selector, mass and reservation inputs. Its R anchor is fixed. This is stronger than one chosen raw-history producer, but a Prop proof index is still only an association.
- Owner 31604–31619: the private all-depth theorem discharges the genuine Nat induction. Owner 31664–31739: public 9374 extracts one removed bucket, follows the exact real restart equality and supplied output index, produces one actual tail history, and applies that induction. It adds no Canonical premise.
- Held definitions 42–94 and 95–184: every Held constructor retains its actual call and recursive qualification. A consumer must eliminate the Held derivation itself for those fields.
- Joint ledger 53–71: Operation carries visible cache, row, caller and callback data. JointOutputLedgerAt 114–168 and JointPreparedLedgerAt 170–274 are indexed by those event lists. The captured case uses one CapturedEventLedgerAt at 73–110, including the SAME selected receipt and terminal index.
- Joint ledger 310–511: qualified_histories_joint_event_ledgers eliminates one Qualified derivation and builds a ledger from it. The top producer at 513–538 requires initial Canonical and Total, constructs a qualified history internally, and does not accept a supplied history. It does not retain a Held qualification or an event-indexed R property.

## Authentic Canonical boundary

Packet is not Canonical. Its Safe field supplies Total, but it contains no trie-validity invariant. Therefore no theorem with the existing JointOutputLedgerAt conclusion follows from the full generality of 9374 merely by adding a proof term. The prospective header adds only PAST Canonical at the SAME original worker entry. This is an explicit local applicability requirement, not a future result oracle and not a replacement assumption for the original accepted-source theorem.

For a literal source startup, EnumerationValidity.initial_canonical at EnumerationValidity.lean:22 proves this property. For a real descendant entry, the actual history or prefix producer must transport that startup fact. runPrefix_entry_invariants at PreparationEntryInvariants.lean:99 supplies Canonical and Total at the actual first parked candidate; the literal parked receipt identifies the callback frame with that candidate. No later Packet or Canonical value may be inferred backwards from an emitted output.

## Exact reuse route

1. Start from the one Held derivation returned by 9374. Derive Canonical/Total at its literal immediate parked continuation from original Canonical, Packet.safe, runPrefix_entry_invariants, and the checked parked callback equality.
2. Reuse the literal cases in CausalHistoryInputInvariants.history_input_invariants (364–609) as local proof text, applied to the visible fields obtained from the Held constructor. Its standalone public qualification theorem is not a witness-identity bridge. The local prefix, preparation, selected-return, finalizer and false-recordTypes laws can derive the same facts without selecting a second history.
3. Use PreparationEntryInvariants.successful_preparation_entry_invariants:73 for entered Canonical/Total and that bucket's ValidSuspended. Use InvocationCanonical.selected_complete_canonical:439 and InvocationRawAliasGrowth.selected_complete_sameClass_forward:338 for the SAME captured selected receipt. Finalize and false-recordTypes preserve those facts by the laws used at CausalHistoryInputInvariants:342–362.
4. At a captured constructor, use the actual CapturedCallbackInvocationAt from that constructor. Reuse JointCausalEventLedger.captured_invocation_event_ledger:276–308 locally, or its exact invocation_event_ledgers/authenticity calls. This helper currently is private, so an ordinary module cannot name it. Owner-local proof text or a minimal same-file export is required.
5. Construct the existing JointOutput/PreparedLedgerAt constructors and prove the event-list R property at the same time. The head R is already retained in the Held constructor. Recursion handles the exact tail index. A captured constructor inserts its nested list before its actual finalize and recordTypes operations; it must not flatten a different callback invocation.

The adapter can be owner-local, where the checked private held depth and phase lemmas are available. Alternatively it can be a low-level normal module over the public Held definitions and public operation laws, with no resource engine copy. The worker-facing header must still derive the Held input internally from the original resource premises. It must not expose an external Held, history, callback or model premise.

## Reusable phase cuts and remaining export work

The checked prefix R producer is public: PrefixHeldHistoryAtOriginalBudget.prefix_held_fragment_history_at_original_budget:235. ParkedPrefixHeldStep.actual_parked_callback_packet_at_original_budget:67 supplies the actual frame/metadata/next equality and Packet. Owner real_outer_parked_depth_admission:31308 derives the lower-depth forecast data. Owner right qualifier:31469 obtains the actual prepared Packet and native held read from the checked current/phase producers.

The prepared phases already derive exact R cuts internally. Opaque owner 30675–30705 derives preparation R. Its 30796–30832 block derives the actual child/finalizer R and false-callback R. Captured owner 31133–31241 derives the actual returned Current/Held cut, residual finalizer R, callback Packet/R and lower-depth tail. These are genuine producers at explicit cuts. They need not be exported merely to assemble the proposed adapter, since the Held constructor already retains the outer-entry R. If a later consumer needs R at a nested child cut, it must extract an authentic Current/ledger cut from that same invocation; outer-entry R alone does not supply it.

## Prospective header and limit

OPEN-PUBLIC-HEADER keeps all original runtime, Packet, resource, selector and indexed-output premises. It adds PAST Canonical because the existing joint ledger requires it. It returns the original removed bucket/read/boundary bundle and ONE indexed event list with its joint ledger and R property on every recorded OUTER parked, selected and preparation entry. The property is stated on visible Operation fields. It does not rely on hidden proof identity.

The complete nested event ledger remains in the same list. The header deliberately does not assert R at every nested operation, finalizer or callback cut: 9374 proves outer-entry qualification. This bounded next theorem does not discharge the separate nested-cut producer, every historical obligation, native TypeIn, guards, or one finite accepted completion. It does not weaken any of those original goals. It is not a source or Haskell counterexample claim.
