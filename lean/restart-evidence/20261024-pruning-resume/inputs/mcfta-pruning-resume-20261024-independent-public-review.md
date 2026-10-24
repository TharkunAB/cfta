# Partial pruning matcher and resume public review

Reviewed at 2026-10-24 02:55:50 CEST. Status: CLEAR. The complete84-line,6211-byte public readback was read, including all11 signatures and all8 axiom reports. No missing premise, raw-current mismatch, fuel mismatch, private-name leak, or frame-scope overclaim was found.

The readback is `/tmp/mcfta-pruning-resume-20261024/public-1/raw.log`, SHA256 `134c4c02aee37a2c553c6d349562a543bb9f2a0eceb7fd5de50477dafd925d9f`. Its actual report has exit0, strict warning and linter flags, matching byte/hash metrics, and an exact checked-input hash. The ordered11 declaration names equal `public-declarations.json` and its actual11 check commands. The8 axiom-report names equal the JSON theorem list and actual print commands.

I also read both complete installed modules:90-line `SourcePruningPartialMatch.lean` and242-line `SourcePruningResume.lean`. I authored the original pure matcher and earlier observer foundations. This is independent review of Required's resume implementation and the new compiled public readback; it is not an independent reproof of my authored matcher foundation. Root's matcher repair changes only two constructor case labels from `prefix` to `«prefix»`; all matcher statement and definition bodies remain unchanged.

The11 public statements have the following exact scope:

1. `Pending` is the existing-pattern/raw-Nat list alias, `Type → Type`; it introduces no new template datatype.
2. `matchPartial` takes only decidable symbol equality, the existing pattern and existing partial term; it has no Guard, state, fuel or semantic oracle parameter.
3. `matchPartial_hole` accepts every partial term with no pending piece.
4. `matchPartial_anyPrefix_nil` also accepts every shape, including truncation.
5. `matchPartial_rawHole` retains both preceding wildcard exceptions; every other pattern suspends the exact input pattern and original raw hole ID.
6. `matchPartial_truncated` rejects every nonwildcard pattern, including symbol-specific empty prefixes.
7. `resume` takes fuel, raw current ID, supplied partial term and ordered pending list; it returns the actual optional pending list in the existing `EnumerateM`.
8. `resume_frame` requires totality and one actual successful resume; it returns the complete before/after frame.
9. `resume_agrees` requires the same current ID, term and pending list, framed inputs, left totality, and two actual successful executions at independent fuels; it returns exact optional-result equality and the complete final frame.
10. `resume_transport` requires only one actual left success, the input frame and left totality. It constructs a finite right fuel, an actual right success with the same result, and the complete final frame. It has no desired-right-success or desired-result premise.
11. `resume_moreFuel` retains every actual successful optional-result/full-state transition when fuel increases by an arbitrary natural extra amount. It does not assert equality of errors or of complete result streams.

The actual `part` definition compares the representative returned for each parked raw hole ID with the supplied raw `current`; it never canonicalizes current implicitly. A nonmatching part keeps the returned canonical representative in its pending pair. `resume` first executes every representative read through ordered `pending.mapM`, then applies pure Option sequencing and concatenation. A pure `none` from an earlier match does not skip later representative reads. Order and repeated pending entries are retained. This agrees with the literal source at `Specftacular/Pruning.hs:289–297`.

The frame remains the existing complete `EnumerationCompressionFrame.Frame`: allocation counter, values, obligations, both ancestry fields and exact representative/size reachability in both directions. It is not physical forest equality. No Safe, Ready, Finished, accepted completion, pruning-soundness, read-only-state, or runtime-resource premise was inserted. The statements establish neither unconditional termination from totality nor full-driver, templateOracle, type/pruning soundness, native error, general term-order, convergence, or Haskell refinement results. The separate new-main LPO integration and native/golden validation reported by Root are outside this readback review and are not substitutes for those open obligations.

The first4 axiom reports contain exactly `propext`. The last4 contain exactly `propext` and `Quot.sound`. There is no `Classical.choice`, `sorryAx`, extra axiom, or exported private helper in the compiled public statements.

Both installed modules are byte-identical to their actual successful strict inputs, with exit0 and literal-empty logs under `warningAsError=true` and `linter.all=true`:

| Installed module | Lines | SHA256 | Actual successful input |
| --- | ---: | --- | --- |
| SourcePruningPartialMatch | 90 | `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` | match-check-2/checked.lean |
| SourcePruningResume | 242 | `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d` | resume-check-1/checked.lean |

The actual676-byte Audit log/report was read and correlated: exit0,3673jobs and75792 theorem dependency checks. Raw SHA256 is `7ff1c89a3bd339b0808e4416a88c5d43118c0d67af7938f1204e466d260b0dc6`. Its only warning is the older unused `inputs` warning at `InternedFreshOrdinaryClosedCompletion.lean:24:5`; neither new module has a warning. Resume passes its first strict attempt. The original failed matcher input and the corrected successful input remain separate retained artifacts.

Exact additional input hashes:

| Input | SHA256 |
| --- | --- |
| public-declarations.json | `32cc91283899285567b98eedff29e5fa594c304093cbfb083ce05ed1d0d03b13` |
| public-1/checked.lean | `63af8631e523198e27c4decd68abbdb9d664a6c2e30d11fb377e3d0bc74336a4` |
| public-1/report.json | `9f824cf1ee183718ae95f18298a0b503667af669b8c75bcb0becc1cca21930f3` |
| match-check-2/report.json | `c29854dcfe8ebe942ccc3ef6ea5521c19b4ade7573b1de279c27f4e012019b03` |
| resume-check-1/report.json | `1bcc89a2fbb7c71d535705739b2c14e6872c6a0eb48d9b5fe8ad032fdec500fa` |
| audit-1/report.json | `317d2a150c49a01a940ce3f424ce39c8fa840dda37c9ac79ad735eede5d30233` |
| specftacular/src/Specftacular/Pruning.hs | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |

No compiler, prepared tool, Git mutation, network action or repository edit was performed for this review.
