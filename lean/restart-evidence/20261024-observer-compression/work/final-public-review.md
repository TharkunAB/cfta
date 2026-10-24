# Final observer source and compiled public review

Reviewed at 2026-10-24 02:21 CEST. Status: CLEAR. No concrete source, public-statement, or axiom issue was found. The reviewer ran no compiler and made no repository change.

The complete final three installed sources were read: `EnumerationObservations.lean` (105 lines), `EnumerationNodeObservation.lean` (78), and `EnumerationPartialObservation.lean` (87). Each is byte-identical to its final successful strict input. All three strict records have exit zero, literal-empty logs, `warningAsError=true`, and `linter.all=true`.

| Installed module | Source SHA256 | Strict input |
| --- | --- | --- |
| `EnumerationObservations` | `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` | `primitive-check-1/checked.lean` |
| `EnumerationNodeObservation` | `0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d` | `node-check-2/checked.lean` |
| `EnumerationPartialObservation` | `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc` | `partial-frame-check-3/checked.lean` |

Both final node and partial sources differ from their preceding successful individually checked inputs by exactly one instance name each. The names are now `nodeObservationMonadList` and `partialObservationMonadList`. The complete instance bodies and all definitions, statements, and proofs are unchanged. This exact substitution was checked in both files.

The entire 104-line, 8,108-byte compiled public output was read without truncation. Its SHA256 is `d8d7a3e83374f4b117fdaf5c52a83f5e0fe33f6ab8176d64d328778787e5ede7`. All 12 checked signatures match the actual command input in order. All 11 printed theorem axiom sets match the requested theorem names. `Frame.symm` has an empty axiom set. Each of the other ten sets contains only `propext` and `Quot.sound`. No other axiom occurs.

The checked primitive and node comparisons permit independent fuels, require only the input frame and left totality, and return equal observations with the complete final frame. The three transport results construct actual finite observations on the related state. They do not assume a successful right read, a desired representative, a desired payload, or a desired node. The node inversion retains the same final state and the literal pending-node projection. Its fuel-extension theorem retains the exact observed output and final state.

The partial renderer currently has complete-frame preservation and exact-state successful fuel extension. Its checked statements do not assert equality of independently observed partial outputs or construct a finite partial render in the related state. Those remain subsequent work. These results also do not establish arbitrary callback congruence, a shared-driver simulation, equality of raw forests, or complete native Haskell representation/error correspondence. The actual pending/eliminated hole ID and recursive-boundary branches remain those reviewed against the existing partial renderer.

Both failed attempts are retained and were read; they are not reported as successful:

- `partial-frame-check-1`: exit 1, 1,599-byte log, SHA256 `34908a78d31fef39bcc8d47443712fd819a095124f06af1dd2b9fb2f4b1ab159`. The first partial fuel proof had a layout/application error and resulting unsolved goals. Check 2 fixed it and passed; the final check 3 changes only the instance name.
- `audit-1`: exit 1, 1,273-byte log, SHA256 `4ed3b310b197ac8eaf26d3b1ee2786fc8f62f854dd2e9c974f3e890da5f73e98`. Combined imports rejected the same generated local instance name from the node and partial modules. The two explicit instance names repair this collision without changing mathematical premises or proofs.

`audit-2` has exit zero, 3,667 build jobs, and 75,754 checked theorem dependencies. Its complete 753-byte log has SHA256 `42ff41b1418ac7c5fd4d121944be998d7880959f065cfbcf984ac6e7dd2959ca`. It contains the known older unused-`inputs` warning at `InternedFreshOrdinaryClosedCompletion.lean:24:5`, with no warning from the new modules. The raw log sizes/hashes and retained reports correlate for both failed attempts and the successful Audit/public runs.

Exact additional input identities:

- `public-1/checked.lean`: `9704d15f5c9327a95afc2f9fe2f750ee29e8f61b316f3001cf70e4d9309dc6c8`.
- `public-1/report.json`: `eef80d6511857c04f4459eb6f6c7554cb4d08131980594c33b5c1f9b6ccc5670`.
- `audit-2/report.json`: `634f2753c62b9824a70236255750b36e523c4faf702ad85c43b438190b7739d9`.
- `node-check-2/report.json`: `28053d38d7f2dedd51fc21bdad704859aae9998e6e9b56156c499d8b5be6aa3b`.
- `partial-frame-check-3/report.json`: `f6522d4bb4596200ccd7f1c0b6b26713a7e20434d1cae7a2d10dbb49eaad9c07`.

The corrected author attribution is retained in `node-review-2.md`, SHA256 `e2775faa1a7acbdd46987c0560a9d4864b19c8d71516d980f80920c4178cb460`. Arity authored the node candidate; Root read the source and installed the checked bytes. The earlier review and source snapshots remain historical. This review claims no Haskell repair, stronger combined end-to-end result, or future checkpoint publication.
