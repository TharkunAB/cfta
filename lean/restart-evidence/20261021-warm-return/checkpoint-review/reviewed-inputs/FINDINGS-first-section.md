# Current formalization findings

## Haskell fix handoff for external work

### External Haskell repair status

No new Haskell repair is required by this proof checkpoint.

| Repair | Imported status | External action |
| --- | --- | --- |
| Recursive self-type field pools | Fixed by `b9219b9e`, merged in PR #65 at `c0cc8a05`. The API rejects a field pool for the datatype itself. This includes the reported `Chain` case. | No additional patch. Keep the historical reproducer and validation below. |
| Typing binder size-order documentation | Fixed by `74691832`, merged in PR #97 at current imported main `794903b3f`. This changes documentation. | No additional patch. The earlier failed runtime reproduction remains unvalidated. |

Both repairs are in the imported main history. No Haskell source changes
in this checkpoint. All earlier repair entries and evidence remain below.

