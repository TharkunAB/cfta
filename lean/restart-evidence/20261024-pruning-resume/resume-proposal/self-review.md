# Resume source self-review

Status: SOURCE_ONLY_AUTHOR_SELF_REVIEW_COMPLETE. This is an uncompiled proposal. The author reviewed all 242 source lines. This report does not give independent approval or a compiler result.

The definition follows `specftacular/src/Specftacular/Pruning.hs:289–298`. It runs `pending.mapM part` before it sequences the pure `Option` results and concatenates their lists. A `none` match result is a value inside the state action. It does not stop later representative reads. A bounded representative read can still fail through the existing action error. Input order and repeated parked entries are retained.

Each part uses the actual `EnumerationState.representative` action. It compares the returned root with the unchanged, raw `current` argument. When they are equal, it calls the imported `SourcePruningPartialMatch.matchPartial`. Otherwise it returns the same pattern paired with the returned root. The source does not replace the matcher with a callback parameter. It does not assume that `current` is canonical.

`resume_frame` preserves the complete existing compression Frame. `resume_agrees` compares two supplied successful actions at independent fuel bounds. `resume_transport` constructs a finite successful action on the right from one actual left success, Frame, and left representative totality. Its list induction follows the actual intermediate states. The common right bound is the sum of the head and tail bounds. Existing fuel-extension lemmas retain both constructed endpoints. `resume_moreFuel` retains the exact optional result and full final state.

The proof uses the existing representative agreement, transport, Frame totality transfer, stateful mapM invariant, and Retains bind/mapM APIs. The seven private lemmas expose one-part success, one-part properties, and ordered traversal properties. The local List Monad and LawfulMonad instances have distinct explicit names. Their proof pattern is the existing EnumerationUntilBridge proof.

No Safe, completion, desired right success, canonical-current, callback, or semantic-output premise is added. The public arguments use the same pending list, partial term, and raw current on both sides. The result does not prove arbitrary pruning callbacks, complete pruning execution, native representation refinement, or resource bounds.

The installed matcher SHA is `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509`. Its difference from the reviewed owner matcher consists only of the two proof case labels `prefix` changed to `«prefix»`. The executable matcher and its interface are unchanged.

One author preflight changed the Lean binder name `partial` to `term`, because `partial` is a keyword. The initial uncompiled draft and its exact patch are retained. This was not a compiler attempt. Static text checks found no sorry, admit, axiom, unsafe, or option override. No selected source was compiled or imported by the author. No repository file was changed.

Selected source SHA: `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d`.

The source index records exact input paths, byte sizes, hashes, and read scope. Root owns subsequent compilation and integration. Upstream LPO integration is separate; it does not change the matcher or observer APIs used here.
