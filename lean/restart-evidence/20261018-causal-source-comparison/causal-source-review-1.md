# Independent review of causal source comparison and initialization

Reviewed on 2026-10-18 at 20:43 CEST. No material issue found. This review runs no new Lean check and introduces no proof pair. It reuses fifteen complete public pairs.

The review covers RootLaw, CausalPublicationProfile, CausalSourceComparison, and CausalHistoryProfiles. It also reads the unchanged prior CausalPublicationHeapInduction as a dependency. That prior module is not a new result in this batch.

`source` performs strong induction on original source syntax size. Node children, union members, and the binder body have proper smaller syntax witnesses. The binder clause receives the body law only. The induction assumes no whole-grammar source law, rank law, output relation, or future callback result.

`publication` compares the actual body and ordinary raw callback builds at `event.afterBody`. Actual callback verification supplies the two joint Contexts, availability at the captured raw return states, and forward growth to this reader. The earlier payload heap and actual empty-table history concern this pre-installation heap. They do not contain the candidate merely by assumption. Scoped freshness and aliases come from the actual publication. The two bare-self cases are checked separately before literal filters become deleted observations. No Ready premise is inferred at the callback cut.

The chronological path induction reconstructs the history through depth, ordinary, reservation, and body stages. Its new payload obligation runs before completion installs the candidate. The syntax induction and chronological heap induction have distinct premises. Their composition is not a circular assumption of candidate Correct. `build_heap` covers the actual Outcome state for a complete or pending source computation. `closed_heap` starts from empty Context, history, and payload heap. `constructed_heap` only rewrites that result at a supplied actual completed equation.

HistoryProfiles repeats the chronological preservation argument over actual History. Its retain constructor cannot add Mu records. Payload Correct is state independent, so retention needs no semantic transport to an arbitrary reader. `heap` derives the whole old payload contract from the empty-table history. `compare` then removes that separate payload premise from the source comparison API. Its actual historical calls, joint Contexts, live aliases, scoped profile and cut agreement, forward return growth, and common actual reader history remain explicit. There is no backward history inference or reader-wide lexical availability condition.

The payload contract here is the old universally assigned profile contract. Stronger tagged root-deletion cache contracts are separate results. The conclusions concern root deletion profiles. They do not establish all deeper guarded observations, full language equality, global termination, source completion, or a runtime defect.

All selected public logs pass the existing hardened full-print and standard-axiom checker. Source hashes and exact receipts are pinned in this review manifest. No production file or existing component evidence was changed.
