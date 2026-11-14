# Complete hook case proof repair

Created 2026-11-14 at 07:02 CET. Status: UNCOMPILED. Root must compile this source.

The source has one proof edit. It replaces the successful finalization subcase in `visitCapturedWith_transport`. It preserves all eight theorem headers, the other seven proof bodies, all definitions, and all print commands.

Root check3 reports one mismatch at line 172. The target retains the private complete-receipt hook match. The public `receipt_erasure` application does not close that target by definitional equality. The replacement exposes both private hook matches with `change`. It then splits the same actual hook result and closes both constructors by reflexivity. It retains the exact receipt, outputs, continuation reason, and native endpoints. It does not change a map or a worker.

The input SHA matches Root's exact check3 input. The edit has an exact textual inverse. GNU patch applies and reverses with zero fuzz and exact byte checks. All eight theorem headers match byte for byte. The unchanged prefix and suffix verify that no other body or instrumentation changed. `checks.json` pins the source, complete immutable diagnostics, actual private and public receipt implementations, and verified five-map source.

No compiler, Git, live source, Haskell, or board operation ran. Root check3 and all earlier drafts remain unchanged. Source integrity checks do not provide Lean proof credit.
