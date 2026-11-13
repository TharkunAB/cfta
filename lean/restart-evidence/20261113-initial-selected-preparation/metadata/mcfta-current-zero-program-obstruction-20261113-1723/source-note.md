# Size zero source obstruction

Status: frozen UNCOMPILED Lean draft. No existing source file changed.
The draft has one private positivity lemma and one public theorem.
The six-line frozen header is unchanged.

`size_zero_frontend_without_program` obtains the actual expression from
CurrentConstruction.firstOrderRaw_total at signed zero. A local structural
induction proves Program.components positive for its var and app constructors.
The second conjunct excludes exactly the count required by RootTyping's final field.
No typing assumptions, native result, assignment, model, or other supplier is added.

The relevant existing consumer is CurrentRootTyping.firstOrderRaw_typed:29-46.
It requires an accepted source term and returns program.components=signed.toNat.
This draft proves the count obstruction directly. It adds no source-language
emptiness or native-language theorem and invokes no native build bridge.
It does not refute the per-emitted-output finite-witness target. A size zero
request need not emit an output. It supplies no output-existence assertion.

The prior audit94 and same-output target10 remain unchanged.
No compiler, Git, live file, Haskell, or board action was run.
