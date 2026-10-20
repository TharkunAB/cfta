# Actual warm binder terminal in an original publication callback

Reviewed at 2026-10-20 22:07 CEST.

The fixture builds one original closed program from empty tables. The program is `box[nested, outer]`. Here `nested` is a raw binder with the nullary `tag17` row. The raw `outer` binder has body `union[var0, nested]`. Both binder flags are false. The example retains unused binders. It does not test a used recursive child or native execution.

The first child publishes `nested`. The later nested call in the outer callback computes both probes at the same heap. Its node table contains the key. Its full record contains the first payload. The request and build return that same payload at that same heap. The theorem retains the first completed build, the original completed build, the actual outer publication callbacks, the raw build and filter, and a rooted callback path.

The actual union schedule has member index 1. Its prefix builds `var0`. Its suffix is empty. The union SourceRow contains the same terminal SourceRow supplied to `resume`. The physical and issued suffixes come from the actual raw build and the actual enclosing constructor work. They are not inferred from a completed outer runtime execution.

The proof calls `SourceCurrentNativeOriginalBinderResume.resume` once. It eliminates only equalities between the returned payload and the actual first payload. It unpacks the returned Stored receipt once. That receipt fixes one historical publication and one raw callback before its universal row clause. The same clause supplies the concrete nullary `tag17` SourceRow. The separate Written receipt and the expanded Stored receipt do not assert equality between their hidden publication witnesses. The historical publication also need not equal the actual outer publication.

The public theorem has the same complete statement as its private checked witness. The public alias keeps the full statement and proof printer bounded. The selected strict log has zero bytes. The selected full printer uses all eight required options and checks `@actual_warm_binder`, its full proof, and its axioms. The axiom list contains only propext, Classical.choice, and Quot.sound. There are no omissions or printer failures.

Six capped Lean commands are retained. Three fail: calculation1 has native alias/parser errors; direct1 lacks explicit node-path arguments; direct2 has one unused simp argument and an empty-list build proof that does not close by rfl. These are fixture elaboration errors. Calculation2 is a successful unselected helper check. Direct3 and public1 are selected. Every command has an effective 4 GiB max, 4 GiB high, zero swap, and a five-minute cap. Every fresh usage gate exceeds 1 percent.

This component has zero production declarations, one constructed declaration, one new source example, and no owned canonical build. It proves an actual source construction and warm historical binder receipt. It does not prove a unique publication, a different prior candidate body, a native owner, an original-root rank, or outer completion. Earlier fixture packages remain unchanged.
