# Integer closure under private term views

`IntegerTermViews` completes the fixed-outcome coordinate reader for the
three request forms in `Gen.Internal.Static.pointsStatic`: WholeTerm,
SpineView, and LabelledView. It uses `GeneratorCombinators.Label` for the
private constructor distinctions. Projection never inspects the erased
natural-number representation in `RecipeCompile.FillLabel`.

`fill` and `fillForest` execute the source `Compile.fillHoles` traversal.
They retain every private label and specialize user labels before their
children. `adapt_fill` and `adapt_fillForest` relate that typed traversal to
the earlier whole-term codec. The adapter is used only after a view has been
selected. The final view comparison uses the complete typed labels.

`spine` is the existing `SupportTerms.applicationLeftChildren` function.
`labelled` follows the source Pure, singleton Choice, JoinN, and application
cases. `labelled_source` proves that it gives exactly the children returned
by `SupportTerms.labelTerm`. Pure and Placeholder must be nullary. `Valid`
states these two requirements recursively. The source constructors satisfy
these requirements. `template_valid` derives them for every bare reader in
`OpenIntegerReaders`; maps and pays retain the template. Choice and user
constructor closure also preserve validity.

`spine_fill`, `labelled_fill`, and `project_fill` prove that each projection
commutes with filling. These equalities include the remaining coordinate
suffix. `project_count` derives that every view retains the complete hole
count. `view_symbols` proves that the actual child-aligned extraction reads
all filled integer symbols in the original order. `readView_fill` supplies
the full tuple inverse. No projection injectivity or term-codec inverse is
assumed.

`rankView` implements one original outcome's coordinate extraction, lattice
rank lookup, and final `hasView` check. `rank_decode` composes the reader with
the successful public lattice constructor. `rankView_sound` proves that
every returned rank is valid and decodes to the requested projected term.
`rankView_exact` proves exact recognition of the projected tuple language.
`decode_injective` gives distinct projected terms at distinct tuple ranks
for this original outcome. `integer_rank_decode` uses the actual source
integer symbol and the proved singleton reader. `reader_rank_decode` also
derives template validity and the hole count from the actual bare reader.
User-label specialization can be arbitrary: the inverse reads coordinate
leaves and the final check verifies all projected labels. Its successful
formula semantics and exceptions remain in `IntegerLabelCodec`.

These results are per original outcome. `labelled_not_globally_injective`
shows that different private choice members can have the same labelled
view. This does not imply a library defect. Member ranks preserve source
positions, including repeated views and values. The original `outcomeRanks`
search must still offer each relevant original member to `pointsStatic`.
That candidate discovery is a separate obligation. Complete OpenKey formula
and count invariants across all grouping and constructor cases also remain
separate from the proved bare-reader cases.

Validation: `lake build MicroCFTA.IntegerTermViews` uses the pinned Lean
4.34.1 toolchain. No admitted declaration or native proof evaluation is used.
No Haskell source changed for this proof milestone.
