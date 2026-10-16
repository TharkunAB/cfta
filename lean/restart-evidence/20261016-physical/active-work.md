# Work newer than the audited checkpoint

The audited checkpoint contains seven frozen modules listed in frozen-modules.json.
Two additional owned files are under active development and are not included in
that audit or its theorem counts:

- lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalTraceCompletion.lean:
  protected yielded traces, bind composition, and the joint completion induction.
- lean/MicroCFTA/SourceCurrentAllocatedNativeReferenceMeaning.lean:
  original bound-reference readback, local laws, and actual branch traces.

Inspect the current files and their terminal build/freeze evidence before using
them. Keep their source bytes and evidence during the next refresh. They do not
change the remaining obligations stated in the restart documents.
