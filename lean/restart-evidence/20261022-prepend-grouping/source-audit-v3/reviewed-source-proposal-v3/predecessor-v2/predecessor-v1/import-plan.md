# Import plan
The only new module import is MicroCFTA.SourceCurrentMergeGrouping.
Its live import is MicroCFTA.MergedSourceGrouping. That module imports MicroCFTA.MergedPhysicalGroupRoot and MicroCFTA.Sized.
Table, Iteration and Iteration.permutation come from the unchanged MergeGrouping module. Sized.groups is already used in that public permutation type and is transitively available.
The installed core List and Option lemmas are already used by the existing imported sources or are in the default Init library. No new dependency or project import is proposed.
This is a source-read import assessment, not a compiler import check. All imported project source bytes remain unchanged.
