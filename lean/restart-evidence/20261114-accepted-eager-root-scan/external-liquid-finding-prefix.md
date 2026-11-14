## External Liquid duplicate-name fix available (2026-11-14 02:48 CET)

PR [#212](https://github.com/TharkunAB/cfta/pull/212) is open and unmerged.
Its head is 438be86d6cc3642a44a25816733ad922a5ee6e99 on main e53852064d.
The external fix makes every occurrence of a repeated query name use the last
occurrence's refinement type in synthesize, headsOf, environmentOf, checkerWith,
valued and qualifiers. It uses an internal queryBindings helper. parseQuery stays
unchanged. This matches the base Query rule from #211. The PR reports that the old
contradictory environment admitted invalid programs. Its reproduction and test
results belong to that PR; Root did not repeat them. No repository Haskell file
changed here. Integrate when the fix reaches main, then refresh correspondence
claims and source pins. The external owner retains this implementation.
Primary GitHub metadata was checked at 02:48 CET; the PR remains unmerged.

