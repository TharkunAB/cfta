# Whitespace validation

All eleven production proof sources pass the whitespace check. The seven
restart authorities and the new proof note also pass. The staged evidence
check passes when it excludes raw logs, starting-worktrees.txt, and the
frozen entries-public.lean probe. The worktree capture has a final blank
separator. The frozen probe has one blank line at EOF. Preserve those bytes
because their component manifests already record them. Imported checking
of that probe passes without warnings or errors.
