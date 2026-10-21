The original unexecuted verifier incorrectly equated local main with origin/main.
Root observed local main at ed73f5997f1c07e2961d06e6e290d1de38319dad and origin/main at the existing starting-main pin. These branches must remain separate.
The corrected script reads an explicit H3 starting-local-main.txt pin and compares the local branch to that pin. Root will write this observation before installation and verification.
This local-main pin was observed now. It is not claimed to be a bootstrap observation.
The saved starting-worktrees.txt has no refs/heads/main entry, so it does not independently pin this local branch.
The exact prior 112-line script and one-site repair are preserved. Reversing the repair restores every old byte.
No local branch, official file, H2 or H3 file was changed. No verifier, compiler or runtime was executed.
