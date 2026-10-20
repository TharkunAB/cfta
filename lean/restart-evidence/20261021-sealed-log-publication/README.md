# Publish required sealed validation logs

The repository ignores *.log. Two recent publication commands added their
restart directories without forcing those files. Their local checksum
seals passed, but 77 required logs were absent from the branch.
The logs contain 28313077 bytes. Their existing SHA256SUMS entries match.
This change adds those exact logs. It changes no existing source or seal.
The audit reads all older checksum manifests and finds no missing local
file. The first audit read repository-relative paths incorrectly. Its
source and result remain. The second audit supports both path forms.
No Lean job is repeated for this publication correction.
Future publications must check every sealed path against the Git index.
