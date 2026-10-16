# Whitespace validation

Production sources and restart documents pass git diff --check.
The evidence scan records three files with retained whitespace findings.
keys-code-build-1.log contains raw failed-attempt diagnostic text.
keys-public.lean and starting-worktrees.txt retain their final blank line.
These frozen evidence files keep their exact bytes. The final package
checksum includes them. No whitespace finding affects production source.
