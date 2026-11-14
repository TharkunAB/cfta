# Actual staged input shape normalization

Status: UNCOMPILED. Root reported the preceding independent own19 failed.
The readback goal retained a bare staged list. The stagedSame equality still
had nested product projections on both sides. The simplifier could not match
that equality, so it did not reach the nested list maps.

The only repair changes stagedSame to its explicit definitional normal form.
The left side is the literal CachedOwn.complete staged child map. The right
side is the observed staged list. The existing readback proof can then project
the actual child inputs. The header, current resources, source operation,
all other proof statements and original marked targets are unchanged.
No resource assumption or future provider is added.

The actual empty-tail callback composition remains unverified. General
ordinary children, full scan, full worker and common finite completion remain
OPEN. No Haskell defect was found. No Haskell or FINDINGS file changed.
No compiler, live-source, Git, board or tmp write occurred.
The clear-writing checks were applied.
