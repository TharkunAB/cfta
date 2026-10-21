# Prelaunch stopped-Scan admission correction

The unexecuted 259-line source 39d513716fe26c16a37cbf100aeaba527251c3fea549ade0a246a93abef12a5e used `At.advance` at an actual stopped Scan return. That endpoint only advances physical state while retaining the old native tables. A stopped Scan can allocate new native cells.

The corrected source obtains the exact returned inventory and admission from `ConjunctionClassScanSoundness.verified` on the SAME actual stopped Scan. All its entry premises are already present. The native Current, Support and causal History still come from `ScanNativeStores.scan` at that same return. No public premise or theorem conclusion changes.

The original source remains in `parent-native-stores-prelaunch.source.lean`. Neither prelaunch version had a Lean or Lake command at the time of this correction. This is a source-review correction, not an executed proof failure.
