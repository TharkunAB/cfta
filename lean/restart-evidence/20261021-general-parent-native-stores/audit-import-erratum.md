# Audit import placement correction

The first default build failed because the new import was placed before run_cmd instead of the initial import block. The failed exact Audit source, raw log and exit receipt remain. Moving the import before the Proof dependency audit module comment restores the legal import block. Removing that single import recovers every starting Audit byte. The selected Parent source remains unchanged. This is one real failed Lake command, separate from the author strict failure and the prelaunch stopped-Scan correction.
