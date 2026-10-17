# First checkpoint metadata verification

The first root verification rejected the assembled edge-kernels log mapping.
The metadata selected kernels-3.log, which checked an earlier one-kernel
source. The final source contains three kernels. Its actual clean log is
kernels-7.log. The root mapping now selects that final log. No production
source or frozen component artifact changed. The failed mapping remains in
kernel-logs-attempt-1.json. The failure was AssertionError: edge-kernels at
the axiom-pair count check. The command stderr was returned by the tool.
