#!/bin/bash
set -eu
control=$(cut -d: -f3 /proc/self/cgroup)
for key in memory.max memory.high memory.swap.max; do cat "/sys/fs/cgroup${control}/${key}"; done
exec /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d /home/tritlo/Code/mcfta/lean build MicroCFTA.SourceCurrentNativeRowOrigins
