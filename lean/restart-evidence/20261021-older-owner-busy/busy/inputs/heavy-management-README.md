# heavy-management

Run heavy builds, tests, and benchmarks side by side on one machine without
running it out of memory.

Each job runs under a hard memory cap in its own systemd user scope, so the
kernel kills the job, not the machine. A pueue queue limits how many jobs run
at once, in groups by cap, so the sum of the caps of all running jobs stays
below a fixed budget. Each job's peak memory is recorded, so the next cap can
follow the measured peak instead of a guess.

## Scripts

- `bin/capped [--mem SIZE] [--time DURATION] command...` runs the command in a
  systemd user scope with `MemoryMax`, `MemoryHigh` and no swap, and under
  `timeout` when `--time` is given. Exit 124 means the time cap, 137 the
  memory cap. When the command ends, its peak memory is appended to
  `$HEAVY_PEAKS` (default `~/.local/state/heavy/peaks`): the date, the
  command, the cap, the peak in MiB, and the exit code.
- `bin/heavy [--later] --mem <N>G --time <M>m command...` queues the job in
  pueue under `capped`:
  - a cap up to 4G goes to the group `small`, a cap up to 8G to the group
    `medium`, a cap up to 12G to the group `large`, and a cap up to 16G to
    the group `build`. A larger cap is
    refused: size it from the recorded peaks;
  - `--later` gives the job a low priority, so jobs that matter now start
    first;
  - `--gpu` puts the job in the group `gpu`, which runs one job at a time,
    so two jobs never share the GPU; the `--mem` cap still applies;
  - the output streams to stdout, and the exit code is the command's own;
  - stopping `heavy` stops the whole job: it kills the task, stops the job's
    systemd scope (`heavy-<time>-<pid>.scope`), and removes a task that
    still waits. `pueue kill` alone does not reach a job that `timeout`
    put in its own process group; stop such a job with
    `systemctl --user stop heavy-<time>-<pid>.scope`.
  - `--exclusive` is refused: wall-clock timings belong on a quiet machine.
- `bin/heavy-setup [build] [large] [medium] [small]` creates the groups
  `build`, `large`, `medium` and `small` with the given numbers of parallel
  jobs (default 2 each, that is at most 2 x 16G + 2 x 12G + 2 x 8G + 2 x 4G =
  80G of caps), and the group `gpu` with one. Do not raise them at runtime: on 2026-10-16 the
  machine died with build and medium set to 5.

## Setup

```sh
nix profile install nixpkgs#pueue        # or any other pueue install
systemd-run --user --unit=pueued -p Restart=on-failure "$(command -v pueued)"
bin/heavy-setup 4 3 2
```

Choose the parallel numbers so that the sum of the caps stays below the memory
that the machine can lose. The sum can go above it when the jobs seldom reach
their caps at the same time: the defaults give 96 GB of caps on a machine with
94 GB.

## Why caps and not current use

Admission counts caps, because the caps are the hard limits: if every running
job reaches its cap at once, the sum of the caps is still within the budget.
Current use is not a safe measure, because a build's memory grows during the
build. To run more jobs at once, lower the caps to what the jobs need: the
recorded peaks show it.

## Requirements

Linux with cgroup v2 and systemd user sessions, bash, pueue 4, jq, and GNU
coreutils `timeout`.
