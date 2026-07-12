# divisionAssoc multi-core determinism probe (diagnostic branch — do NOT merge)

Reproduces and localizes an intermittent crash: under the multi-core prover, the nonlinear-arith
proof `divisionAssoc.key` occasionally trips the `BackTrackingManager` determinism guard
(`assertValidTicket`) — a worker `AssertionError` that the RunAllProofs harness otherwise swallows
into a "proof did not close". This branch instruments that guard to dump a `[BTDIV]` line naming
the *diverging choice point*, and adds a gradle task that hammers the proof and survives each crash
so it reports a rate plus samples.

## Run on a Linux box (best: many cores, and put the box under load)

    ./gradlew :key.core:divergenceProbe

Tune (defaults: workers 4,8,12; 1200 reps per worker count):

    ./gradlew :key.core:divergenceProbe -PprobeWorkers=4,8,12 -PprobeReps=3000

The crash is low-rate and timing-sensitive: it shows up under scheduler contention (busy multi-core
Linux runner), and may need thousands of reps on an idle machine. To force contention, run the box
busy in parallel, e.g. in another shell:

    for i in $(seq 1 $(nproc)); do yes > /dev/null & done      # saturate cores
    # ... run the probe ...
    kill %1 2>/dev/null; pkill yes                              # stop the load afterwards

Requires JDK 21 (match CI); `enableAssertions` is set by the task.

## Reading the output (console — `DIVP` / `BTDIV` lines)

    DIVP | probe: proof=... workers=[4, 8, 12] reps/worker=1200
    DIVP | SC baseline: closed=true canonNodes=816 rootDigest=...
    DIVP | CRASH at 8w#137: java.lang.AssertionError @ ...BackTrackingManager.assertValidTicket(...)
    [BTDIV] position=<n> expected=<ChoicePointClass>@<id> actual=<ChoicePointClass>@<id> initialApp=<rule> seq=...
    DIVP | SUMMARY: <d> diverged, <c> crashed / <N> runs   (0/0 = not reproduced here)

- `SUMMARY` with `crashed > 0` → reproduced; the `[BTDIV]` lines above it name the choice point that
  differed between two evaluations of the same feature term (the non-deterministic decision to trace).
- `DIVERGENCE` (as opposed to `CRASH`) → a run closed via a *different* proof tree than single-core
  (or did not close) without crashing — also a determinism finding; the first differing node is printed.
- `0 diverged, 0 crashed` → not reproduced in this run (raise `-PprobeReps`, add load, or use more cores).

Please capture the full console output (especially every `[BTDIV]` line) and send it back.
