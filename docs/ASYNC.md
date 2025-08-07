## Async execution (level-by-level)

This document describes the parallel execution model in veritas-core. The core guarantees determinism of the final status and trust-stamp while enabling concurrency for independent checks.

### Model
- The contract graph is a directed acyclic graph (DAG) over nodes; self-edges are allowed and do not create dependencies.
- The engine groups nodes into topological generations (levels). All edges whose `from` lies in the same level form a batch.
- Levels are executed sequentially; within a level, checks run in parallel in a thread pool.

### Flags
- `--concurrency {N|auto}`: number of workers per level (default: 1; `auto` = min(32, cpu_count)).
- `--fail-fast`: stop scheduling subsequent levels after the first failure; tasks of the current level finish.
- `--profile`: record per-plugin and per-level times; visible via `--stats`.

### Determinism guarantees
- Plugin outputs are buffered and printed in a stable order based on (level, edge-index). No interleaving.
- The trust-stamp (`whole.lock`) is computed from a canonical JSON of `{nodes, edges}` with sorted keys and is emitted only if all checks succeed. It is independent of `--concurrency`.

### Events (for observers/MCP)
- `graph.built {n_nodes, n_edges}`
- `run.started {concurrency, fail_fast, profile}`
- `edge.started {from, to, obligation, level, index}`
- `edge.finished {from, to, obligation, level, index, ok, details, dt}`
- `summary {checks_passed, checks_failed, timings?}`
- `run.finished {ok, checks_passed, checks_failed, skipped}`
- `whole_hash {hash}` (only on success)

### Error policy
- Any exception in a plugin, unknown plugin, malformed edge, or cycle detection marks the run as failed.
- Orphan nodes are reported and counted as failures.

### Example
```
veritas check --concurrency=auto --profile --stats
```

### Compatibility
- With `--concurrency=1`, behavior is identical to the legacy sequential run (deterministic logs and trust-stamp).


