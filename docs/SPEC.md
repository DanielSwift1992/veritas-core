# Veritas Contract Graph – Specification (schema = 1)

> Status: **Stable / v1.0** – canonical specification used by the reference implementation.  
> JSON-Schema: see `docs/schema-1.json`.  
> Approved by: steering committee, 2025-07-10.

---

## 1 · Purpose

The file `logic-graph.yml` is the **single source-of-truth** that describes every
N-E-C contract in a repository:

* **N – Node** – the _nodes_ table, each evidence / claim boundary.
* **E – Edge** – the _edges_ list, a directed obligation `from → to`.
* **C – Check** – the plugin that attests the obligation.

The core engine consumes this graph (_schema = 1_), executes every obligation
via a plugin, and produces a **Trust-stamp** if all checks succeed.

---

## 2 · Top-level Structure

```yaml
schema: 1                 # required – constant 1
generated: "2025-07-04T12:34:56Z"  # optional – ISO 8601 timestamp or "auto-scan"

nodes:    # list<Node>
edges:    # list<Edge>
```

### 2.1 Node

| Field     | Type | Required | Description |
|-----------|------|----------|-------------|
| `id`      | str  | ✓        | Globally unique identifier (stable across renames). |
| `type`    | str  | ✓        | One of `evidence`, `claim`, `contract`. |
| `boundary`| str  | –        | Relative path (file/dir) that the node represents. |
| `meta`    | dict | –        | Arbitrary extra data reserved for plugins. |

### 2.2 Edge

| Field         | Type | Required | Description |
|---------------|------|----------|-------------|
| `from`        | str  | ✓        | Source node `id`. |
| `to`          | str  | ✓        | Target node `id`. |
| `obligation`  | str  | ✓        | Name of a **check plugin** (e.g. `file_exists`, `pytest`). |
| `meta`        | dict | –        | Arbitrary data passed verbatim to plugin. |
#### 2.3 Meta Canonicalization

`meta` MUST be JSON-serializable. To ensure deterministic hashing and reproducible runs:

- Floating-point values are **forbidden** in `meta`. Use strings with fixed precision (e.g. "1.2345") or integer encodings.
- Dictionaries are canonicalized by sorting keys; arrays preserve order.
- Plugins SHOULD treat `cfg` deterministically and avoid reading ambient state.


### 2.0 Plugins

Optional list of extra plugin packages to import before discovery.

```yaml
plugins:
  - ./my_checks     # local directory containing __init__.py with @plugin decorators
  - acme-checks     # already installed PyPI distribution
```

If a string starts with `./` or `../` it is treated as a relative path; otherwise it is imported as-is.

---

## 3 · Graph Invariants

1. **Uniqueness** – every `nodes[*].id` is unique.
2. **Referential integrity** – `edges[*].from` and `edges[*].to` MUST reference existing node ids.
3. **Orphans** – nodes that are never referenced by any edge are reported as warnings and mark the run as *failed* (engine's `orphan-lint`).
4. **Cycles** – cycles are disallowed and cause failure, except **self-edges** (`from == to`) which are explicitly **allowed** to express reflexive obligations (evidence self-check). Execution MAY be parallelized across independent levels of the DAG; the final status is computed only after all scheduled checks finish. Edges skipped due to fail-fast are reported in the summary as `skipped`.
5. **Determinism** – identical graphs (after key-ordering) must yield identical `whole.lock` trust-stamps.

---
## MDR: Flow + Dissipation

MDR is the core trust invariant in Veritas: every obligation (flow) must be checked, and dissipation (cycles, entropy) must be controlled. For the full theory and mathematical background, see [docs/MDR.md](MDR.md).

- **Flow**: Each edge in the graph is a flow of obligation (promise, check).
- **Dissipation**: The core and plugins can implement dissipation control (e.g., cycles, self-checks, `radius_tracker`).
- MDR is the minimal set of invariants for trust: the engine guarantees all flows are checked and dissipation is controlled.

---
## MDR API in the Core

- `extract_subgraph(graph, uid, depth)`: returns a subgraph for navigation/extensions (used by kb).
- `mdr_dissipation`: built-in plugin, checks for absence of cycles (dissipation=0).

---

## 4 · Minimal JSON-Schema (excerpt)

```jsonc
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "Veritas logic-graph schema-1",
  "type": "object",
  "required": ["schema", "nodes", "edges"],
  "properties": {
    "schema": { "const": 1 },
    "generated": { "type": "string" },
    "nodes": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["id", "type"],
        "properties": {
          "id": { "type": "string", "pattern": "^[A-Za-z0-9_./-]+$" },
          "type": { "enum": ["evidence", "claim", "contract"] },
          "boundary": { "type": "string" },
          "meta": { "type": "object" }
        },
        "additionalProperties": false
      }
    },
    "edges": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["from", "to", "obligation"],
        "properties": {
          "from": { "type": "string" },
          "to": { "type": "string" },
          "obligation": { "type": "string" },
          "meta": { "type": "object" }
        },
        "additionalProperties": false
      }
    }
  },
  "additionalProperties": false
}
```

---

## 5 · Example

```yaml
schema: 1
generated: auto-scan

nodes:
  - id: artifact__code
    type: evidence
    boundary: artifact/code
  - id: artifact__proofs
    type: evidence
    boundary: artifact/proofs

edges:
  - from: artifact__code
    to: artifact__code
    obligation: file_exists
  - from: artifact__proofs
    to: artifact__proofs
    obligation: file_exists
  - from: artifact__code
    to: artifact__proofs
    obligation: mdr_dissipation
```

---

## 6 · Versioning Policy

* The **major** number of `schema` increases on breaking changes.
* Fields may be added in a **minor** release if they are optional and guarded by `additionalProperties: false`.
* Deprecations must live for ≥1 minor release before removal.

---

## 7 · Open Governance

Evolution of the specification is tracked via **VEP** (Veritas Enhancement Proposal) documents stored in `docs/vep/` and decided by the steering committee (≤ 5 members). The reference implementation (this repo) MUST stay compatible with the canonical JSON-Schema. 