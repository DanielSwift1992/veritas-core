# Veritas Contract Graph – Specification (schema = 4)

> Status: **Draft / v0.1** – minimal guarantees sufficient for the reference Δ-Kernel demo.  
> Approved by: core maintainers on 2025-07-04.  
> See also: `docs/BRAND.md`, `docs/CHEATSHEET.md`, `docs/PLAN_NEXT.md`.

---

## 1 · Purpose

The file `logic-graph.yml` is the **single source-of-truth** that describes every
_K-П-С_ contract in a repository:

* **K** (Kонтекст) – _nodes_ table – each evidence/claim boundary.
* **П** (Переход) – _edges_ list – a directed obligation from `from → to`.
* **С** (Свидетельство) – plugin check that attests the obligation.

The core engine consumes this graph (_schema = 4_), executes every obligation
via a plugin, and produces a **Trust-stamp** if all checks succeed.

---

## 2 · Top-level Structure

```yaml
schema: 4                 # required – constant 4
generated: "2025-07-04T12:34:56Z"  # optional – ISO 8601 timestamp or "auto-scan"

nodes:    # list<Node>
edges:    # list<Edge>
```

### 2.1 Node

| Field     | Type | Required | Description |
|-----------|------|----------|-------------|
| `id`      | str  | ✔︎ | Globally unique identifier (stable across renames). |
| `type`    | str  | ✔︎ | One of `evidence`, `claim`, `contract`. |
| `boundary`| str  | – | Relative path (file/dir) that the node represents. |
| `meta`    | dict | – | Arbitrary extra data reserved for plugins. |

### 2.2 Edge

| Field         | Type | Required | Description |
|---------------|------|----------|-------------|
| `from`        | str  | ✔︎ | Source node `id`. |
| `to`          | str  | ✔︎ | Target node `id`. |
| `obligation`  | str  | ✔︎ | Name of a **check plugin** (e.g. `file_exists`, `pytest`). |
| `meta`        | dict | – | Arbitrary data passed verbatim to plugin. |

---

## 3 · Graph Invariants

1. **Uniqueness** – every `nodes[*].id` is unique.
2. **Referential integrity** – `edges[*].from` and `edges[*].to` MUST reference
   existing node ids.
3. **Orphans** – nodes that are never referenced by any edge are reported as
   warnings and mark the run as *failed* (engine's `orphan-lint`).
4. **Cycles** – cycles are disallowed and cause failure, except **self-edges**
   (`from == to`) which are explicitly **allowed** to express reflexive
   obligations (evidence self-check).
5. **Determinism** – identical graphs (after key-ordering) must yield identical
   `whole.lock` trust-stamps.

---

## 4 · Minimal JSON-Schema (excerpt)

```jsonc
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "Veritas logic-graph schema-4",
  "type": "object",
  "required": ["schema", "nodes", "edges"],
  "properties": {
    "schema": { "const": 4 },
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
schema: 4
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
    obligation: lean_compile
```

---

## 6 · Versioning Policy

* The **major** number of `schema` increases on breaking changes.
* Fields may be added in a **minor** release if they are optional and guarded
  by `additionalProperties: false`.
* Deprecations must live for ≥1 minor release before removal.

---

## 7 · Open Governance

Evolution of the specification is tracked via **VEP** (Veritas Enhancement
Proposal) documents stored in `docs/vep/` and decided by the steering
committee (≤ 5 members).  The reference implementation (this repo) MUST stay
compatible with the canonical JSON-Schema. 