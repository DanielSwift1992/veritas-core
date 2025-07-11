# MDR: Minimal Dissipative Reasoning

Minimal Dissipative Reasoning (MDR) is the core trust invariant in Veritas Core. MDR ensures that every obligation (flow) in a contract graph is checked, and that dissipation (loss or dispersion of trust, e.g., cycles or entropy) is controlled.

---

## 1. What is MDR?

MDR is a principle for contract graphs: **all declared obligations must be verifiable, and the system must prevent uncontrolled accumulation of uncertainty or risk**. In graph terms, this means:
- **Flow:** Obligations propagate as directed edges in the graph.
- **Dissipation:** Trust can be lost or dispersed through cycles, orphans, or entropy in the graph structure.

A system is MDR-compliant if it checks all flows and controls dissipation.

---

## 2. Mathematical/Graph-theoretic Formulation

- **Flow:** Each edge in the graph represents an obligation (promise, check) from one node to another.
- **Dissipation:** Measured by the presence of cycles, orphan nodes, or high graph entropy.
- **MDR Invariant:**
  - The graph must be acyclic (except for allowed self-edges).
  - All nodes must be referenced by at least one edge (no orphans).
  - The system must be able to compute a deterministic trust-stamp (whole-hash) for the graph.

Formally:
- For all nodes n, there exists a path of obligations to n (no orphans).
- For all cycles C in the graph, C must be explicitly allowed (e.g., self-checks only).
- The trust-stamp is a function of the canonicalized graph structure.

---

## 3. Why MDR?

MDR is the minimal invariant for trust in contract graphs:
- It guarantees that every promise is checked (no hidden obligations).
- It prevents the system from accumulating unbounded risk or uncertainty (no uncontrolled cycles or orphans).
- It enables reproducibility and auditability (deterministic trust-stamp).

---

## 4. MDR in Veritas Core

- **Engine:** Enforces MDR by checking for cycles, orphans, and determinism during `veritas check`.
- **Plugins:** The built-in `mdr_dissipation` plugin checks for cycles (dissipation > 0 → FAIL).
- **Graph API:** The `extract_subgraph` function allows analysis of flows and dissipation in any subgraph.
- **Stats:** The `ripple_score` metric quantifies the reach of obligations from a root node.

---

## 5. Extending MDR in Plugins/Knowledge-base

- Write plugins that check for custom MDR invariants (e.g., entropy, risk thresholds, domain-specific dissipation).
- Use `extract_subgraph` to analyze local MDR compliance in subgraphs.
- Compose MDR checks with other plugins for layered trust models.

---

## 6. References

- [Veritas Core Specification](SPEC.md)
- [NetworkX: Graph Theory in Python](https://networkx.org/)
- [Minimality in OSS Core Design](https://typer.tiangolo.com/)
- [Graph Entropy and Trust](https://en.wikipedia.org/wiki/Graph_entropy) 