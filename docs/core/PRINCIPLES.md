# Veritas Core Principles (`PRINCIPLES.md`)

> These invariants are **immutable** – any edit needs a super-majority of the Board.  
> Threshold numbers (*H*, *R*, quora …) live in project configs & playbooks, **never here**.

---

## P-0 · Principle of Computable Intent

Any human intention that **claims truth about the system** **must** be externalised as a contract Veritas can evaluate to **PASS/FAIL**.

```text
∀ intent i_h, ∃ edge e ∈ E :   check(e)=passed  ⇔  i_h valid
````

> Logic becomes a first-class citizen.  The next five invariants (P-1 … P-5) keep those contracts ownable, consensual, auditable, reversible and power-balanced.

---

## P-Table – Five Binary Invariants

| №       | Name                           | Human phrasing                                                                                                                    | Binary test                                           | Why it never gets old                                                                      |
| ------- | ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------- | ------------------------------------------------------------------------------------------ |
| **P-1** | **Explicit Boundary**          | Every artefact has **exactly one accountable entity** (a person *or* a named group) **and** appears in ≥ 1 declared relationship. | `∀ v ∈ V: ∃! owner(v) ∧ ∃ e (e.from=v ∨ e.to=v)`      | Stewardship needs an owner; isolation breeds rot.                                          |
| **P-2** | **Verifiable Consent**         | Crossing someone else’s boundary demands an explicit **YES/NO** recorded in the log.                                              | `crossing(Δ,v) ∧ owner(Δ)≠owner(v) ⇒ human_vote(v)=✓` | Unrecorded consent is just a rumour.                                                       |
| **P-3** | **Audit Trail**                | No decision without an immutable record, sufficient for replay.                                                                   | every `check(e)` → `append⟨ts,edge,input,result⟩`     | An unrecorded history is an indefensible one.                                              |
| **P-4** | **Two-Way Door Invariant**     | Act autonomously only if **rollback ≤ H** *and* **blast-radius ≤ R**.                                                             | `rollback_cost≤H ∧ impact≤R ⇒ self-go`                | Autonomy without a safety-check is just recklessness.                                      |
| **P-5** | **Accountability = Authority** | If entity *H* bears responsibility *R*, it receives the **minimal** set of powers *A* required to fulfil *R*.                     | `responsible(H,R) ⇒ authorised(H, Path(R))`           | Authority without accountability is tyranny; accountability without authority is sabotage. |

---

## 2 · Why five are enough

1. **Completeness** – together they span ownership, consent, traceability, autonomy and power balance.
2. **Orthogonality** – principles overlap minimally, removing ambiguity.
3. **Minimality** – drop one → blind spot; add more → derivable duplicate.

---

## 3 · Deriving micro-rules

| Micro-rule                                          | Expressed as         |
| --------------------------------------------------- | -------------------- |
| **Two-Way Door decision** – “act if rollback < 2 h” | P-4 with `H = 2 h`   |
| **Required LGTM from owner**                        | P-1 + P-2            |
| **Escalate if change > $10 k**                     | P-4 with `R = $10 k` |

See `COOKBOOK.md` for YAML + plugin recipes.

---

## 4 · Human-Focus Ratio (HFR) – proof sketch

$$
\text{HFR} = \frac{I}{I + K + R + D}
$$

* **I** – Intent creation
* **K** – Contract coding
* **R** – Routine execution
* **D** – Disruption diagnostics

LLM assistance drives *K → 0*, Veritas CI drives *R → 0*, immediate edge failure drives *D ≈ 0*; denominator collapses towards *I*, hence **HFR → 1**.
Formal proof outline → `../whitepaper/WHITEPAPER.pdf`.

---

### CI Guard

`make principles-test` must return **TRUE** for all six tests (P-0 … P-5) on the demo graph; the workflow blocks merge otherwise. 