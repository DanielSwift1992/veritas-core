# Evidence Matrix: From Kernel Properties to Quantifiable ROI

*This document captures the cause-and-effect chain from low-level design choices in the Δ-Kernel up to board-level business outcomes.  Copy-paste any section into a white-paper, landing page or investor deck as needed.*

---

## 1  Kernel properties → systemic advantages

| Property of the Δ-Kernel & vertex engine                             | Immediate consequence                                    | Strategic leverage                                  |
| -------------------------------------------------------------------- | -------------------------------------------------------- | --------------------------------------------------- |
| *Acyclic, hash-addressed N-E-C graph*                                | one-line **Whole-stamp** proves *nothing hidden changed* | cryptographic audit trail & reproducible builds     |
| *Checks are pure functions*<br>(no mutation, only boolean result)    | results can be cached, parallelised, memoised            | linear → sub-linear CI times when the repo grows    |
| *Plugins loaded via entry-points*                                    | any team can write its own checks in 30 lines            | domain experts extend Veritas without touching core |
| *Graph file is regular YAML*                                         | editable in any IDE, diff-friendly                       | can be code-reviewed like source; no vendor lock-in |
| *"Tuning completeness"* (add as much or as little edges as you like) | zero-friction incremental rollout                        | maturity model for adoption programmes              |

---

## 2  Role-centred use-cases & outcome KPIs

| Role / job-to-be-done                                                            | Typical plugin mix (starter pack)                                          | Pain today                                          | KPI after Veritas                                                                                                |
| -------------------------------------------------------------------------------- | -------------------------------------------------------------------------- | --------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------- |
| **System / Solution Architect**<br>"My architecture diagram must stay true."     | • `forbidden_import`  • `openapi_spec_valid`  • `dockerfile_best_practice` | Docs drift, late discovery of dependency violations | *Mean time-to-violation-detect* ↓ from days ➜ minutes<br>*On-boarding time* ↓ 30 % (new hire runs `veritas ask`) |
| **DevOps / SRE**<br>"Pipelines should be declarative and portable."              | • `pytest`  • `bandit`  • `sbom_up_to_date`  • `trivy_scan`                | 2-3 parallel CI script dialects, flaky jobs         | *.gitlab-ci.yml* LoC ↓ > 90 %<br>*Time-to-green* ↓ 25–50 % (selective re-runs)                                   |
| **Security / Compliance Officer**<br>"Prove GDPR & SOC-2 controls continuously." | • `check_encryption`  • `iam_policy_least_priv`  • `data_retention_window` | Spreadsheet audits, point-in-time evidence          | *Audit prep time* ↓ ×10<br>*Control coverage* ↑ to 100 % (each requirement = node)                               |
| **Product Manager / CTO**<br>"I need a live risk & progress dashboard."          | same graph + `kpi_target_met` obligations                                  | Blind spots until after release                     | *Lead-time from spec to proof* compressed; live "trust-stamp" visible to stakeholders                            |
| **Data-science Lead**<br>"My model pipeline must be reproducible."               | • `mlflow_model_exists`  • `dataset_version_pin`  • `notebook_execute`     | "works on my GPU", undetected data drift            | *Re-run success rate* → 100 %<br>*Drift detection latency* ↓ from weeks ➜ hours                                  |

*(Add or drop rows to match the persona set you care about.)*

---

## 3  Demonstration blueprint ("proof-of-value" repo)

```text
veritas-demo/
├─ services/            # tiny micro-service dummy
├─ infra/               # terraform sample
├─ ml/                  # notebook + model.pkl
├─ logic-graph.yml      # ≈ 40 nodes / 80 edges
└─ README.md            # scenario description
```

1. **Commit A** – deliberately break two obligations (e.g. outdated OpenAPI file, failing notebook).
2. Run **baseline** CI:

   ```bash
   time ./scripts/legacy_ci.sh     # ~4–5 min, all passes "green" because gaps invisible
   ```
3. **Switch branch** that introduces `veritas check` in pipeline.
4. Observe:

   ```bash
   veritas check --stats
   CHECKS PASSED=78 FAILED=2
   # Whole-stamp not produced
   ```
5. Fix the two files ⇒ next run green, `whole.lock` appears.

Metrics above (build time, failure latency, LoC reduction) are now *observable*.

---

## 4  How to measure & publish the gains

| Step                                  | Tooling snippet                                                       |
| ------------------------------------- | --------------------------------------------------------------------- |
| **1. Collect timings** per obligation | `veritas check --profile --json > run.json`                           |
| **2. Diff CI-script size**            | `wc -l .gitlab-ci.yml before/ after/`                                 |
| **3. Track onboarding**               | onboarding script logs wall-clock until first green `veritas check`   |
| **4. Continuous audit bundle**        | `veritas attest --dest artefact_$(git rev-parse --short HEAD).tar.gz` |

A single **navigation list** on the project wiki can then link each metric to its JSON evidence bundle.

---

## 5  Next-level automation ideas (road-map)

1. **`veritas measure`** – CLI sub-command that commits every `--profile` JSON to `metrics/`, giving an auto-generated performance dashboard over time.
2. **Graph visualiser plugin** – emits an interactive SVG or Mermaid diagram for `veritas ask --viz`, improving stakeholder communication.
3. **Selective re-run engine** – uses graph-diffing to execute only obligations impacted by changed nodes (cuts CI time further).

All three can be implemented **outside the core**—perfect dog-food examples of the plugin interface.

---

### Take-away

*Veritas* does **one thing** in the kernel—prove that every declared promise currently holds—and does it so primitively that you can layer *any* domain-specific proof on top.
That minimalism is precisely what lets you **attach hard metrics** for architects, operators, and executives, moving the conversation from "nice idea" to *measurable ROI*. 