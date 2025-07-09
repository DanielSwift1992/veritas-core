# Contributing to Veritas

Thank you for considering a contribution – new **promises** and **checks** are our lifeblood.

---

## 1  Philosophy of Contribution

• We value **new verifiable promises** more than sheer LOC.<br>• All contributions flow through the **Loop of Trust** described below.<br>• Humans keep ownership of meaning; machines automate verification.

---

## 2  Loop of Trust (5 steps)

1. **Intention** – you open an Issue/PR describing the new promise.
2. **Translation** – optional LLM assistant generates edge + plugin draft.
3. **Validation** – CI runs `veritas check --dry-run` and posts a report.
4. **Adoption** – a **Curator** reviews & merges (or requests changes / human_vote).
5. **Observation** – metrics & alerts feed back into future intent.

Decision Gates **G0…G3** determine who must review based on `rollback_cost` & `impact` (P-4).

---

## 3  Roles (pick any, mix freely)

| Role | What you do |
| ---- | ------------ |
| **Visionary** | Crafts new meta-goals & invariants |
| **Curator** | Reviews & merges PRs, tends the graph |
| **Arbiter** | Judges contentious FAILs |
| **Plugin Hacker** | Authors custom plugins (any language) |
| **Signal Reviewer** | Provides `human_vote` where subjective judgement is needed |

---

## 4  Workflow Checklist

```text
$ git checkout -b feat/my-promise
$ edit logic-graph.yml  # add edge
$ poetry run veritas check --dry-run      # ensure no regressions
$ git commit -a -m "feat: promise X via bundle_size_max"
$ gh pr create ...                        # open PR
```
> If CI turns **red**, investigate or request an exemption (`human_vote`).

---

## 5  LLM Assistant Guide

• Use the `/veritas-draft` chat-command to generate edge+plugin stubs.<br>• Always review generated code – the Curator *must* sign off.<br>• The assistant never merges code autonomously.

---

## 6  Plugin How-to (40 LoC)

1. Subclass `BaseCheck` and implement `run()` returning `CheckResult`.<br>2. Keep fixtures under `tests/fixtures/`.<br>3. Publish to PyPI with an entry-point under `[project.entry-points."veritas_plugins"]`.<br>4. Add a recipe to `../COOKBOOK.md`.

---

## 7  Style & Tooling

Pre-commit hooks enforce Black, Ruff, and MyPy (strict). Install via:
```bash
pip install -e .[test]
pre-commit install
```

---

### Subjective edges (`human_vote` etc.)

See **PRINCIPLES P-2** and the design in `docs/temp_or_future_human_vote.md` (tbd).  Subjective checks must log *who* and *why* for audit (P-3).

---

`veritas check` on the repo must stay **green** – CI will block otherwise. 