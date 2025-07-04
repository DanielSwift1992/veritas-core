# Veritas – Core Values

These are the principles that guide every commit.  They are intentionally short; if a proposed feature violates any of them, it must be redesigned or dropped.

| # | Value | What it means in practice |
| - | ----- | ------------------------- |
| 1 | **Reproducibility over features** | A fancy integration is useless if it breaks determinism.  We will not merge code that makes builds flaky. |
| 2 | **Language-agnostic** | The core knows nothing about Lean, Python, R, … – everything language-specific lives in plugins. |
| 3 | **Minimal friction** | A new repo should reach a green badge in under 5 minutes.  Defaults must be sensible; YAML should be optional. |
| 4 | **Observable, not magical** | All checks are plain shell commands recorded in logs.  No hidden network calls, no telemetry. |
| 5 | **Opt-in strictness** | Users choose how far they go (Bronze → Gold).  CI should never surprise-fail on a minor update. |
| 6 | **Open governance** | Specs and reference code live under Apache-2.0; design decisions are tracked in public issues. |
| 7 | **Sustainability** | We avoid one-off hacks that will need constant babysitting.  Fewer dependencies, pinned versions, SBOM. | 