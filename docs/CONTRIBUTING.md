# Contributing to Veritas

Thank you for considering a contribution! Veritas follows a lightweight **VEP (Veritas Enhancement Proposal)** workflow for any change that touches the public contract graph schema or plugin interface.

## Quick start

1. Fork & clone the repo, create a feature branch.
2. Run `./build.sh` – ensure baseline passes.
3. Make your changes & add tests.
4. `pre-commit run -a` to satisfy linters.
5. Open a PR.

## VEP process

1. Copy `docs/vep/vep-0000.md` → `docs/vep/vep-XXXX-my-title.md`.
2. Fill in all sections; open a PR labelled `VEP`.
3. Steering committee reviews → status moves Draft → Accepted → Final.
4. Once Accepted, implement in core and bump `schema` minor/major as needed.

Non-schema bug-fixes and docs improvements can skip VEP.

## Code style

* Python ≥ 3.10, `ruff` + `black`.
* Keep core lean: avoid heavy deps; new checks should live in plugins.

## Licence

By contributing you agree your work is licensed under MIT, same as project. 