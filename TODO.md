# Veritas Core · TODO Roadmap

> High-level tasks to reach v0.2 “incremental”. The list is living – update as items are completed.

## ☐ Incremental cache
- Implement optional `.veritas_cache` file – skip edge execution when boundary hash unchanged.
- Hash helper exposed via `veritas.vertex.engine._edge_hash()`.

## ☐ Edge hash API
- Provide public util in `plugin_api` for plugins to override/custom hash.
- Document in `docs/api/plugins.md`.

## ☐ Raise test coverage (> 80 %)
- Add tests for `_util.render_stats` pretty/template branches.
- Exercise `env_gen.generate_dockerfile/conda_yaml` with various requirements.
- Cover CLI `attest`, `status`, `ask` flags.

## ☐ env_gen enhancements
- Detect `pyproject.toml` / poetry sections for dependencies.
- Allow `veritas env --python 3.12` flag to change base image.

## ☐ Bus & plugin docs
- New section **docs/bus_plugins.md** describing event lifecycle and best practices.

## ☐ wheel_not_bloated plugin
- Plugin fails if built wheel > 50 KB.
- Ship under optional extra `plugins`.

---
Feel free to pick a task, open a PR and tick the box ☑️. 