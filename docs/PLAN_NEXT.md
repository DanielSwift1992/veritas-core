# Veritas – эволюция к минимальному и расширяемому ядру

(черновик предложения; основан на обсуждении 2025-07-04)

## TL;DR

У нас уже есть рабочий MVP.  Цель следующего цикла — превратить его в элегантное _минимальное ядро_, которое подключается одной командой и остаётся расширяемым благодаря плагинам и строгой спецификации.

---

## 1 · Четыре неизменяемых абстракции

| Слой | Роль | Модуль | Изменчивость |
|------|------|---------|--------------|
| **Model** | Парсит `veritas.yml` → объекты (`Concept`, `Artifact`, `Check`) | `veritas.model` | 🟢 (только при смене schema) |
| **Collector** | Скани-рует исходники, размечает STATUS-теги, строит граф | `veritas.collect` | 🟡 |
| **Executor** | Запускает плагины параллельно, кеширует | `veritas.run` | 🟠 |
| **Reporter** | Выводит Markdown / JSON / HTML / badge | `veritas.report` | 🟠 |

---

## 2 · `veritas.yml` v2 (строгая схема + auto-scan)

```yaml
meta:
  schema: 2
  roots:
    proofs: artifact/proofs
    code  : artifact/code
defaults:
  ".py": pytest
  ".lean": lean_compile
concepts: [Landauer, NavierStokes]
artifacts:
  - path: artifact/code/physics/landauer.py
    concept: Landauer
    role: demo
  - path: artifact/proofs/EnergyBalance.lean
    concept: Landauer
    role: proof
reports:
  - markdown_table: README.md
```

* JSON-Schema публикуется вместе с ядром.
* `veritas scan` генерирует первичный YAML.

---

## 3 · Плагины

* Встроенный набор сведен к `file_exists`.
* Остальные → отдельные пакеты (`veritas-pytest`, `veritas-lean`, …).
* Сигнатура `run(self, artifact: Path, *, cfg: Dict) -> CheckResult`.
* Параллелизм через `asyncio` + семафор.
* Кеш `.veritas/cache.json` (хэш содержимого + имя check).

---

## 4 · CLI UX

```
veritas init            # cookiecutter + badge
veritas scan            # auto-yaml
veritas check           # бывший build.sh
veritas status --readme # обновить таблицу
veritas plugin list
```

`build.sh` уходит из корня; CI вызывает `veritas check`.

---

## 5 · Документация и «красота»

| Слой | MVP | Nice-to-have |
|------|-----|--------------|
| Docs | `mkdocs-material` | Binder-примеры, DAG-визуализация |
| Demo | README gif | live-badge |
| VSCode | syntax highlight STATUS | панель проблем |

---

## 6 · Миграция текущего репозитория

1. `pip install veritas-core==0.9`
2. `veritas scan` → v2 YAML.
3. В CI заменить `build.sh` на `veritas check`.
4. Подключить плагины (`veritas-lean`, `veritas-pytest`).

~30 минут работы.

---

## 7 · Open Governance & Spec

* `SPEC.md` + JSON-Schema.
* VEP (Veritas Enhancement Proposal) процесс.
* Steering-Committee ≤ 5 человек.
* SemVer строго соблюдается.
* Подписи релизов, SBOM, sigstore. 