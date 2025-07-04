# Veritas – короткая памятка

> **Всего пять элементов: 3 атома + 2 закона.** Поняв их, вы понимаете всю систему — и философию, и код, и CLI.

| Группа | Элемент | Роль | Как выглядит в `veritas.yml` |
|--------|---------|------|--------------------------------|
| **А-томы** | **Claim** (утверждение) | Что мы хотим, чтобы было верно | `claims:\n  - Landauer\n  - "Модель v2 > v1"` |
| | **Evidence** (свидетельство) | Файл, подтверждающий Claim | `artifacts:\n  - path: proofs/Landauer.lean\n    claim: Landauer` |
| | **Check** (проверка) | Процедура, которая связывает Evidence ↔ Claim | `plugins:\n  - lean_compile` |
| **Законы** | **Явная связь** | *Нет файла без Claim, нет Claim без файла.* Вернуться ошибку при нарушении. | Проверяется парсером YAML |
| | **Непрерывный аудит** | *Каждый коммит → все Checks, затронутые diff.* | `veritas check` или GitHub Action |

---

## Почему этого достаточно

* Любой проект сводится к графу `Claim ↔ Evidence`, проверка — проход по рёбрам-Checks.
* Расширяемость = ещё один Check-плагин; атомы и законы неизменны.
* `veritas.yml` — само Evidence для Claim «проект структурирован» и валидируется Check-ом `jsonschema_validate`.

---

## Минимальный исполнимый каркас (≈ 120 LOC)

```python
# veritas.py
import subprocess, yaml, pathlib, sys

OPS = {
    "produce": lambda step: subprocess.check_call(step["cmd"].split()),
    "assert":  lambda step: subprocess.check_call(step["cmd"].split()),
    "observe": lambda step: print(f'[metric] {step["name"]} → {step["value"]}')
}

def run(cfg="veritas.yml"):
    data = yaml.safe_load(open(cfg))
    # --- закон явной связи ---
    for art in data.get("artifacts", []):
        assert "claim" in art, f"{art['path']} не связан с claim"
    # --- исполнение ---
    for op in ("produce", "assert", "observe"):
        for step in data.get(op, []):
            OPS[op](step)

if __name__ == "__main__":
    run(*sys.argv[1:] or [])
```

---

## Пример проекта из 4 строк YAML

```yaml
claims: [Landauer]
artifacts:
  - path: proofs/Landauer.lean
    claim: Landauer
produce:
  - {cmd: "bash build_fig1.sh"}
assert:
  - {cmd: "lean --make proofs/Landauer.lean"}
observe:
  - {name: "fig1.png-hash", value: "sha256:…"}
```

---

## KPI простоты

| Цель | Проверка |
|------|-----------|
| ⏱️ Порог входа ≤ 10 мин | Новый пользователь запускает шаблон и получает зелёный чек за ≤ 600 сек. |
| 📄 Весь API = 1 A4 | README-cheatsheet содержит все ключевые поля YAML и CLI-команды. |
| 🔌 Плагин ≤ 50 LOC | Пример: `R_knitr.py` — новый Check для отчёта R-Markdown. |

---

### Что поменялось по сравнению с черновиками

1. Слили идеи produce/assert/observe и Claim/Evidence/Check.
2. Уронили уровни сложности до одного файла YAML и одного файла Python.
3. Убрали уровни Bronze/Silver — строгие законы сами по себе.

---

## Как начать

```bash
pip install veritas-min
veritas-init myproj
cd myproj && git init
python veritas.py            # зелёный чек
``` 