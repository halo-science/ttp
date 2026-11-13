# Отчёт о машинной верификации и аудите аксиом TTP

**Дата:** 2026-11-14 00:44  
**Репозиторий:** `D:\___Work\TTP` (сборочный стенд: `~/ttp` в WSL Ubuntu 24.04)  
**Коммит:** `00461a1b9f216d71fe764e6d4a5fddbf484abeaf`

## Окружение

| Параметр | Значение |
|---|---|
| Lean | `4.35.0` (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) |
| Lake | `5.0.0-src+eb6cafb` |
| Toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | `v4.35.0` |
| Модулей `TTP/` | 12 |
| `sorry` в исходниках | 0 |

## 1. Сборка

Команда: `lake build` (в `~/ttp`, после синхронизации из `D:\___Work\TTP`).

```text
Build completed successfully (2924 jobs).
```

## 2. Аудит аксиом (`#print axioms`)

Команда: `lake env lean /tmp/axioms_audit.lean` (импорт `TTP`, все 12 модулей).

```text
'TTP.crystal_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.prime_of_sieve_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.sieve_exact_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.phase_step_homomorphism' depends on axioms: [propext, Quot.sound]
'TTP.cyclotomicEvalOne_eq_one_iff_vonMangoldt_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.sieve_nilpotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.memoryJ_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.CMI_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.properTimeDefect_eq_zero_of_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.torusGram_cholesky_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.ramanujanWaveUnitInterval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.stormer_resonance_13090' depends on axioms: [propext]
'TTP.dyadic_center_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.purePrimeProjectorPower_eq_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'TTP.dualAdder_eq_mod' depends on axioms: [propext, Quot.sound]
```

## 3. Сводная таблица

| № | Теорема | Модуль | Аксиомы | `sorryAx` |
|---:|---|---|---|---|
| 1 | `crystal_coprime` | `TTP/Definitions.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 2 | `prime_of_sieve_horizon` | `TTP/ExactSieve.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 3 | `sieve_exact_identity` | `TTP/ExactSieve.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 4 | `phase_step_homomorphism` | `TTP/PhaseDiode.lean` | `propext, Quot.sound` | нет |
| 5 | `cyclotomicEvalOne_eq_one_iff_vonMangoldt_eq_zero` | `TTP/ChordCharge.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 6 | `sieve_nilpotent` | `TTP/SieveNilpotence.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 7 | `memoryJ_bounds` | `TTP/MemoryKernel.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 8 | `CMI_three` | `TTP/MemoryKernel.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 9 | `properTimeDefect_eq_zero_of_horizon` | `TTP/ProperTimeWhitening.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 10 | `torusGram_cholesky_factorization` | `TTP/CholeskyRamanujan.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 11 | `ramanujanWaveUnitInterval_eq_zero` | `TTP/FunctionFieldBridge.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 12 | `stormer_resonance_13090` | `TTP/ToroidalMetricsAndRNS.lean` | `propext` | нет |
| 13 | `dyadic_center_coprime` | `TTP/ToroidalMetricsAndRNS.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 14 | `purePrimeProjectorPower_eq_delta` | `TTP/ToroidalMetricsAndRNS.lean` | `propext, Classical.choice, Quot.sound` | нет |
| 15 | `dualAdder_eq_mod` | `TTP/ToroidalMetricsAndRNS.lean` | `propext, Quot.sound` | нет |

## 4. Вывод

- Все 15 ключевых теорем успешно проверены ядром Lean 4.
- В списках аксиом присутствуют только стандартные аксиомы Lean/Mathlib:
  `propext`, `Classical.choice`, `Quot.sound` (у `stormer_resonance_13090` — только `propext`).
- **`sorryAx` отсутствует** во всех проверенных теоремах; в исходниках `TTP/*.lean` нет `sorry`.
- `Lean.ofReduceBool` отсутствует: в доказательствах используется `decide`/`norm_num`, а не `native_decide`.
- Сборка: `BUILD_EXIT=0`, `2924 jobs`, `WARNINGS=0`, `ERRORS=0`.

### Воспроизведение

```bash
cd ~/ttp
lake build
cat > /tmp/axioms_audit.lean <<EOF
import TTP
#print axioms TTP.crystal_coprime
#print axioms TTP.prime_of_sieve_horizon
...
EOF
lake env lean /tmp/axioms_audit.lean
```

