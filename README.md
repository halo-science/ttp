# Toroidal Theory of Primes (TTP) in Lean 4

![Lean](https://img.shields.io/badge/Lean-4.35.0-blueviolet)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)
![Build](https://img.shields.io/badge/build-passing-brightgreen)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)

Академическая библиотека формальной математики на Lean 4 / Mathlib: перенос задач
теории решета на праймориальный тор, фильтрация составного шума круговыми полиномами
и бескомпараторная кинематика шага на торе.

---

## Аннотация (RU)

Библиотека **TTP** формализует ядро *Тороидальной теории простых чисел*
(Toroidal Theory of Primes), включая хордово-кумулянтную алгебру
(Chord-Cumulant Algebra) как аппарат гашения составного шума. Основная идея —
заменить деление с остатком и просеивание на интервале арифметикой вычетов
на **праймориальном торе**
`Z / M_k Z`, где `M_k = p_k#` — праймориал первых `k` простых чисел. Составной шум
(диполи, триполи, кубические узлы) гасится тождественно: алгебраически — через
значение кругового полинома `Φ_q(1)` и функцию фон Мангольдта `Λ`, комбинаторно —
через знакопеременный усечённый логарифм решета `𝓛_k`. Три аналитических
направления — ядро памяти Шеннона, обеление собственного времени и факторизация
Холецкого–Рамануджана — вынесены в модули `MemoryKernel`, `ProperTimeWhitening`
и `CholeskyRamanujan`.

Все результаты проверены ядром Lean 4: библиотека собирается с `exit code 0`,
без предупреждений компилятора и без `sorry`.

## Abstract (EN)

**TTP** is a Lean 4 / Mathlib library formalising the algebraic and combinatorial
core of the Toroidal Theory of Primes. Integers are represented as vectors of
residues on a primorial torus `Z / p_k# Z`; composite contributions are annihilated by
cyclotomic evaluation at one (`Φ_q(1)`), by von Mangoldt vanishing (`Λ(q) = 0`), and by
the alternating truncated sieve logarithm `𝓛_k`. Three analytic directions —
the Shannon memory kernel, proper-time whitening, and the Cholesky–Ramanujan
factorization — are developed in `MemoryKernel`, `ProperTimeWhitening`, and
`CholeskyRamanujan`. The development is fully verified:
`lake build` exits with code `0`, zero compiler warnings, zero `sorry`.

---

## 1. Концептуальное введение

Классическое решето Эратосфена работает с целыми числами и делением с остатком.
TTP заменяет эту модель на **геометрию тора**:

1. **Праймориал `p_k#`** — произведение первых `k` простых чисел; он задаёт период
   тора `Z / M_k Z`.
2. **Праймориальный тор** `T_k = Z / M_k Z` по китайской теореме об остатках
   изоморфен прямому произведению `∏_{i≤k} Z / p_i Z`, то есть числу `n`
   сопоставляется вектор вычетов `(n mod p_1, …, n mod p_k)`.
3. **Копрайм-кристалл** `Φ_k* = T_kˣ` — мультипликативная группа обратимых
   элементов тора; её элементы — ровно те вычеты, что взаимно просты с `M_k`.
4. **Составной шум** (числа с `ω(n) ≥ 2` и их степени) должен быть подавлен
   фильтром. В TTP это делается двумя независимыми способами:
   - *алгебраически*: `Φ_q(1) = 1` и `Λ(q) = 0` для всех `q`, не являющихся
     степенью простого;
   - *комбинаторно*: знакопеременная сумма `𝓛_k(n) = Σ_{m=1}^{k} (-1)^{m-1}/m · C_m(n)`
     обращается в ноль для диполей, триполей и кубических узлов.
5. **Фазовый диод** реализует шаг `n ↦ n + Δ` как независимое сложение вычетов
   на каждой оси — без целочисленного деления (DIV) и без заимствований между
   разрядами, что и является вычислительной моделью специализированного
   кремниевого сопроцессора ТТП.

---

## 2. Архитектура модулей

| Модуль | Раздел монографии | Ключевые определения и теоремы |
|---|---|---|
| `TTP/Definitions.lean` | Глава 1 — праймориальный тор | `primorial : ℕ → ℕ`, `PrimorialTorus k := ZMod (primorial k)`, `CoprimeCrystal k := (PrimorialTorus k)ˣ`, `crystal_coprime` |
| `TTP/ChordCharge.lean` | Глава 3 — хордовая алгебра (ХКА) | `cyclotomicEvalOne q := (cyclotomic q ℤ).eval 1`; `cyclotomicEvalOne_prime`, `_prime_pow`, `_of_omega_ge_two`, `_eq_one_iff`, `_eq_one_iff_not_isPrimePow`, `_eq_one_iff_vonMangoldt_eq_zero` |
| `TTP/SieveNilpotence.lean` | Глава 4 — Аксиома IV (конечная нильпотентность) | `IsSieveFactorization B m n L`; `sieve_factorization_pow_le : B^m ≤ n`; `sieve_nilpotent`; `prime_factorization_length_one` |
| `TTP/ExactSieve.lean` | Глава 5.0 — алгебраическое замыкание решета | `squarefree_prime_of_chord_nontrivial`, `prime_of_sieve_horizon`, `sieve_exact_identity` |
| `TTP/PhaseDiode.lean` | Глава 5.1 — оператор фазового диода | `PhaseDiodeOpen p n := (n : ZMod p) ≠ 0`; `phase_diode_open_iff_not_dvd`, `phase_step_homomorphism`, `phase_diode_twin_open` |
| `TTP/CombinatorialSieve.lean` | Глава 5.2 — комбинаторное гашение | `sieveLogOrder1/2/3`; `sieve_log_prime_eq_one`, `sieve_log_prime_sq_eq_half`, `sieve_cancellation_dipole`, `sieve_cancellation_mixed_tripole`, `sieve_cancellation_cubic_node`, `sieve_log_order_embed` |
| `TTP/MemoryKernel.lean` | Направление I — ядро памяти Шеннона | `memoryKernel t`; `memoryKernel_sub_taylorLower`, `taylorUpper_sub_memoryKernel`, `taylorLower_remainder_pos`, `taylorUpper_remainder_pos`, `memoryKernel_taylor_sandwich`; `memoryJLower/Upper`, `memoryJ_bounds`; `CMI`, `CMI_three`; `tail_majorant_split`, `tail_sum_telescope`, `tail_sum_lt` |
| `TTP/ProperTimeWhitening.lean` | Направление II — обеление собственного времени | `PhaseDiodeChain4Open`; `phase_diode_chain4_iff_not_dvd`, `phase_diode_chain4_periodic`, `phase_diode_chain4_two_of_even`; `properTimeDefect`, `properTimeDefect_eq_zero_of_horizon`; `cmi_zero_of_vanishing_kernels`; `cca_composite_channel_annihilation`; `external_cmi_tail_lt` |
| `TTP/CholeskyRamanujan.lean` | Направление III — Холецкий–Рамануджан | `jordanTotient2`, `torusGram`, `choleskyRaw`, `choleskyInvRaw`; `sum_jordanTotient2_divisors`, `jordanTotient2_prime`, `torusGram_cholesky_factorization`, `cholesky_mobius_inversion`, `ramanujan_linear_drift_zero`, `ramanujan_totient_weight`, `torus_coboundary_prime_factor` |
| `TTP.lean` | корень библиотеки | импортирует все модули |

### 2.1. Содержательные формулировки

- **Кристалл (Гл. 1).** Для любого `x : (ZMod (p_k#))ˣ` натуральное значение
  `x.1.val` взаимно просто с праймориалом `p_k#`.
- **Хордовый заряд (Гл. 3).** `Φ_p(1) = p`, `Φ_{p^(k+1)}(1) = p`, а для `ω(q) ≥ 2`
  выполнено `Φ_q(1) = 1`. Более того, при `q > 1`
  `Φ_q(1) = 1 ↔ ¬ IsPrimePow q ↔ Λ(q) = 0`.
- **Нильпотентность (Гл. 4).** Если `n < B^m`, то ситовой факторизации `n` на `m`
  сомножителей, каждый из которых `≥ B`, не существует.
- **Горизонт `B^2` (Гл. 5.0).** Если все простые делители `n` не меньше `B ≥ 2`
  и `n < B^2`, то `n` простое; следовательно `Φ_n(1) = n`.
- **Фазовый диод (Гл. 5.1).** `PhaseDiodeOpen p n ↔ ¬ p ∣ n`, а
  `(n + Δ : ZMod p) = n + Δ` — шаг на торе является гомоморфизмом сложения.
- **Гашение (Гл. 5.2).** `𝓛₂(pq) = 0`, `𝓛₃(p²q) = 0`, `𝓛₃(pqr) = 0`,
  при этом `𝓛₂(p²) = 1/2`, `𝓛₁(p) = 1`.
- **Ядро памяти (Направление I).** `K(t) = (3+t)/((1-t)(1+t)²)` зажато между
  `3-2t` и `3-2t+5t²` при `0 < t ≤ 1/2`; `0 < J_low(r) < J_high(r) < 1/(2r²)`
  при `r ≥ 2`; `CMI(3, p₀) = p₀(1-p₀)²J₁`; хвост
  `∑_{i<N} 1/(2(B+i-2)(B+i-3)) = 1/(2(B-3)) - 1/(2(B+N-3)) < 1/(2(B-3))`
  при `B ≥ 4`, `N ≥ 1`.
- **Обеление собственного времени (Направление II).** 4-точечная цепочка на оси `p`
  открыта ↔ `p` не делит узлы и периодична по `u` с периодом `p`; при чётных сдвигах
  на оси `p = 2` цепочка открыта ↔ `Odd u`; при `2 ≤ B`, `1 ≤ a`, `b ≤ B²`
  дефект `properTimeDefect B a b = 0`; при `ω(q) ≥ 2` выполнено
  `Φ_q(1) = 1 ∧ Λ(q) = 0`; внешний хвост памяти строго `< 1/(2(B-3))`.
- **Холецкий–Рамануджан (Направление III).** `∑_{c∣g} J₂(c) = g²`,
  `J₂(p) = p²-1`; `𝒢_{d₁d₂} = (1/12) ∑_c J₂(c) L_{d₁c} L_{d₂c}`;
  `∑_d L⁻¹_{qd} L_{dc} = δ_{q,c}`; `∑_{d∣q} d·μ(q/d) = φ(q)`;
  `J₂(p)/φ(p)² = (p+1)/(p-1)`; `∑_{d∣q} μ(q/d) = 0` при `q > 1`.

---

## 3. Сборка и воспроизведение

### Требования

- `git`, `curl`, `elan` (Lean version manager);
- Lean toolchain, закреплённый в `lean-toolchain` (`leanprover/lean4:v4.35.0`);
- Mathlib, закреплённый в `lakefile.toml` (тег `v4.35.0`);
- ~8 GB свободного дискового пространства (Mathlib cache + сборка).

### Установка с нуля (Ubuntu 24.04 / WSL2)

```bash
# 1. Системные зависимости
sudo apt-get update
sudo apt-get install -y curl git build-essential

# 2. Менеджер версий Lean (пропустите, если elan уже установлен)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 3. Клонирование и сборка
git clone <URL-репозитория> ttp
cd ttp
lake exe cache get   # ≈ 6–7 GB olean-файлов Mathlib
lake build
```

### Команды

```bash
elan --version          # ожидается elan 4.2.4 или новее
lake exe cache get      # загрузка кэша Mathlib (≈ 9000 olean-файлов)
lake build              # сборка библиотеки
```

Проверка отдельного файла без полной сборки:

```bash
lake env lean path/to/File.lean
```

Полезно для локальной проверки лемм: `lake exe cache get` идемпотентен и догружает
только отсутствующие артефакты.

### Открытие проекта в WSL и VS Code

| Способ | Команда / путь |
|---|---|
| Терминал WSL | `wsl --cd ~/ttp` |
| Проводник Windows | `\\wsl.localhost\Ubuntu-24.04\home\gosudar\ttp` |
| VS Code (Remote-WSL) | `code --remote wsl+Ubuntu-24.04 ~/ttp` |

Расширение `leanprover.lean4` должно быть установлено **в WSL-remote** (не локально),
иначе language server не увидит toolchain и Mathlib.

---

## 4. Статус верификации

Проверено в окружении: **Ubuntu 24.04 LTS (WSL2), x86_64**, Lean 4.35.0
(commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Lake 5.0.0, elan 4.2.4,
Mathlib `v4.35.0`. Дата верификации: 2026-11-13.

```
Build completed successfully (2922 jobs).
BUILD_EXIT=0
WARNINGS=0
ERRORS=0
SORRY=0
```

| Показатель | Значение |
|---|---|
| Код возврата `lake build` | **0** |
| Предупреждения компилятора | **0** |
| Ошибки | **0** |
| `sorry` в исходниках | **0** |
| Задач сборки (jobs) | 2922 |
| Модулей в `TTP/` | **10** |
| Проект собирается после `touch` любого модуля | да (проверено) |

Дополнительно каждый модуль проверялся независимым файлом через `lake env lean`
(утверждения применялись к конкретным числам: `p = 2, 3, 5, 7, 11, 13`,
`n = 6, 10, 12, 30`, `q = 3, 5, 7, 11`, `r = 2, 3, 5`, `B = 2, 3, 4, 5`,
`M = 6, 30`), с `exit code 0`.

Ключевые коммиты аналитических направлений: `60db6ee` — `MemoryKernel`,
`3f4a627` — `ProperTimeWhitening`, `b99c5eb` — `CholeskyRamanujan`.

---

## 5. Структура репозитория

```
ttp/
├── TTP.lean              # корневой модуль (импортирует все разделы)
├── TTP/
│   ├── Basic.lean                 # шаблонный модуль Lake
│   ├── Definitions.lean           # Глава 1: праймориал, тор, кристалл
│   ├── ChordCharge.lean           # Глава 3: Φ_q(1), примарность, Λ
│   ├── SieveNilpotence.lean       # Глава 4: Аксиома IV
│   ├── ExactSieve.lean            # Глава 5.0: точное решето и горизонт B²
│   ├── PhaseDiode.lean            # Глава 5.1: фазовый диод
│   ├── CombinatorialSieve.lean    # Глава 5.2: гашение 𝓛_k
│   ├── MemoryKernel.lean          # Направление I: ядро памяти Шеннона
│   ├── ProperTimeWhitening.lean   # Направление II: обеление собственного времени
│   └── CholeskyRamanujan.lean     # Направление III: Холецкий–Рамануджан
├── lean-toolchain                 # leanprover/lean4:v4.35.0
├── lakefile.toml                  # зависимости и опции линтеров Mathlib
├── lake-manifest.json
└── .github/workflows/             # CI: Lean Action CI, release, update
```

---

## 6. Технические замечания

- Проект использует **module system** Mathlib: каждый файл начинается с
  copyright-заголовка, содержит `module`, `public import` и
  `@[expose] public section`. Это обязательно: при обычном `import` объявления
  становятся приватными и недоступны из других модулей.
- `primorial` и `cyclotomicEvalOne` — **noncomputable** (зависят от `Nat.nth`
  и `Polynomial.cyclotomic`), поэтому `#eval`/`decide` к ним неприменимы;
  значения доказываются через `Nat.nth_prime_*` и `eval_one_cyclotomic_*`.
- `Nat.nth` импортируется из `Mathlib.Data.Nat.Prime.Nth`
  (в `Mathlib.Data.Nat.Prime.Basic` его нет).
- В Mathlib 4.35 модули `Mathlib.Data.Rat.Basic` и
  `Mathlib.Data.List.BigOperators.Lemmas` отсутствуют; используются
  `Mathlib.Data.Rat.Defs` + `Mathlib.Data.Rat.Lemmas` и
  `Mathlib.Algebra.(Order.)BigOperators.Group.List.*` соответственно.
- `properTimeDefect` — **noncomputable**: предикат содержит неограниченный
  `∀ p, …`, поэтому определение использует `classical`; `Nat.sum_divisorsAntidiagonal`
  применяется явным термом (переписывание не матчит шаблон `f i.1 i.2`).
- Для обращения матрицы используется биекция `Finset.sum_bij` (d ↦ d/c), а для
  `J₂` — инверсия Мёбиуса `sum_eq_iff_sum_mul_moebius_eq` совместно с
  `Nat.sum_totient`; в 4.35 это `Nat.Prime.divisors`, а не `Nat.divisors_prime`.
- Все строки должны укладываться в 100 символов (`linter.style.longLine`).
- Ключевые леммы-опоры: `ZMod.val_coe_unit_coprime`,
  `Polynomial.eval_one_cyclotomic_not_prime_pow`,
  `Nat.squarefree_and_prime_pow_iff_prime`, `Nat.minFac_sq_le_self`,
  `List.pow_length_le_prod`, `ArithmeticFunction.vonMangoldt_eq_zero_iff`.

---

## 7. Лицензия и цитирование

Код распространяется по лицензии **Apache License 2.0**
(<https://www.apache.org/licenses/LICENSE-2.0>); условия указаны в заголовках
исходных файлов. При использовании просьба ссылаться на репозиторий:

```bibtex
@misc{ttp_lean,
  title        = {Toroidal Theory of Primes (TTP) in Lean 4},
  author       = {Andrei Lukianchikov},
  year         = {2026},
  howpublished = {\url{https://github.com/<owner>/ttp}},
  note         = {Formalisation in Lean 4 with Mathlib}
}
```

> При публикации замените `<owner>` в BibTeX и URL репозитория на фактический
> GitHub-аккаунт (`https://github.com/<owner>/ttp`).
