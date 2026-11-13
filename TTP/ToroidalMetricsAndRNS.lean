/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import TTP.PhaseDiode
public import TTP.CombinatorialSieve
public import TTP.CholeskyRamanujan

/-!
# Тороидальные метрики и бескомпараторная СОК (Главы 2, 5.2, 7.2, 8.1, 8.3, 10)

Формальное покрытие оставшихся глав монографии: резонанс Штёрмера `Δ* = 13090`
на 8-мерном праймориальном торе `M₈ = 9699690`, закон диадической ортогональности,
телескопическое экранирование Фано `O_k(1)`, неподвижная точка оператора Эйлера,
вторичная инверсия Мёбиуса в неветвящемся проекторе простых чисел и ячейка
`Dual-Adder` бескомпараторного сопроцессора СОК.
-/

@[expose] public section

namespace TTP

open scoped BigOperators

/-! ### Глава 2: резонанс Штёрмера и диадическая ортогональность -/

/-- Резонанс Штёрмера `Δ* = 13090` на 8-мерном торе `M₈ = 9699690`:
делимость кубического полинома смежных чисел и вес Хэмминга `w_H = 3`. -/
theorem stormer_resonance_13090 :
    9699690 ∣ (13090 - 1) * 13090 * (13090 + 1) ∧
      ([2, 3, 5, 7, 11, 13, 17, 19].filter (fun p => 13090 % p ≠ 0)).length = 3 := by
  constructor
  · norm_num
  · decide

/-- Закон диадической ортогональности (Глава 2.3): сдвиг на `2^s` (`s ≥ 1`) от нечётного
полупраймориального центра `(2m + 1) · M_odd` взаимно прост с `2 · M_odd`. -/
theorem dyadic_center_coprime {M_odd : ℕ} (hodd : Odd M_odd) (m s : ℕ) (hs : 1 ≤ s) :
    Nat.Coprime ((2 * m + 1) * M_odd + 2 ^ s) (2 * M_odd) := by
  have hEven : Even (2 ^ s) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
    rw [pow_succ]
    exact even_two.mul_left (2 ^ t)
  have hOddSum : Odd ((2 * m + 1) * M_odd + 2 ^ s) :=
    (odd_two_mul_add_one m).mul hodd |>.add_even hEven
  have h2 : Nat.Coprime ((2 * m + 1) * M_odd + 2 ^ s) 2 :=
    Nat.coprime_two_right.mpr hOddSum
  have hM : Nat.Coprime (2 ^ s) M_odd :=
    (Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hodd)).symm
  have hM' : Nat.Coprime ((2 * m + 1) * M_odd + 2 ^ s) M_odd := by
    rw [show (2 * m + 1) * M_odd + 2 ^ s = 2 ^ s + M_odd * (2 * m + 1) by ring]
    exact (Nat.coprime_add_mul_left_left (2 ^ s) M_odd (2 * m + 1)).mpr hM
  exact h2.mul_right hM'

/-! ### Главы 5.2, 8.1, 8.3: телескопическое экранирование и оператор Эйлера -/

/-- Телескопическое тождество для суммы приращений кограницы на окне длины `L`. -/
theorem coboundary_telescope_sum (E : ℕ → ℚ) (L : ℕ) :
    (∑ i ∈ Finset.range L, (E (i + 1) - E i)) = E L - E 0 :=
  Finset.sum_range_sub E L

/-- Ограниченность накопленного приращения кограницы (экранирование Фано `O_k(1)`). -/
theorem coboundary_telescope_bound (E : ℕ → ℚ) (C : ℚ) (L : ℕ)
    (h0 : -C ≤ E 0 ∧ E 0 ≤ C) (hL : -C ≤ E L ∧ E L ≤ C) :
    -(2 * C) ≤ (∑ i ∈ Finset.range L, (E (i + 1) - E i)) ∧
      (∑ i ∈ Finset.range L, (E (i + 1) - E i)) ≤ 2 * C := by
  rw [coboundary_telescope_sum]
  constructor <;> linarith [h0.1, h0.2, hL.1, hL.2]

/-- Линейная функция `x` как точная неподвижная точка нормированного оператора Эйлера. -/
theorem euler_operator_linear_fixed_point {p : ℕ} (hp : 2 ≤ p) (x : ℚ) :
    ((p : ℚ) / ((p : ℚ) - 1)) * (x - x / (p : ℚ)) = x := by
  have hp0 : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hp1 : (p : ℚ) - 1 ≠ 0 := by
    have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  field_simp

/-! ### Глава 7.2: вторичная инверсия Мёбиуса в проекторе простых чисел -/

/-- Неветвящийся проектор простых чисел `𝓛_k^Dir` на степенях простых `p^m` (Глава 7.2). -/
def purePrimeProjectorPower (m : ℕ) : ℚ :=
  ∑ r ∈ m.divisors,
    ((ArithmeticFunction.moebius r : ℚ) / (r : ℚ)) * (1 / ((m / r : ℕ) : ℚ))

/-- Точное выделение чистых простых (`m = 1`) и аннигиляция высших степеней (`m ≥ 2`). -/
theorem purePrimeProjectorPower_eq_delta {m : ℕ} (hm : 1 ≤ m) :
    purePrimeProjectorPower m = if m = 1 then 1 else 0 := by
  have hm0 : m ≠ 0 := by omega
  have hterm : ∀ r ∈ m.divisors,
      ((ArithmeticFunction.moebius r : ℚ) / (r : ℚ)) * (1 / ((m / r : ℕ) : ℚ)) =
        (ArithmeticFunction.moebius r : ℚ) / (m : ℚ) := by
    intro r hr
    have hdvd : r ∣ m := Nat.dvd_of_mem_divisors hr
    have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hmq : (m : ℚ) ≠ 0 := by
      have : 0 < m := by omega
      exact_mod_cast this.ne'
    have hqr : ((m / r : ℕ) : ℚ) ≠ 0 := by
      have hpos : 0 < m / r :=
        Nat.div_pos (Nat.le_of_dvd (by omega : 0 < m) hdvd) hrpos
      exact_mod_cast hpos.ne'
    have hmul : (r : ℚ) * ((m / r : ℕ) : ℚ) = (m : ℚ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    field_simp
    rw [mul_assoc, hmul]
  unfold purePrimeProjectorPower
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, sum_moebius_divisors m]
  by_cases h1 : m = 1
  · subst h1
    simp
  · simp [h1]

/-! ### Глава 10: ячейка `Dual-Adder` бескомпараторного сопроцессора СОК -/

/-- Аппаратная ячейка `Dual-Adder` (Глава 10.2): шаг в СОК без операции деления. -/
def dualAdder (p r δ : ℕ) : ℕ :=
  if r + δ < p then r + δ else r + δ - p

/-- Точное совпадение ячейки `Dual-Adder` с операцией взятия остатка `(r + δ) % p`. -/
theorem dualAdder_eq_mod {p r δ : ℕ} (hr : r < p) (hδ : δ < p) :
    dualAdder p r δ = (r + δ) % p := by
  unfold dualAdder
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · have hp : p ≤ r + δ := by omega
    rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)]

/-- Сохранение инварианта диапазона регистра `dualAdder p r δ < p`. -/
theorem dualAdder_lt {p r δ : ℕ} (hr : r < p) (hδ : δ < p) :
    dualAdder p r δ < p := by
  rw [dualAdder_eq_mod hr hδ]
  exact Nat.mod_lt _ (by omega)

/-- Эквивалентность ненулевого выхода `Dual-Adder` открытому состоянию Фазового Диода. -/
theorem dualAdder_ne_zero_iff_phase_diode_open {p r δ : ℕ} [Fact p.Prime]
    (hr : r < p) (hδ : δ < p) :
    dualAdder p r δ ≠ 0 ↔ PhaseDiodeOpen p (r + δ) := by
  rw [dualAdder_eq_mod hr hδ, phase_diode_open_iff_not_dvd p (r + δ)]
  exact (Nat.dvd_iff_mod_eq_zero (m := p) (n := r + δ)).not.symm

end TTP
