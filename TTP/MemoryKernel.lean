/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Ядро памяти Шеннона и кубическое затухание `O(q⁻³)`

Глава 4, Теоремы I.1–I.2: точное расщепление производящего ядра
`K(t) = (3 + t) / ((1 - t)(1 + t)^2)`, двусторонние рациональные границы `J(r)`,
бинарный фазовый замок `q = 3` и телескопическая мажоранта хвоста памяти.
-/

@[expose] public section

namespace TTP

/-! ### 1. Производящее ядро и его тейлоровские аппроксимации -/

/-- Производящее ядро памяти Шеннона `K(t) = (3 + t) / ((1 - t)(1 + t)^2)`. -/
def memoryKernel (t : ℚ) : ℚ :=
  (3 + t) / ((1 - t) * (1 + t) ^ 2)

/-- Точное расщепление: остаток нижней аппроксимации Тейлора. -/
theorem memoryKernel_sub_taylorLower (t : ℚ) (ht1 : t ≠ 1) (ht2 : t ≠ -1) :
    memoryKernel t - (3 - 2 * t) =
      t ^ 2 * (5 + t - 2 * t ^ 2) / ((1 - t) * (1 + t) ^ 2) := by
  have h1 : (1 : ℚ) - t ≠ 0 := by
    intro h
    exact ht1 (by linarith)
  have h2 : (1 : ℚ) + t ≠ 0 := by
    intro h
    exact ht2 (by linarith)
  have hD : (1 - t) * (1 + t) ^ 2 ≠ 0 := mul_ne_zero h1 (pow_ne_zero 2 h2)
  unfold memoryKernel
  rw [← mul_div_cancel_right₀ (3 - 2 * t) hD]
  rw [← sub_div]
  congr 1
  ring

/-- Точное расщепление: остаток верхней аппроксимации Тейлора. -/
theorem taylorUpper_sub_memoryKernel (t : ℚ) (ht1 : t ≠ 1) (ht2 : t ≠ -1) :
    (3 - 2 * t + 5 * t ^ 2) - memoryKernel t =
      t ^ 3 * (4 - 3 * t - 5 * t ^ 2) / ((1 - t) * (1 + t) ^ 2) := by
  have h1 : (1 : ℚ) - t ≠ 0 := by
    intro h
    exact ht1 (by linarith)
  have h2 : (1 : ℚ) + t ≠ 0 := by
    intro h
    exact ht2 (by linarith)
  have hD : (1 - t) * (1 + t) ^ 2 ≠ 0 := mul_ne_zero h1 (pow_ne_zero 2 h2)
  unfold memoryKernel
  rw [← mul_div_cancel_right₀ (3 - 2 * t + 5 * t ^ 2) hD]
  rw [← sub_div]
  congr 1
  ring

/-- Остаток нижней аппроксимации строго положителен при `0 < t ≤ 1/2`. -/
theorem taylorLower_remainder_pos {t : ℚ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) :
    0 < t ^ 2 * (5 + t - 2 * t ^ 2) / ((1 - t) * (1 + t) ^ 2) := by
  have ht1 : t < 1 := by linarith
  have ht2 : -1 < t := by linarith
  have hnum : 0 < 5 + t - 2 * t ^ 2 := by nlinarith
  have h1t : 0 < 1 - t := by linarith
  have h1pt : 0 < 1 + t := by linarith
  have hden : 0 < (1 - t) * (1 + t) ^ 2 := mul_pos h1t (pow_pos h1pt 2)
  exact div_pos (mul_pos (pow_pos h0 2) hnum) hden

/-- Остаток верхней аппроксимации строго положителен при `0 < t ≤ 1/2`. -/
theorem taylorUpper_remainder_pos {t : ℚ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) :
    0 < t ^ 3 * (4 - 3 * t - 5 * t ^ 2) / ((1 - t) * (1 + t) ^ 2) := by
  have ht1 : t < 1 := by linarith
  have ht2 : -1 < t := by linarith
  have hnum : 0 < 4 - 3 * t - 5 * t ^ 2 := by nlinarith
  have h1t : 0 < 1 - t := by linarith
  have h1pt : 0 < 1 + t := by linarith
  have hden : 0 < (1 - t) * (1 + t) ^ 2 := mul_pos h1t (pow_pos h1pt 2)
  exact div_pos (mul_pos (pow_pos h0 3) hnum) hden

/-- Двусторонняя тейлоровская вилка для ядра при `t = 1/r ∈ (0, 1/2]`. -/
theorem memoryKernel_taylor_sandwich {t : ℚ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) :
    3 - 2 * t < memoryKernel t ∧ memoryKernel t < 3 - 2 * t + 5 * t ^ 2 := by
  have ht1 : t ≠ 1 := by linarith
  have ht2 : t ≠ -1 := by linarith
  constructor
  · have h := memoryKernel_sub_taylorLower t ht1 ht2
    have hpos := taylorLower_remainder_pos h0 h1
    linarith
  · have h := taylorUpper_sub_memoryKernel t ht1 ht2
    have hpos := taylorUpper_remainder_pos h0 h1
    linarith

/-! ### 2. Двусторонние рациональные границы ядра `J(r)` -/

/-- Нижняя рациональная граница `J_low(r) = 1/(2r²) - 1/(6r³)`. -/
def memoryJLower (r : ℚ) : ℚ :=
  1 / (2 * r ^ 2) - 1 / (6 * r ^ 3)

/-- Верхняя рациональная граница `J_high(r) = 1/(2r²) - 1/(6r³) + 1/(4r⁴)`. -/
def memoryJUpper (r : ℚ) : ℚ :=
  1 / (2 * r ^ 2) - 1 / (6 * r ^ 3) + 1 / (4 * r ^ 4)

/-- Нижняя граница строго положительна при `r ≥ 2`. -/
theorem memoryJLower_pos {r : ℚ} (hr : 2 ≤ r) : 0 < memoryJLower r := by
  have hr0 : (0 : ℚ) < r := by linarith
  have h3 : 0 < 6 * r ^ 3 := mul_pos (by norm_num) (pow_pos hr0 3)
  have hnum : 0 < 3 * r - 1 := by linarith
  have h : memoryJLower r = (3 * r - 1) / (6 * r ^ 3) := by
    unfold memoryJLower
    field_simp
    ring
  rw [h]
  exact div_pos hnum h3

/-- Нижняя граница строго меньше верхней при `r ≥ 2`. -/
theorem memoryJLower_lt_memoryJUpper {r : ℚ} (hr : 2 ≤ r) :
    memoryJLower r < memoryJUpper r := by
  have hr0 : (0 : ℚ) < r := by linarith
  have h4 : 0 < 4 * r ^ 4 := mul_pos (by norm_num) (pow_pos hr0 4)
  have hpos : 0 < 1 / (4 * r ^ 4) := div_pos one_pos h4
  unfold memoryJLower memoryJUpper
  linarith

/-- Верхняя граница строго меньше `1/(2r²)` при `r ≥ 2`. -/
theorem memoryJUpper_lt_half_inv_sq {r : ℚ} (hr : 2 ≤ r) :
    memoryJUpper r < 1 / (2 * r ^ 2) := by
  have hr0 : (0 : ℚ) < r := by linarith
  have h4 : 0 < r ^ 4 := pow_pos hr0 4
  have hdiff : 1 / (6 * r ^ 3) - 1 / (4 * r ^ 4) = (2 * r - 3) / (12 * r ^ 4) := by
    have h3 : (6 : ℚ) * r ^ 3 ≠ 0 := by positivity
    have h4' : (4 : ℚ) * r ^ 4 ≠ 0 := by positivity
    field_simp
    ring
  have hpos : 0 < 1 / (6 * r ^ 3) - 1 / (4 * r ^ 4) := by
    rw [hdiff]
    have hnum : 0 < 2 * r - 3 := by linarith
    have hden : 0 < 12 * r ^ 4 := mul_pos (by norm_num) h4
    exact div_pos hnum hden
  have h : 1 / (2 * r ^ 2) - memoryJUpper r = 1 / (6 * r ^ 3) - 1 / (4 * r ^ 4) := by
    unfold memoryJUpper
    ring
  linarith

/-- Строгая цепочка границ `0 < J_low < J_high < 1/(2r²)` при `r ≥ 2`. -/
theorem memoryJ_bounds {r : ℚ} (hr : 2 ≤ r) :
    0 < memoryJLower r ∧ memoryJLower r < memoryJUpper r ∧ memoryJUpper r < 1 / (2 * r ^ 2) :=
  ⟨memoryJLower_pos hr, memoryJLower_lt_memoryJUpper hr, memoryJUpper_lt_half_inv_sq hr⟩

/-! ### 3. Бинарный фазовый замок при `q = 3` -/

/-- Условная взаимная информация `CMI(q, p₀)` канала памяти. -/
def CMI (J1 J2 p0 : ℚ) (q : ℕ) : ℚ :=
  p0 * (1 - p0) ^ 2 / ((q : ℚ) - 2) * J1 +
    ((q : ℚ) - 3) * (1 - p0) ^ 3 / ((q : ℚ) - 2) ^ 2 * J2

/-- Бинарный фазовый замок: при `q = 3` канал фазовой триангуляции обнуляется,
и `CMI` сводится к транзитному каналу `p₀(1-p₀)²J₁`. -/
theorem CMI_three (J1 J2 p0 : ℚ) :
    CMI J1 J2 p0 3 = p0 * (1 - p0) ^ 2 * J1 := by
  unfold CMI
  norm_num

/-! ### 4. Телескопическая мажоранта хвоста памяти -/

/-- Тождество расщепления члена мажоранты при `q ≥ 4`. -/
theorem tail_majorant_split {q : ℕ} (hq : 4 ≤ q) :
    1 / (2 * ((q : ℚ) - 2) * ((q : ℚ) - 3)) =
      1 / (2 * ((q : ℚ) - 3)) - 1 / (2 * ((q : ℚ) - 2)) := by
  have hq' : (4 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have h2 : (q : ℚ) - 2 ≠ 0 := by linarith
  have h3 : (q : ℚ) - 3 ≠ 0 := by linarith
  field_simp
  ring

/-- Телескопическая формула конечной суммы хвоста памяти по `N` шагам от `B ≥ 4`. -/
theorem tail_sum_telescope (B N : ℕ) (hB : 4 ≤ B) :
    (∑ i ∈ Finset.range N,
        1 / (2 * (((B + i : ℕ) : ℚ) - 2) * (((B + i : ℕ) : ℚ) - 3))) =
      1 / (2 * ((B : ℚ) - 3)) - 1 / (2 * (((B + N : ℕ) : ℚ) - 3)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rw [tail_majorant_split (q := B + N) (by omega)]
    have hcast : (((B + (N + 1) : ℕ) : ℚ) - 3) = (((B + N : ℕ) : ℚ) - 2) := by
      push_cast
      ring
    rw [hcast]
    ring

/-- Строгая мажоранта хвоста: при `N ≥ 1` сумма строго меньше `1/(2(B-3))`. -/
theorem tail_sum_lt (B N : ℕ) (hB : 4 ≤ B) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range N,
        1 / (2 * (((B + i : ℕ) : ℚ) - 2) * (((B + i : ℕ) : ℚ) - 3))) <
      1 / (2 * ((B : ℚ) - 3)) := by
  rw [tail_sum_telescope B N hB]
  have hBN : (4 : ℚ) ≤ ((B + N : ℕ) : ℚ) := by
    have : 4 ≤ B + N := by omega
    exact_mod_cast this
  have hden : 0 < ((B + N : ℕ) : ℚ) - 3 := by linarith
  have hpos : 0 < 1 / (2 * (((B + N : ℕ) : ℚ) - 3)) :=
    div_pos one_pos (mul_pos (by norm_num) hden)
  linarith

end TTP
