/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import TTP.CholeskyRamanujan

/-!
# Мост к функциональным полям `𝔽_q[t]`

Архитектурное замыкание `TTP`: ультраметрический мост между праймориальным тором
в `ℤ` и функциональными полями `𝔽_q[t]`.

1. Полиномиальный квадратичный горизонт простоты: нормированный приводимый
   многочлен `F` над `ZMod p` имеет нормированный неприводимый делитель `P`
   с `2 * P.natDegree ≤ F.natDegree`.
2. Ультраметрическое деление оболочек степеней без дробного остатка:
   `q ^ d ∣ q ^ N` и `q^N / q^d = q^(N-d)` в `ℚ`.
3. Экспоненциальное затухание хвоста памяти `O(q⁻²ᵈ)`: точная геометрическая
   сумма слоёв и строгая мажоранта при `N ≥ 1`.
4. Мост к `ℤ`: тождественный вакуум волн Холецкого — Рамануджана на `[0, 1)`.
-/

@[expose] public section

namespace TTP

open scoped BigOperators

/-! ### Полиномиальный квадратичный горизонт простоты -/

/-- Аддитивность степени для нормированных многочленов над `ZMod p`. -/
theorem poly_monic_mul_natDegree {p : ℕ} [Fact p.Prime]
    {A B : Polynomial (ZMod p)} (hA : A.Monic) (hB : B.Monic) :
    (A * B).Monic ∧ (A * B).natDegree = A.natDegree + B.natDegree :=
  ⟨hA.mul hB, hA.natDegree_mul hB⟩

set_option maxHeartbeats 800000 in
-- The `WfDvdMonoid` instance search and the monic normalization of an irreducible
-- factor require more than the default heartbeat limit.
/-- Полиномиальный квадратичный горизонт: приводимый нормированный многочлен `F`
имеет нормированный неприводимый делитель степени не выше `(natDegree F) / 2`. -/
theorem poly_quadratic_degree_horizon {p : ℕ} [Fact p.Prime]
    {F : Polynomial (ZMod p)} (hF : F.Monic) (hdeg : 1 ≤ F.natDegree)
    (hred : ¬ Irreducible F) :
    ∃ P : Polynomial (ZMod p), P.Monic ∧ Irreducible P ∧ P ∣ F ∧ 2 * P.natDegree ≤ F.natDegree := by
  have hF0 : F ≠ 0 := hF.ne_zero
  have hnu : ¬ IsUnit F := by
    intro hu
    have hd : F.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
    rw [Polynomial.degree_eq_natDegree hF0] at hd
    have h0 : F.natDegree = 0 := by simpa using hd
    omega
  have hnot : ¬ ∀ q : Polynomial (ZMod p), q.Monic →
      q.natDegree ∈ Finset.Ioc 0 (F.natDegree / 2) → ¬ q ∣ F := by
    intro hall
    exact hred ((Polynomial.irreducible_iff_lt_natDegree_lt hF0 hnu).mpr hall)
  push Not at hnot
  obtain ⟨q, hqmonic, hqmem, hqdvd⟩ := hnot
  rw [Finset.mem_Ioc] at hqmem
  obtain ⟨hqpos, hqle⟩ := hqmem
  have hq0 : q ≠ 0 := hqmonic.ne_zero
  obtain ⟨r, hrirr, hrq⟩ := Polynomial.exists_irreducible_of_natDegree_pos hqpos
  have hr0 : r ≠ 0 := hrirr.ne_zero
  have hc0 : r.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.1 hr0
  set P : Polynomial (ZMod p) := r * Polynomial.C r.leadingCoeff⁻¹ with hPdef
  have hPmonic : P.Monic := by
    rw [hPdef]
    exact Polynomial.monic_mul_leadingCoeff_inv hr0
  have hPirr : Irreducible P := by
    rw [hPdef]
    exact Polynomial.irreducible_mul_leadingCoeff_inv.mpr hrirr
  have hPdeg : P.natDegree = r.natDegree := by
    rw [hPdef]
    exact Polynomial.natDegree_mul_leadingCoeff_inv r hr0
  have hPq : P ∣ q := by
    obtain ⟨s, hs⟩ := hrq
    refine ⟨Polynomial.C r.leadingCoeff * s, ?_⟩
    have hC : Polynomial.C r.leadingCoeff⁻¹ * Polynomial.C r.leadingCoeff = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hc0, Polynomial.C_1]
    symm
    calc P * (Polynomial.C r.leadingCoeff * s)
        = r * ((Polynomial.C r.leadingCoeff⁻¹ * Polynomial.C r.leadingCoeff) * s) := by
          rw [hPdef]
          ring
      _ = r * (1 * s) := by rw [hC]
      _ = r * s := by rw [one_mul]
      _ = q := hs.symm
  refine ⟨P, hPmonic, hPirr, hPq.trans hqdvd, ?_⟩
  have hPle : P.natDegree ≤ q.natDegree := by
    rw [hPdeg]
    exact Polynomial.natDegree_le_of_dvd hrq hq0
  have hq2 : 2 * q.natDegree ≤ F.natDegree := by
    have h := (Nat.le_div_iff_mul_le Nat.zero_lt_two).mp hqle
    omega
  omega

/-! ### Ультраметрическое деление оболочек степеней -/

/-- Ультраметрическая делимость объёма оболочки `q^N` на норму делителя `q^d` (`d ≤ N`). -/
theorem poly_shell_exact_dvd (q : ℕ) {N d : ℕ} (hd : d ≤ N) :
    q ^ d ∣ q ^ N :=
  pow_dvd_pow q hd

/-- Отсутствие дробного краевого остатка на полиномиальной оболочке степеней в `ℚ`. -/
theorem poly_shell_zero_remainder {q N d : ℕ} (hq : 1 ≤ q) (hd : d ≤ N) :
    ((q ^ N : ℕ) : ℚ) / ((q ^ d : ℕ) : ℚ) = ((q ^ (N - d) : ℕ) : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have hqpos : 0 < q := by omega
    exact_mod_cast (ne_of_gt hqpos)
  have hpow : q ^ N = q ^ d * q ^ (N - d) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  rw [hpow, Nat.cast_mul]
  have hd0 : ((q ^ d : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero d hq0
  exact mul_div_cancel_left₀ _ hd0

/-! ### Экспоненциальное затухание хвоста памяти -/

/-- Член геометрического хвоста памяти на слое степени `m` в `𝔽_q[t]`. -/
def polyTailLayer (q m : ℕ) : ℚ :=
  1 / (2 * ((q : ℚ) ^ 2) ^ m)

/-- Геометрическая сумма `∑_{j<N} r^j` в форме с `(1 - r)` в знаменателе. -/
private lemma geom_sum_range_rat (r : ℚ) (hr : r ≠ 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) = (1 - r ^ N) / (1 - r) := by
  rw [geom_sum_eq hr N,
    show (1 : ℚ) - r ^ N = -(r ^ N - 1) by ring,
    show (1 : ℚ) - r = -(r - 1) by ring, neg_div_neg_eq]

/-- Инверсия степени в поле: `(x⁻¹)^n = (x^n)⁻¹`. -/
private lemma inv_pow_rat (x : ℚ) (n : ℕ) : (x⁻¹) ^ n = (x ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_inv, ih]

/-- Алгебраический шаг индукции для геометрической суммы слоёв памяти. -/
private lemma poly_tail_step (Q : ℚ) (hQ0 : Q ≠ 0) (hQ1 : Q ≠ 1) (e n : ℕ) :
    (1 - 1 / Q ^ n) / (2 * (Q - 1) * Q ^ e) + 1 / (2 * Q ^ (e + 1 + n)) =
      (1 - 1 / Q ^ (n + 1)) / (2 * (Q - 1) * Q ^ e) := by
  have hQe : Q ^ e ≠ 0 := pow_ne_zero e hQ0
  have hQm : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ1
  have hpow1 : Q ^ (e + 1 + n) = Q ^ e * Q ^ n * Q := by
    rw [show e + 1 + n = e + n + 1 by omega, pow_succ, pow_add]
  have hpow2 : Q ^ (n + 1) = Q ^ n * Q := pow_succ Q n
  rw [hpow1, hpow2]
  field_simp
  ring

/-- Замкнутая форма одного слоя геометрической суммы. -/
private lemma poly_tail_closed_form (Q : ℚ) (hQ0 : Q ≠ 0) (hQ1 : Q ≠ 1) (e N : ℕ) :
    (1 / (2 * Q ^ (e + 1))) * ((1 - (Q⁻¹) ^ N) / (1 - Q⁻¹)) =
      (1 - 1 / Q ^ N) / (2 * (Q - 1) * Q ^ e) := by
  have hQe : Q ^ e ≠ 0 := pow_ne_zero e hQ0
  have hQm : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ1
  have hQN : Q ^ N ≠ 0 := pow_ne_zero N hQ0
  rw [show Q ^ (e + 1) = Q ^ e * Q by rw [pow_succ], inv_pow_rat Q N]
  field_simp

/-- Точная замкнутая формула конечной суммы экспоненциального хвоста памяти в `𝔽_q[t]`. -/
theorem poly_tail_geometric_sum {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (N : ℕ) :
    (∑ j ∈ Finset.range N, polyTailLayer q (d + j)) =
      (1 - 1 / ((q : ℚ) ^ 2) ^ N) / (2 * ((q : ℚ) ^ 2 - 1) * ((q : ℚ) ^ 2) ^ (d - 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.sub_add_cancel hd).symm⟩
  have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  set Q : ℚ := (q : ℚ) ^ 2 with hQdef
  simp only [Nat.add_sub_cancel]
  have hQgt : (1 : ℚ) < Q := by
    rw [hQdef]
    nlinarith [sq_nonneg ((q : ℚ) - 2)]
  have hQ0 : Q ≠ 0 := ne_of_gt (by linarith)
  have hQ1 : Q ≠ 1 := ne_of_gt hQgt
  have hQinv : Q⁻¹ ≠ 1 := by
    intro h
    have h1 : Q * Q⁻¹ = Q * 1 := by rw [h]
    rw [mul_inv_cancel₀ hQ0, mul_one] at h1
    exact hQ1 h1.symm
  have hterm : ∀ j : ℕ,
      polyTailLayer q ((e + 1) + j) = (1 / (2 * Q ^ (e + 1))) * (Q⁻¹) ^ j := by
    intro j
    have hQj : Q ^ j ≠ 0 := pow_ne_zero j hQ0
    unfold polyTailLayer
    rw [← hQdef, pow_add, inv_pow_rat Q j]
    field_simp
  calc ∑ j ∈ Finset.range N, polyTailLayer q ((e + 1) + j)
      = ∑ j ∈ Finset.range N, (1 / (2 * Q ^ (e + 1))) * (Q⁻¹) ^ j :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = (1 / (2 * Q ^ (e + 1))) * ∑ j ∈ Finset.range N, (Q⁻¹) ^ j := by
        rw [Finset.mul_sum]
    _ = (1 / (2 * Q ^ (e + 1))) * ((1 - (Q⁻¹) ^ N) / (1 - Q⁻¹)) := by
        rw [geom_sum_range_rat (Q⁻¹) hQinv N]
    _ = (1 - 1 / Q ^ N) / (2 * (Q - 1) * Q ^ e) :=
        poly_tail_closed_form Q hQ0 hQ1 e N
    _ = (1 - 1 / ((q : ℚ) ^ 2) ^ N) /
          (2 * ((q : ℚ) ^ 2 - 1) * ((q : ℚ) ^ 2) ^ e) := by
        rw [hQdef]

/-- Строгая экспоненциальная мажоранта хвоста памяти при `N ≥ 1`. -/
theorem poly_tail_geometric_lt {q d N : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, polyTailLayer q (d + j)) <
      1 / (2 * ((q : ℚ) ^ 2 - 1) * ((q : ℚ) ^ 2) ^ (d - 1)) := by
  rw [poly_tail_geometric_sum hq hd N]
  have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  set Q : ℚ := (q : ℚ) ^ 2 with hQdef
  have hQgt : (1 : ℚ) < Q := by
    rw [hQdef]
    nlinarith [sq_nonneg ((q : ℚ) - 2)]
  have hQpos : (0 : ℚ) < Q := by linarith
  have hD : (0 : ℚ) < 2 * (Q - 1) * Q ^ (d - 1) := by
    have h1 : (0 : ℚ) < Q - 1 := by linarith
    exact mul_pos (mul_pos two_pos h1) (pow_pos hQpos _)
  rw [div_lt_div_iff_of_pos_right hD]
  have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
  rw [hN1, pow_succ]
  have hpos : (0 : ℚ) < 1 / (Q ^ (N - 1) * Q) := by
    exact one_div_pos.mpr (mul_pos (pow_pos hQpos _) hQpos)
  linarith

/-! ### Мост к `ℤ`: вакуум волн Рамануджана на `[0, 1)` -/

/-- Волна Холецкого — Рамануджана `ψ_q(x)` на интервале `[0, 1)`, где `{x / d} = x / d`. -/
def ramanujanWaveUnitInterval (q : ℕ) (x : ℚ) : ℚ :=
  ∑ d ∈ q.divisors, (d : ℚ) * (ArithmeticFunction.moebius (q / d) : ℚ) * (x / (d : ℚ))

/-- Тождественный вакуум волн Рамануджана на `[0, 1)` для любого `q > 1`. -/
theorem ramanujanWaveUnitInterval_eq_zero {q : ℕ} (hq : 1 < q) (x : ℚ) :
    ramanujanWaveUnitInterval q x = 0 := by
  unfold ramanujanWaveUnitInterval
  have hterm : ∀ d ∈ q.divisors,
      (d : ℚ) * (ArithmeticFunction.moebius (q / d) : ℚ) * (x / (d : ℚ)) =
        (ArithmeticFunction.moebius (q / d) : ℚ) * x := by
    intro d hd
    have hd0 : (d : ℚ) ≠ 0 := by
      have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      exact_mod_cast this
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ramanujan_linear_drift_zero hq, zero_mul]

end TTP
