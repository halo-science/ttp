/-
Copyright (c) 2026 The Numbertheory Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Numbertheory Authors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Numbertheory.Definitions

/-!
# Хордовая алгебра (ХКА): круговой заряд

Значение кругового полинома `Φ_q` в точке `1` (`cyclotomicEvalOne`) и его связь
с примарностью и функцией фон Мангольдта `Λ`.
-/

@[expose] public section

namespace TTPC

open Polynomial

open scoped ArithmeticFunction ArithmeticFunction.omega

/-- Значение кругового полинома `Φ_q(X)` в точке `X = 1` в кольце `ℤ`. -/
noncomputable def cyclotomicEvalOne (q : ℕ) : ℤ :=
  (cyclotomic q ℤ).eval 1

/-- `Φ_1(1) = 0`. -/
theorem cyclotomicEvalOne_one : cyclotomicEvalOne 1 = 0 := by
  simp [cyclotomicEvalOne, Polynomial.cyclotomic_one]

/-- Для простого `p`: `Φ_p(1) = p`. -/
theorem cyclotomicEvalOne_prime {p : ℕ} [Fact p.Prime] :
    cyclotomicEvalOne p = (p : ℤ) := by
  simp [cyclotomicEvalOne]

/-- Для степени простого `p^(k+1)`: `Φ_{p^(k+1)}(1) = p`. -/
theorem cyclotomicEvalOne_prime_pow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    cyclotomicEvalOne (p ^ (k + 1)) = (p : ℤ) := by
  simp [cyclotomicEvalOne]

/-- Фильтрационный критерий ХКА: `Φ_q(1) = 1` тогда и только тогда, когда `q`
не является степенью простого числа (включая `q = 1 = p^0`). -/
theorem cyclotomicEvalOne_eq_one_iff (q : ℕ) :
    cyclotomicEvalOne q = 1 ↔ ∀ p : ℕ, p.Prime → ∀ k : ℕ, p ^ k ≠ q := by
  constructor
  · intro h p hp k hk
    rcases k with _ | k
    · simp only [pow_zero] at hk
      rw [← hk, cyclotomicEvalOne_one] at h
      norm_num at h
    · rw [← hk] at h
      have h1 : cyclotomicEvalOne (p ^ (k + 1)) = (p : ℤ) :=
        @cyclotomicEvalOne_prime_pow p (Fact.mk hp) k
      rw [h1] at h
      have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
      omega
  · intro h
    rw [cyclotomicEvalOne, Polynomial.eval_one_cyclotomic_not_prime_pow]
    intro p hp k hk
    exact h p hp k hk

/-- Если у `q` не менее двух различных простых делителей (`ω(q) ≥ 2`),
то `Φ_q(1) = 1`. -/
theorem cyclotomicEvalOne_of_omega_ge_two {q : ℕ} (hq : 2 ≤ ω q) :
    cyclotomicEvalOne q = 1 := by
  rw [cyclotomicEvalOne_eq_one_iff]
  intro p hp k hk
  rcases k with _ | k
  · simp only [pow_zero] at hk
    have h0 : ω q = 0 := by rw [← hk]; simp
    omega
  · have h1 : ω (p ^ (k + 1)) = 1 :=
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp (Nat.succ_ne_zero k)
    rw [hk] at h1
    omega

/-- Фильтрационный критерий в терминах примарности: для `q > 1`
значение `Φ_q(1)` равно `1` тогда и только тогда, когда `q` не является степенью простого. -/
theorem cyclotomicEvalOne_eq_one_iff_not_isPrimePow {q : ℕ} (hq : 1 < q) :
    cyclotomicEvalOne q = 1 ↔ ¬ IsPrimePow q := by
  rw [isPrimePow_nat_iff, cyclotomicEvalOne_eq_one_iff]
  constructor
  · rintro h ⟨p, k, hp, hk0, hk⟩
    exact h p hp k hk
  · intro h p hp k hk
    rcases k with _ | k
    · simp only [pow_zero] at hk
      omega
    · exact h ⟨p, k + 1, hp, Nat.succ_pos k, hk⟩

/-- Связь с функцией фон Мангольдта: для `q > 1` значение `Φ_q(1)` равно `1`
тогда и только тогда, когда `Λ(q) = 0`. -/
theorem cyclotomicEvalOne_eq_one_iff_vonMangoldt_eq_zero {q : ℕ} (hq : 1 < q) :
    cyclotomicEvalOne q = 1 ↔ Λ q = 0 := by
  rw [cyclotomicEvalOne_eq_one_iff_not_isPrimePow hq, ArithmeticFunction.vonMangoldt_eq_zero_iff]

end TTPC
