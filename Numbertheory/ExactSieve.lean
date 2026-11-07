/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Squarefree
public import Numbertheory.Definitions
public import Numbertheory.ChordCharge
public import Numbertheory.SieveNilpotence

/-!
# Точное решето: замыкание алгебры и горизонта сита

Объединение хордового заряда (`ChordCharge`) и нильпотентности решета
(`SieveNilpotence`): устранение составного шума, точный фильтр простых
и горизонт решета `B^2`.
-/

@[expose] public section

namespace TTPC

/-- Устранение составного шума: бесквадратное `n > 1`, у которого круговой
заряд не равен `1`, обязано быть простым (ср. `Λ n = 0`). -/
theorem squarefree_prime_of_chord_nontrivial {n : ℕ} (hn : 1 < n)
    (hsq : Squarefree n) (h_chord : cyclotomicEvalOne n ≠ 1) : n.Prime := by
  have hIP : IsPrimePow n := by
    by_contra h
    exact h_chord ((cyclotomicEvalOne_eq_one_iff_not_isPrimePow hn).mpr h)
  exact Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsq, hIP⟩

/-- Горизонт решета `B^2`: если все простые делители `n` не меньше `B ≥ 2`
и `n < B^2`, то `n` простое (факторизация длины `≥ 2` невозможна). -/
theorem prime_of_sieve_horizon {B n : ℕ} (hB : 2 ≤ B) (hn1 : 1 < n) (hn : n < B ^ 2)
    (h_div : ∀ p, p.Prime → p ∣ n → B ≤ p) : n.Prime := by
  -- `hB` сохраняется в сигнатуре ради API: противоречие вытекает уже из
  -- `B ≤ minFac n`, `minFac n ^ 2 ≤ n` и `n < B ^ 2`.
  have hB2 : 2 ≤ B := hB
  by_contra hnp
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hpr : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hBle : B ≤ n.minFac := h_div n.minFac hpr hdvd
  have hsq2 : B ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left hBle 2
  omega

/-- Итоговая связка ТТПЧ: число, пережившее первичное сито до горизонта `B^2`,
имеет хордовый заряд, строго равный его простому значению. -/
theorem sieve_exact_identity {B p : ℕ} (hB : 2 ≤ B) (hp1 : 1 < p) (hp : p < B ^ 2)
    (h_div : ∀ q, q.Prime → q ∣ p → B ≤ q) :
    cyclotomicEvalOne p = (p : ℤ) := by
  have hpp : p.Prime := prime_of_sieve_horizon hB hp1 hp h_div
  exact @cyclotomicEvalOne_prime p (Fact.mk hpp)

end TTPC
