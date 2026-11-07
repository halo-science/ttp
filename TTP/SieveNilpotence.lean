/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Prime.Basic
public import TTP.Definitions
public import TTP.ChordCharge

/-!
# Аксиома IV ТТП: конечная нильпотентность решета

Ситовые факторизации числа `n` на `m` сомножителей, каждый из которых не меньше
ситовой границы `B ≥ 2`. Если `n < B^m`, допустимых факторизаций не существует:
высшие ситовые свёртки тождественно равны нулю.
-/

@[expose] public section

namespace TTP

/-- Допустимая ситовая факторизация `n` на `m` сомножителей, каждый из которых `≥ B`. -/
def IsSieveFactorization (B m n : ℕ) (L : List ℕ) : Prop :=
  L.length = m ∧ (∀ x ∈ L, B ≤ x) ∧ L.prod = n

/-- Фундаментальное неравенство: произведение `m` чисел, каждое из которых `≥ B`,
не меньше `B^m`. -/
theorem sieve_factorization_pow_le (B m n : ℕ) (L : List ℕ)
    (h : IsSieveFactorization B m n L) : B ^ m ≤ n := by
  obtain ⟨hlen, hB, hprod⟩ := h
  subst m
  subst n
  exact List.pow_length_le_prod L B hB

/-- Главная теорема о нильпотентности сита (Аксиома IV ТТП): при `n < B^m`
допустимых ситовых факторизаций длины `m` не существует. -/
theorem sieve_nilpotent (B m n : ℕ) (hn : n < B ^ m) (L : List ℕ)
    (h : IsSieveFactorization B m n L) : False := by
  have hle := sieve_factorization_pow_le B m n L h
  omega

/-- Следствие для простых чисел: любая ситовая факторизация простого `p`
на сомножители `≥ 2` имеет длину ровно `1`. -/
theorem prime_factorization_length_one {p m : ℕ} (hp : p.Prime) (L : List ℕ)
    (h : IsSieveFactorization 2 m p L) : m = 1 := by
  obtain ⟨hlen, hB, hprod⟩ := h
  rcases L with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hprod
    have := hp.two_le
    omega
  · simp at hlen
    omega
  · have ha : 2 ≤ a := hB a (by simp)
    have hdvd : a ∣ p := by
      rw [← hprod]
      exact List.dvd_prod (by simp)
    have hap : a = p := by
      rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | h2
      · omega
      · exact h2
    have h1 : a * (b * t.prod) = a := by
      calc a * (b * t.prod) = (a :: b :: t).prod := by simp
        _ = p := hprod
        _ = a := hap.symm
    have h2 : b * t.prod = 1 := by
      have ha0 : 0 < a := by omega
      exact Nat.mul_left_cancel ha0 (by simpa using h1)
    have hb : 2 ≤ b := hB b (by simp)
    have hb_le : b ≤ 1 := Nat.le_of_dvd (by norm_num) ⟨t.prod, h2.symm⟩
    omega

end TTP
