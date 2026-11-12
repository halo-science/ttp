/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import TTP.PhaseDiode
public import TTP.ExactSieve
public import TTP.ChordCharge
public import TTP.MemoryKernel

/-!
# Обеление собственного времени и ортогональность каналов CCA (Направление II)

Связывает фазовый диод (`TTP.PhaseDiode`), точное решето (`TTP.ExactSieve`),
хордовый заряд (`TTP.ChordCharge`) и ядро памяти (`TTP.MemoryKernel`) в единую
цепочку: многоточечную проводимость тора, детерминированное обнуление дефекта
собственного времени внутри квадратичного горизонта `B^2` и телескопическую
границу хвоста внешней памяти.
-/

@[expose] public section

namespace TTP

open scoped ArithmeticFunction.omega

/-! ### Лемма II.1: многоточечная проводимость фазового диода -/

/-- 4-точечная открытая цепочка сдвигов на оси `p`. -/
def PhaseDiodeChain4Open (p u S₁ S₂ S₃ : ℕ) : Prop :=
  PhaseDiodeOpen p u ∧ PhaseDiodeOpen p (u + S₁) ∧
    PhaseDiodeOpen p (u + S₂) ∧ PhaseDiodeOpen p (u + S₃)

/-- Цепочка открыта тогда и только тогда, когда `p` не делит ни один из четырёх узлов. -/
theorem phase_diode_chain4_iff_not_dvd (p u S₁ S₂ S₃ : ℕ) [Fact p.Prime] :
    PhaseDiodeChain4Open p u S₁ S₂ S₃ ↔
      ¬ (p ∣ u) ∧ ¬ (p ∣ (u + S₁)) ∧ ¬ (p ∣ (u + S₂)) ∧ ¬ (p ∣ (u + S₃)) := by
  simp [PhaseDiodeChain4Open, phase_diode_open_iff_not_dvd]

/-- Периодичность цепочки по сдвигу `u` с периодом `p`. -/
theorem phase_diode_chain4_periodic (p u S₁ S₂ S₃ : ℕ) :
    PhaseDiodeChain4Open p (u + p) S₁ S₂ S₃ ↔ PhaseDiodeChain4Open p u S₁ S₂ S₃ := by
  unfold PhaseDiodeChain4Open PhaseDiodeOpen
  have h0 : ((u + p : ℕ) : ZMod p) = (u : ZMod p) := by
    push_cast
    rw [ZMod.natCast_self, add_zero]
  have hS : ∀ S : ℕ, (((u + p) + S : ℕ) : ZMod p) = ((u + S : ℕ) : ZMod p) := by
    intro S
    push_cast
    rw [ZMod.natCast_self, add_zero]
  rw [h0, hS S₁, hS S₂, hS S₃]

/-- Точное вырождение на оси `p = 2`: при чётных сдвигах цепочка открыта
тогда и только тогда, когда `u` нечётно. -/
theorem phase_diode_chain4_two_of_even {u S₁ S₂ S₃ : ℕ}
    (h1 : Even S₁) (h2 : Even S₂) (h3 : Even S₃) :
    PhaseDiodeChain4Open 2 u S₁ S₂ S₃ ↔ Odd u := by
  unfold PhaseDiodeChain4Open PhaseDiodeOpen
  have h0 : ((u : ZMod 2) ≠ 0) ↔ Odd u := ZMod.natCast_ne_zero_iff_odd
  have hs : ∀ S : ℕ, Even S → (((u + S : ℕ) : ZMod 2) ≠ 0 ↔ Odd u) := by
    intro S hS
    have hzero : ((S : ℕ) : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hS
    have hcast : (((u + S : ℕ)) : ZMod 2) = (u : ZMod 2) := by
      push_cast
      rw [hzero, add_zero]
    rw [hcast, ZMod.natCast_ne_zero_iff_odd]
  rw [h0, hs S₁ h1, hs S₂ h2, hs S₃ h3]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, h, h, h⟩

/-! ### Теорема II.2: обнуление дефекта собственного времени -/

/-- Дефект собственного времени на интервале `(a, b)`: число составных кандидатов,
переживших первичное решето с границей `B`. -/
noncomputable def properTimeDefect (B a b : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioo a b).filter (fun m =>
    (∀ p, p.Prime → p ∣ m → B ≤ p) ∧ ¬ m.Prime)).card

/-- Внутри квадратичного горизонта `b ≤ B^2` дефект собственного времени равен нулю. -/
theorem properTimeDefect_eq_zero_of_horizon {B a b : ℕ} (hB : 2 ≤ B) (ha : 1 ≤ a)
    (hb : b ≤ B ^ 2) : properTimeDefect B a b = 0 := by
  classical
  unfold properTimeDefect
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hprop
  rw [Finset.mem_Ioo] at hm
  obtain ⟨ham, hmb⟩ := hm
  obtain ⟨hdiv, hnp⟩ := hprop
  exact hnp (prime_of_sieve_horizon hB (by omega) (by omega) hdiv)

/-- При нулевых ядрах памяти `J₁ = J₂ = 0` условная взаимная информация обнуляется. -/
theorem cmi_zero_of_vanishing_kernels (p0 : ℚ) (q : ℕ) : CMI 0 0 p0 q = 0 := by
  simp [CMI]

/-! ### Теорема II.3: ортогональность каналов и граница хвоста -/

/-- Аннигиляция смешанных межосевых кумулянтов: для `ω(q) ≥ 2` круговой заряд
равен единице, а функция фон Мангольдта обращается в нуль. -/
theorem cca_composite_channel_annihilation {q : ℕ} (hq : 2 ≤ ω q) :
    cyclotomicEvalOne q = 1 ∧ ArithmeticFunction.vonMangoldt q = 0 := by
  have h1 : cyclotomicEvalOne q = 1 := cyclotomicEvalOne_of_omega_ge_two hq
  have hq1 : 1 < q := by
    have hpos : 0 < ω q := by omega
    exact ArithmeticFunction.cardDistinctFactors_pos.mp hpos
  exact ⟨h1, (cyclotomicEvalOne_eq_one_iff_vonMangoldt_eq_zero hq1).mp h1⟩

/-- Строгая граница хвоста внешней памяти: если поканальная память ограничена
телескопической мажорантой, суммарная остаточная память меньше `1/(2(B-3))`. -/
theorem external_cmi_tail_lt {B N : ℕ} (hB : 4 ≤ B) (hN : 1 ≤ N) (cmiVal : ℕ → ℚ)
    (hbound : ∀ i ∈ Finset.range N, cmiVal i ≤
      1 / (2 * (((B + i : ℕ) : ℚ) - 2) * (((B + i : ℕ) : ℚ) - 3))) :
    (∑ i ∈ Finset.range N, cmiVal i) < 1 / (2 * ((B : ℚ) - 3)) := by
  have hle : (∑ i ∈ Finset.range N, cmiVal i) ≤
      ∑ i ∈ Finset.range N,
        1 / (2 * (((B + i : ℕ) : ℚ) - 2) * (((B + i : ℕ) : ℚ) - 3)) :=
    Finset.sum_le_sum hbound
  have hlt := tail_sum_lt B N hB hN
  linarith

end TTP
