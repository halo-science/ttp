/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import TTP.Definitions
public import TTP.ChordCharge
public import TTP.ExactSieve

/-!
# Оператор фазового диода и бескомпараторная кинематика тора

Проекция числа на оси тора (`n mod p_i`), критерий открытого узла в `ZMod p`
и гомоморфизм фазового сдвига `n ↦ n + Δ` без деления и заимствований.
-/

@[expose] public section

namespace TTP

/-- Фазовый диод на оси `p`: проверка ненулевого вычета (пропускание открытого узла). -/
def PhaseDiodeOpen (p : ℕ) (n : ℕ) : Prop :=
  (n : ZMod p) ≠ 0

/-- Критерий открытого узла: диод открыт тогда и только тогда, когда `p` не делит `n`. -/
theorem phase_diode_open_iff_not_dvd (p n : ℕ) [Fact p.Prime] :
    PhaseDiodeOpen p n ↔ ¬ (p ∣ n) := by
  simp [PhaseDiodeOpen, ZMod.natCast_eq_zero_iff]

/-- Закон фазового сдвига: шаг `n ↦ n + Δ` на торе — независимое сложение вычетов. -/
theorem phase_step_homomorphism (p : ℕ) (n Δ : ℕ) :
    ((n + Δ : ℕ) : ZMod p) = (n : ZMod p) + (Δ : ZMod p) := by
  push_cast
  rfl

/-- Критерий парного попадания в кристалл (близнецовый зазор `Δ = 2`):
если открыты узлы `n` и `n + 2`, то `p` не делит ни `n`, ни `n + 2`. -/
theorem phase_diode_twin_open (p n : ℕ) [Fact p.Prime]
    (h1 : PhaseDiodeOpen p n) (h2 : PhaseDiodeOpen p (n + 2)) :
    ¬ (p ∣ n) ∧ ¬ (p ∣ (n + 2)) := by
  constructor
  · exact (phase_diode_open_iff_not_dvd p n).mp h1
  · exact (phase_diode_open_iff_not_dvd p (n + 2)).mp h2

end TTP
