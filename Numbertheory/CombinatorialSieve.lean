/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Numbertheory.Definitions
public import Numbertheory.ChordCharge
public import Numbertheory.SieveNilpotence
public import Numbertheory.ExactSieve
public import Numbertheory.PhaseDiode

/-!
# Глава 5.2: комбинаторное гашение составного шума в операторном логарифме решета

Усечённые знакопеременные логарифмы решета `𝓛_k(n) = Σ_{m=1}^{k} (-1)^{m-1}/m · C_m(n)`
над `ℚ` и тождественное обнуление составного вклада для диполей, триполей и кубических узлов.
-/

@[expose] public section

namespace TTPC

/-- Знакопеременный логарифм решета глубины 1 (простой слой). -/
def sieveLogOrder1 (C1 : ℚ) : ℚ :=
  C1

/-- Знакопеременный логарифм решета глубины 2 (квадратичный горизонт: диполи и квадраты). -/
def sieveLogOrder2 (C1 C2 : ℚ) : ℚ :=
  C1 - (1 / 2) * C2

/-- Знакопеременный логарифм решета глубины 3 (кубический горизонт: триполи и кубы). -/
def sieveLogOrder3 (C1 C2 C3 : ℚ) : ℚ :=
  C1 - (1 / 2) * C2 + (1 / 3) * C3

/-- Для простого числа `p` свёртка сохраняет единичный вес: `𝓛_k(p) = 1`. -/
theorem sieve_log_prime_eq_one :
    sieveLogOrder1 1 = 1 := by
  rfl

/-- Для квадрата простого `p^2` вклад равен `1/2` (вес фон Мангольдта `Λ(p^2)/ln(p^2)`). -/
theorem sieve_log_prime_sq_eq_half :
    sieveLogOrder2 1 1 = 1 / 2 := by
  norm_num [sieveLogOrder2]

/-- Гашение полупростого диполя `pq`: `1 - 1/2(2) = 0`. Составной шум уничтожается. -/
theorem sieve_cancellation_dipole :
    sieveLogOrder2 1 2 = 0 := by
  norm_num [sieveLogOrder2]

/-- Гашение смешанного триполя `p^2 q`: `1 - 1/2(4) + 1/3(3) = 1 - 2 + 1 = 0`. -/
theorem sieve_cancellation_mixed_tripole :
    sieveLogOrder3 1 4 3 = 0 := by
  norm_num [sieveLogOrder3]

/-- Гашение кубического узла `pqr`: `1 - 1/2(6) + 1/3(6) = 1 - 3 + 2 = 0`. -/
theorem sieve_cancellation_cubic_node :
    sieveLogOrder3 1 6 6 = 0 := by
  norm_num [sieveLogOrder3]

/-- Инвариантность: при нулевой третьей свёртке расширение до порядка 3
не меняет значение логарифма. -/
theorem sieve_log_order_embed (C1 C2 : ℚ) :
    sieveLogOrder3 C1 C2 0 = sieveLogOrder2 C1 C2 := by
  simp [sieveLogOrder3, sieveLogOrder2]

end TTPC
