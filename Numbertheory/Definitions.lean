/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.ZMod.Basic

/-!
# Глава 1 ТТПЧ

Базовые определения: праймориал, праймориальный тор и копрайм-кристалл.
-/

@[expose] public section

namespace TTPC

open Nat

/--
Праймориал p_k#: произведение первых k простых чисел
(соответствует Главе 1 ТТПЧ).
-/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => primorial k * (Nat.nth Nat.Prime k)

/--
Праймориальный тор ранга k: кольцо вычетов Z / M_k Z
(согласно Китайской теореме об остатках изоморфно прямому произведению по модулям p_i).
-/
abbrev PrimorialTorus (k : ℕ) := ZMod (primorial k)

/--
Копрайм-кристалл Φ_k*: мультипликативная группа обратимых элементов тора.
-/
abbrev CoprimeCrystal (k : ℕ) := (PrimorialTorus k)ˣ

/--
Теорема: натуральное значение любого вычета из копрайм-кристалла
строго взаимно просто с периодом тора (праймориалом M_k).
-/
theorem crystal_coprime (k : ℕ) (x : CoprimeCrystal k) :
    Nat.Coprime (x.1.val) (primorial k) := by
  exact ZMod.val_coe_unit_coprime x

end TTPC
