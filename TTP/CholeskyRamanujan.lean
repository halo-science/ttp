/-
Copyright (c) 2026 Andrei Lukianchikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrei Lukianchikov
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import TTP.Definitions

/-!
# Факторизация Холецкого — Рамануджана и кограница на торе (Направление III)

Алгебраическое ядро Теорем III.1–III.2 над `ℚ`: тотиент Жордана `J₂`, точная
треугольная факторизация матрицы Грама на решётке делителей и нейтральность волн
Рамануджана.
-/

@[expose] public section

namespace TTP

/-- Тотиент-функция Жордана второго порядка `J₂(n) = ∑_{d ∣ n} μ(n/d) · d²`. -/
def jordanTotient2 (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * ((d : ℚ) ^ 2)

/-- Матрица Грама центрированных пилообразных волн на торе: `gcd(d₁, d₂)² / (12 d₁ d₂)`. -/
def torusGram (d₁ d₂ : ℕ) : ℚ :=
  ((Nat.gcd d₁ d₂ : ℚ) ^ 2) / (12 * (d₁ : ℚ) * (d₂ : ℚ))

/-- Нижнетреугольный оператор Холецкого `L_{d, c} = (1 / d) · 𝟏_{c ∣ d}`. -/
def choleskyRaw (d c : ℕ) : ℚ :=
  if c ∣ d then (1 : ℚ) / (d : ℚ) else 0

/-- Обратный оператор Холецкого — Мёбиуса `L⁻¹_{q, d} = d · μ(q/d) · 𝟏_{d ∣ q}`. -/
def choleskyInvRaw (q d : ℕ) : ℚ :=
  if d ∣ q then (d : ℚ) * (ArithmeticFunction.moebius (q / d) : ℚ) else 0

/-! ### Вспомогательные суммы Мёбиуса -/

/-- `∑_{d ∣ n} μ(d) = δ_{n,1}`. -/
lemma sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℚ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

/-- Сумма по кратным `c` внутри делителей `c * m` переиндексируется в делители `m`. -/
lemma sum_multiples_moebius {c m : ℕ} (hc : 0 < c) (hm : 0 < m) :
    (∑ d ∈ (c * m).divisors.filter (fun d => c ∣ d),
        (ArithmeticFunction.moebius ((c * m) / d) : ℚ))
      = ∑ e ∈ m.divisors, (ArithmeticFunction.moebius (m / e) : ℚ) := by
  have hcm : 0 < c * m := Nat.mul_pos hc hm
  refine Finset.sum_bij (fun d _ => d / c) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hcd⟩ := hd
    rw [Nat.mem_divisors]
    obtain ⟨k, rfl⟩ := hcd
    exact ⟨by
      rw [Nat.mul_div_cancel_left k hc]
      exact (Nat.mul_dvd_mul_iff_left hc).mp hdvd, hm.ne'⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    rw [Finset.mem_filter, Nat.mem_divisors] at hd₁ hd₂
    obtain ⟨⟨-, -⟩, hc₁⟩ := hd₁
    obtain ⟨⟨-, -⟩, hc₂⟩ := hd₂
    calc d₁ = c * (d₁ / c) := (Nat.mul_div_cancel' hc₁).symm
      _ = c * (d₂ / c) := by rw [heq]
      _ = d₂ := Nat.mul_div_cancel' hc₂
  · intro e he
    rw [Nat.mem_divisors] at he
    obtain ⟨hev, -⟩ := he
    refine ⟨c * e, ?_, Nat.mul_div_cancel_left e hc⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left c hev, hcm.ne'⟩, ⟨e, rfl⟩⟩
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hcd⟩ := hd
    obtain ⟨k, rfl⟩ := hcd
    show (ArithmeticFunction.moebius ((c * m) / (c * k)) : ℚ)
      = (ArithmeticFunction.moebius (m / (c * k / c)) : ℚ)
    rw [Nat.mul_div_mul_left m k hc, Nat.mul_div_cancel_left k hc]

/-! ### Теоремы III.1–III.2 -/

/-- Свёрточное тождество Дирихле: `∑_{c ∣ g} J₂(c) = g²` при `g ≥ 1`. -/
theorem sum_jordanTotient2_divisors {g : ℕ} (hg : 1 ≤ g) :
    (∑ c ∈ g.divisors, jordanTotient2 c) = (g : ℚ) ^ 2 := by
  have hmain : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, jordanTotient2 d) = (n : ℚ) ^ 2 := by
    refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
      (f := jordanTotient2) (g := fun n => (n : ℚ) ^ 2)).mpr ?_
    intro n hn
    have hanti : (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℚ) * (x.2 : ℚ) ^ 2)
        = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * ((n / d : ℕ) : ℚ) ^ 2 :=
      Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a : ℚ) * (b : ℚ) ^ 2)
    rw [hanti]
    unfold jordanTotient2
    have hstep : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * ((d : ℚ) ^ 2))
        = ∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius (n / d) : ℚ) * (((n / (n / d) : ℕ) : ℚ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      rw [Nat.div_div_self hdvd hn.ne']
    rw [hstep, Nat.sum_div_divisors n
      (fun x => (ArithmeticFunction.moebius x : ℚ) * (((n / x : ℕ) : ℚ) ^ 2))]
  exact hmain g (by omega)

/-- Значение `J₂(p) = p² - 1` для простого `p`. -/
theorem jordanTotient2_prime {p : ℕ} (hp : p.Prime) :
    jordanTotient2 p = (p : ℚ) ^ 2 - 1 := by
  rw [jordanTotient2, hp.divisors,
    Finset.sum_insert (by simp [hp.ne_one.symm]), Finset.sum_singleton]
  simp [ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos]
  ring

/-- Точная факторизация Холецкого матрицы Грама на решётке делителей `M ≥ 1`. -/
theorem torusGram_cholesky_factorization {M d₁ d₂ : ℕ} (hM : 1 ≤ M)
    (hd₁ : d₁ ∈ M.divisors) (hd₂ : d₂ ∈ M.divisors) :
    torusGram d₁ d₂ =
      (1 / 12 : ℚ) * ∑ c ∈ M.divisors, jordanTotient2 c * choleskyRaw d₁ c * choleskyRaw d₂ c := by
  have hM0 : M ≠ 0 := by omega
  have hd₁dvd : d₁ ∣ M := Nat.dvd_of_mem_divisors hd₁
  have hd₂dvd : d₂ ∣ M := Nat.dvd_of_mem_divisors hd₂
  have hd₁pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁dvd (by omega)
  have hd₂pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd₂dvd (by omega)
  have hgdvd : Nat.gcd d₁ d₂ ∣ M := dvd_trans (Nat.gcd_dvd_left d₁ d₂) hd₁dvd
  have hraw : ∀ (d c : ℕ), choleskyRaw d c = (if c ∣ d then (1 : ℚ) else 0) * (1 / (d : ℚ)) := by
    intro d c
    unfold choleskyRaw
    by_cases h : c ∣ d <;> simp [h]
  have hfilter1 : M.divisors.filter (fun c => c ∣ d₁) = d₁.divisors :=
    Nat.divisors_filter_dvd_of_dvd hM0 hd₁dvd
  have hfilter2 : d₁.divisors.filter (fun c => c ∣ d₂) = (Nat.gcd d₁ d₂).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd hd₁pos.ne' (Nat.gcd_dvd_left d₁ d₂)]
    apply Finset.filter_congr
    intro c hc
    have hc1 : c ∣ d₁ := Nat.dvd_of_mem_divisors hc
    exact ⟨fun h2 => Nat.dvd_gcd hc1 h2, fun hg => dvd_trans hg (Nat.gcd_dvd_right d₁ d₂)⟩
  have hsum : (∑ c ∈ M.divisors, jordanTotient2 c * choleskyRaw d₁ c * choleskyRaw d₂ c)
      = (∑ c ∈ (Nat.gcd d₁ d₂).divisors, jordanTotient2 c) *
          ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
    calc
      ∑ c ∈ M.divisors, jordanTotient2 c * choleskyRaw d₁ c * choleskyRaw d₂ c
          = ∑ c ∈ M.divisors,
              (if c ∣ d₁ then (if c ∣ d₂ then jordanTotient2 c else 0) else 0) *
                ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [hraw d₁ c, hraw d₂ c]
            by_cases h1 : c ∣ d₁
            · by_cases h2 : c ∣ d₂
              · simp [h1, h2]
                ring
              · simp [h1, h2]
            · simp [h1]
      _ = (∑ c ∈ M.divisors,
              (if c ∣ d₁ then (if c ∣ d₂ then jordanTotient2 c else 0) else 0)) *
            ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            rw [Finset.sum_mul]
      _ = (∑ c ∈ M.divisors.filter (fun c => c ∣ d₁),
              (if c ∣ d₂ then jordanTotient2 c else 0)) *
            ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            rw [← Finset.sum_filter]
      _ = (∑ c ∈ d₁.divisors, (if c ∣ d₂ then jordanTotient2 c else 0)) *
            ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            rw [hfilter1]
      _ = (∑ c ∈ d₁.divisors.filter (fun c => c ∣ d₂), jordanTotient2 c) *
            ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            rw [← Finset.sum_filter]
      _ = (∑ c ∈ (Nat.gcd d₁ d₂).divisors, jordanTotient2 c) *
            ((1 / (d₁ : ℚ)) * (1 / (d₂ : ℚ))) := by
            rw [hfilter2]
  rw [hsum, sum_jordanTotient2_divisors (Nat.gcd_pos_of_pos_left d₂ hd₁pos)]
  unfold torusGram
  have h1 : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁pos.ne'
  have h2 : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂pos.ne'
  field_simp

/-- Точное обращение оператора Холецкого — Мёбиуса `(L⁻¹ L)_{q, c} = δ_{q, c}` на `M.divisors`. -/
theorem cholesky_mobius_inversion {M q c : ℕ} (hM : 1 ≤ M)
    (hq : q ∈ M.divisors) (hc : c ∈ M.divisors) :
    (∑ d ∈ M.divisors, choleskyInvRaw q d * choleskyRaw d c) = if q = c then 1 else 0 := by
  have hM0 : M ≠ 0 := by omega
  have hqdvd : q ∣ M := Nat.dvd_of_mem_divisors hq
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqdvd (by omega)
  have hcdvd : c ∣ M := Nat.dvd_of_mem_divisors hc
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcdvd (by omega)
  have hterm : ∀ d ∈ M.divisors,
      choleskyInvRaw q d * choleskyRaw d c =
        if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0 := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega)).ne'
    unfold choleskyInvRaw choleskyRaw
    by_cases h1 : d ∣ q
    · by_cases h2 : c ∣ d
      · simp only [h1, h2, ite_true]
        have hd0q : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
        field_simp
      · simp [h1, h2]
    · simp [h1]
  have hstep1 : (∑ d ∈ M.divisors, choleskyInvRaw q d * choleskyRaw d c)
      = ∑ d ∈ M.divisors,
          if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0 :=
    Finset.sum_congr rfl hterm
  have hqM : q.divisors ⊆ M.divisors := Nat.divisors_subset_of_dvd hM0 hqdvd
  have hstep2a : (∑ d ∈ M.divisors,
        if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0)
      = ∑ d ∈ q.divisors,
          if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0 :=
    (Finset.sum_subset
      (f := fun d =>
        if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0)
      hqM (fun d _ hdnot => by
        have hndq : ¬ d ∣ q := by
          intro h
          exact hdnot (Nat.mem_divisors.mpr ⟨h, hqpos.ne'⟩)
        simp [hndq])).symm
  have hstep2b : (∑ d ∈ q.divisors,
        if d ∣ q then (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) else 0)
      = ∑ d ∈ q.divisors,
          (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    simp [Nat.dvd_of_mem_divisors hd]
  have hstep2 := hstep2a.trans hstep2b
  have hstep3 : (∑ d ∈ q.divisors,
        (if c ∣ d then (ArithmeticFunction.moebius (q / d) : ℚ) else 0))
      = ∑ d ∈ q.divisors.filter (fun d => c ∣ d),
          (ArithmeticFunction.moebius (q / d) : ℚ) :=
    (Finset.sum_filter (fun d => c ∣ d)
      (fun d => (ArithmeticFunction.moebius (q / d) : ℚ))).symm
  rw [hstep1, hstep2, hstep3]
  by_cases hcq : c ∣ q
  · obtain ⟨m, rfl⟩ := hcq
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · subst hm0
        simp at hq
      · exact hm
    rw [sum_multiples_moebius hcpos hmpos]
    rw [Nat.sum_div_divisors m (fun x => (ArithmeticFunction.moebius x : ℚ))]
    rw [sum_moebius_divisors m]
    have hm1 : (c * m = c) ↔ (m = 1) := by
      constructor
      · intro h
        exact Nat.mul_left_cancel hcpos (by simpa using h)
      · intro h
        rw [h, mul_one]
    by_cases h : m = 1
    · simp [h]
    · have hne : c * m ≠ c := fun hh => h (hm1.mp hh)
      simp [h, hne]
  · have hqc : q ≠ c := by
      intro h
      subst h
      exact hcq dvd_rfl
    have hempty : q.divisors.filter (fun d => c ∣ d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd hcd
      exact hcq (dvd_trans hcd (Nat.dvd_of_mem_divisors hd))
    rw [hempty, Finset.sum_empty]
    simp [hqc]

/-- Обнуление линейного тренда волн Рамануджана при `q > 1`. -/
theorem ramanujan_linear_drift_zero {q : ℕ} (hq : 1 < q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℚ)) = 0 := by
  rw [Nat.sum_div_divisors q (fun d => (ArithmeticFunction.moebius d : ℚ))]
  rw [sum_moebius_divisors q]
  simp [show q ≠ 1 by omega]

/-- Тотиент-вес амплитуды Рамануджана: `∑_{d ∣ q} d · μ(q/d) = φ(q)`. -/
theorem ramanujan_totient_weight (q : ℕ) :
    (∑ d ∈ q.divisors, (d : ℚ) * (ArithmeticFunction.moebius (q / d) : ℚ)) =
      (Nat.totient q : ℚ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp
  have hφ : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, (Nat.totient d : ℚ)) = (n : ℚ) := by
    intro n hn
    exact_mod_cast Nat.sum_totient n
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
    (f := fun n => (Nat.totient n : ℚ)) (g := fun n => (n : ℚ))).mp hφ q hq0
  have hanti : (∑ x ∈ q.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (x.2 : ℚ))
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℚ) * ((q / d : ℕ) : ℚ) :=
    Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a : ℚ) * (b : ℚ))
  rw [hanti] at hinv
  have hcomm : (∑ d ∈ q.divisors, (d : ℚ) * (ArithmeticFunction.moebius (q / d) : ℚ))
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℚ) * (d : ℚ) := by
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hstep : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℚ) * (d : ℚ))
      = ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius (q / d) : ℚ) * (((q / (q / d) : ℕ) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    rw [Nat.div_div_self hdvd hq0.ne']
  rw [hcomm, hstep, Nat.sum_div_divisors q
    (fun x => (ArithmeticFunction.moebius x : ℚ) * ((q / x : ℕ) : ℚ)), hinv]

/-- Спектральный фактор простой оси: `J₂(p) / φ(p)² = (p + 1) / (p - 1)`. -/
theorem torus_coboundary_prime_factor {p : ℕ} (hp : p.Prime) :
    jordanTotient2 p / ((Nat.totient p : ℚ) ^ 2) = ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  have hcast : ((Nat.totient p : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
    norm_num
  rw [jordanTotient2_prime hp, hcast]
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have h1 : (p : ℚ) - 1 ≠ 0 := by linarith
  field_simp
  ring

end TTP
