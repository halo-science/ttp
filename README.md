# Toroidal Theory of Primes (TTP) in Lean 4

![Lean](https://img.shields.io/badge/Lean-4.35.0-blueviolet)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)
![Build](https://img.shields.io/badge/build-passing-brightgreen)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)
![License](https://img.shields.io/badge/license-Apache--2.0-blue)

A Lean 4 / Mathlib formalisation of the algebraic, combinatorial, analytic and
hardware foundations of the **Toroidal Theory of Primes (TTP)**.

## Abstract (EN)

**TTP** is a Lean 4 / Mathlib library formalising the core of the Toroidal Theory
of Primes. Integers are represented as residue vectors on a primorial torus
`Z / p_k# Z`; composite contributions are annihilated by cyclotomic evaluation at one
(`Φ_q(1)`), by von Mangoldt vanishing (`Λ(q) = 0`), and by the alternating truncated
sieve logarithm `𝓛_k`. The library develops the Chord-Cumulant Algebra, the finite
nilpotent sieve, the Shannon memory kernel with cubic decay `O(q⁻³)`, proper-time
whitening, the Cholesky–Ramanujan factorisation of the toroidal Gram matrix, the
ultrametric bridge to function fields `𝔽_q[t]`, the Størmer/dyadic metric layer, and
the comparator-free `Dual-Adder` cell of a Divider-less RNS coprocessor. The
repository contains **12 verified Lean modules**, the full monograph
(`docs/monograph_v2.md`, 10 chapters, Russian), a machine-readable verification and
axiom audit (`docs/VERIFICATION_AUDIT.md`), and synthesizable SystemVerilog RTL
(`rtl/`). The development is fully verified: `lake build` exits with code `0`,
zero compiler warnings, zero `sorry`, and `#print axioms` reports only the standard
Lean/Mathlib axioms.

## Аннотация (RU)

**TTP** — библиотека формальной математики на Lean 4 / Mathlib, формализующая ядро
Тороидальной теории простых чисел: праймориальный тор, хордово-кумулянтную алгебру,
конечное нильпотентное решето, аналитические направления (ядро памяти Шеннона,
обеление собственного времени, факторизация Холецкого–Рамануджана), мост к
функциональным полям `𝔽_q[t]`, метрики Штёрмера и диадическую ортогональность, а
также ячейку `Dual-Adder` бескомпараторного сопроцессора СОК. Библиотека содержит
**12 верифицированных модулей** (`2924` задачи сборки, `sorry = 0`); полная
монография — `docs/monograph_v2.md`, машинный аудит — `docs/VERIFICATION_AUDIT.md`,
синтезируемый RTL — `rtl/`.

## Manifesto: The HALO Paradigm of Verified Symbiotic Science

This work establishes a new methodological standard whose strength lies not in loud declarations, but in **replacing closed gatekeeping with deterministic verifiability**.

For centuries, the entry ticket to fundamental science was the ability to spend years manually writing out intermediate calculations and passing through a closed filter of peer reviewers. The four-stage **HALO** architecture introduced here breaks that monopoly:

* **H — Human** (*Architect of Ontology & Constraints*): defines the foundational worldview, breaks centuries-old coordinate dogmas, and imposes strict structural constraints against heuristic dead-ends.
* **A — AI Assistant & Agent** (*Conceptual Synthesis & Tactical Proof Search*): acts as an analytical exoskeleton—bridging disparate mathematical domains and assembling formal proof states and hardware specifications.
* **L — Logical Prover** (*Deterministic Arbitration*): the deterministic type-checker of Lean 4 provides formal certification of every theorem, while Verilator performs static RTL linting of the hardware description; the two roles are distinct, and the lint is not presented as a formal equivalence proof.
* **O — Oracle-free Verification** (*Machine-Certified Truth*): no generative model is used as an oracle, and no conjecture or LLM output is ever taken on faith. The trusted base is the Lean 4 kernel together with the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; every claim must pass full mechanical certification.

**HALO — Human-Architected, AI-Augmented, Logically Verified, Oracle-Free Science**—proves in practice that a single researcher with strong geometric intuition can construct an entire mathematical system and carry it all the way to a formal machine certificate.

**The ultimate proof of this methodology is the Toroidal Theory of Primes (TTP) itself**—a self-contained mathematical, information-theoretic, and hardware framework built from scratch through this workflow. Spanning discrete primorial tori, Chord-Cumulant Algebra ($\Phi_q(1)$), Shannon proper-time whitening, finite nilpotent sieves, and comparator-free RNS-16 silicon RTL, the constructive core of TTP is rigorously established through deterministic analytics and mechanically certified in Lean 4 across **12 modules (`2924` build jobs, `sorry = 0`, standard axioms only)**.

Mathematical truth is invariant to who or what discovered the proof path; what endures is a theorem verified down to the axioms of logic.

## 1. Conceptual Introduction

Classical Eratosthenes sieve operates on integers with division and remainder. TTP
replaces this model with **torus geometry**:

1. **Primorial `p_k#`** is the product of the first `k` primes; it defines the period
   of the torus `Z / M_k Z`.
2. **Primorial torus** `T_k = Z / M_k Z` is, by the Chinese Remainder Theorem,
   isomorphic to `∏_{i≤k} Z / p_i Z`: an integer `n` is represented by its residue
   vector `(n mod p_1, …, n mod p_k)`.
3. **Coprime crystal** `Φ_k* = T_kˣ` is the multiplicative group of units of the torus;
   its elements are exactly the residues coprime to `M_k`.
4. **Composite noise** (numbers with `ω(n) ≥ 2` and their powers) is suppressed in two
   independent ways:
   - *algebraically*: `Φ_q(1) = 1` and `Λ(q) = 0` for every `q` that is not a prime
     power;
   - *combinatorially*: the alternating sieve logarithm
     `𝓛_k(n) = Σ_{m=1}^{k} (-1)^{m-1}/m · C_m(n)` vanishes for dipoles, tripoles and
     cubic nodes.
5. **Phase Diode** implements the step `n ↦ n + Δ` as independent residue addition on
   each axis — with no integer division (DIV) and no carry propagation between
   channels. This is the computational model of the specialised silicon coprocessor.

## 2. Module Architecture

| Module | Monograph chapters | Key definitions and theorems |
|---|---|---|
| `TTP/Basic.lean` | Infrastructure (Preface) | Lake template module (`def hello`); no mathematical API |
| `TTP/Definitions.lean` | Chapter 1 (§1.1, §1.3, §1.5) | `primorial : ℕ → ℕ`, `PrimorialTorus k := ZMod (primorial k)`, `CoprimeCrystal k := (PrimorialTorus k)ˣ`, `crystal_coprime` |
| `TTP/ChordCharge.lean` | Chapter 6 (§6.2–6.3) | `cyclotomicEvalOne q := (cyclotomic q ℤ).eval 1`; `cyclotomicEvalOne_prime`, `_prime_pow`, `_of_omega_ge_two`, `_eq_one_iff`, `_eq_one_iff_not_isPrimePow`, `_eq_one_iff_vonMangoldt_eq_zero` |
| `TTP/SieveNilpotence.lean` | Chapter 7 (§7.1) | `IsSieveFactorization B m n L`; `sieve_factorization_pow_le : B^m ≤ n`; `sieve_nilpotent`; `prime_factorization_length_one` |
| `TTP/ExactSieve.lean` | Chapters 1, 7 (§1.4–1.5, §7.3) | `squarefree_prime_of_chord_nontrivial`, `prime_of_sieve_horizon`, `sieve_exact_identity` |
| `TTP/PhaseDiode.lean` | Chapters 3, 9 (§3.3, §9.1) | `PhaseDiodeOpen p n := (n : ZMod p) ≠ 0`; `phase_diode_open_iff_not_dvd`, `phase_step_homomorphism`, `phase_diode_twin_open` |
| `TTP/CombinatorialSieve.lean` | Chapters 7, 9 (§7.2, §9.2) | `sieveLogOrder1/2/3`; `sieve_log_prime_eq_one`, `sieve_log_prime_sq_eq_half`, `sieve_cancellation_dipole`, `sieve_cancellation_mixed_tripole`, `sieve_cancellation_cubic_node`, `sieve_log_order_embed` |
| `TTP/MemoryKernel.lean` | Chapters 4, 9 (§4.1–4.3, §9.1) | `memoryKernel t`; `memoryKernel_sub_taylorLower`, `taylorUpper_sub_memoryKernel`, `taylorLower_remainder_pos`, `taylorUpper_remainder_pos`, `memoryKernel_taylor_sandwich`; `memoryJLower/Upper`, `memoryJ_bounds`; `CMI`, `CMI_three`; `tail_majorant_split`, `tail_sum_telescope`, `tail_sum_lt` |
| `TTP/ProperTimeWhitening.lean` | Chapters 3, 4, 6 (§3.3, §4.2–4.3, §6.3) | `PhaseDiodeChain4Open`; `phase_diode_chain4_iff_not_dvd`, `phase_diode_chain4_periodic`, `phase_diode_chain4_two_of_even`; `properTimeDefect`, `properTimeDefect_eq_zero_of_horizon`; `cmi_zero_of_vanishing_kernels`; `cca_composite_channel_annihilation`; `external_cmi_tail_lt` |
| `TTP/CholeskyRamanujan.lean` | Chapters 3, 6, 8 (§3.2, §6.1, §8.3–8.4) | `jordanTotient2`, `torusGram`, `choleskyRaw`, `choleskyInvRaw`; `sum_jordanTotient2_divisors`, `jordanTotient2_prime`, `torusGram_cholesky_factorization`, `cholesky_mobius_inversion`, `ramanujan_linear_drift_zero`, `ramanujan_totient_weight`, `torus_coboundary_prime_factor` |
| `TTP/FunctionFieldBridge.lean` | Chapter 8 (§8.4) | `poly_monic_mul_natDegree`, `poly_quadratic_degree_horizon`; `poly_shell_exact_dvd`, `poly_shell_zero_remainder`; `polyTailLayer`, `poly_tail_geometric_sum`, `poly_tail_geometric_lt`; `ramanujanWaveUnitInterval`, `ramanujanWaveUnitInterval_eq_zero` |
| `TTP/ToroidalMetricsAndRNS.lean` | Chapters 2, 5, 7, 8, 10 (§2.2–2.3, §5.2, §7.2, §8.1/8.3, §10.2) | `stormer_resonance_13090`, `dyadic_center_coprime`; `coboundary_telescope_sum`, `coboundary_telescope_bound`, `euler_operator_linear_fixed_point`; `purePrimeProjectorPower`, `purePrimeProjectorPower_eq_delta`; `dualAdder`, `dualAdder_eq_mod`, `dualAdder_lt`, `dualAdder_ne_zero_iff_phase_diode_open` |
| `TTP.lean` | Root module | Imports all 12 modules |

### 2.1. Key Results

- **Coprime crystal (Ch. 1).** For every `x : (ZMod (p_k#))ˣ`, the natural value
  `x.1.val` is coprime to the primorial `p_k#`.
- **Chord charge (Ch. 6).** `Φ_p(1) = p`, `Φ_{p^(k+1)}(1) = p`, and `Φ_q(1) = 1` for
  `ω(q) ≥ 2`. Moreover, for `q > 1`, `Φ_q(1) = 1 ↔ ¬ IsPrimePow q ↔ Λ(q) = 0`.
- **Nilpotence (Ch. 7).** If `n < B^m`, no sieve factorisation of `n` into `m` factors,
  each `≥ B`, exists.
- **`B²` horizon (Ch. 1, §1.4).** If every prime divisor of `n` is at least `B ≥ 2`
  and `n < B^2`, then `n` is prime; consequently `Φ_n(1) = n`.
- **Phase Diode (Ch. 3).** `PhaseDiodeOpen p n ↔ ¬ p ∣ n`, and
  `(n + Δ : ZMod p) = n + Δ`: the torus step is an additive homomorphism.
- **Sieve cancellation (Ch. 7).** `𝓛₂(pq) = 0`, `𝓛₃(p²q) = 0`, `𝓛₃(pqr) = 0`, while
  `𝓛₂(p²) = 1/2` and `𝓛₁(p) = 1`.
- **Memory kernel (Direction I).** `K(t) = (3+t)/((1-t)(1+t)²)` is sandwiched between
  `3-2t` and `3-2t+5t²` for `0 < t ≤ 1/2`; `0 < J_low(r) < J_high(r) < 1/(2r²)` for
  `r ≥ 2`; `CMI(3, p₀) = p₀(1-p₀)²J₁`; and the tail
  `∑_{i<N} 1/(2(B+i-2)(B+i-3)) = 1/(2(B-3)) - 1/(2(B+N-3)) < 1/(2(B-3))`
  for `B ≥ 4`, `N ≥ 1`.
- **Proper-time whitening (Direction II).** A 4-point chain on the `p`-axis is open iff
  `p` divides none of its nodes and is periodic in `u` with period `p`; for even shifts
  on the `p = 2` axis the chain is open iff `Odd u`; for `2 ≤ B`, `1 ≤ a`, `b ≤ B²`
  the proper-time defect satisfies `properTimeDefect B a b = 0`; for `ω(q) ≥ 2` we have
  `Φ_q(1) = 1 ∧ Λ(q) = 0`; the external memory tail is strictly `< 1/(2(B-3))`.
- **Cholesky–Ramanujan (Direction III).** `∑_{c∣g} J₂(c) = g²`, `J₂(p) = p²-1`;
  `𝒢_{d₁d₂} = (1/12) ∑_c J₂(c) L_{d₁c} L_{d₂c}`; `∑_d L⁻¹_{qd} L_{dc} = δ_{q,c}`;
  `∑_{d∣q} d·μ(q/d) = φ(q)`; `J₂(p)/φ(p)² = (p+1)/(p-1)`; `∑_{d∣q} μ(q/d) = 0` for
  `q > 1`.
- **Function fields (Direction IV).** A reducible monic `F` over `ZMod p` has a monic
  irreducible divisor `P` with `2·deg P ≤ deg F`; `q^d ∣ q^N` and
  `q^N / q^d = q^(N-d)`; the geometric tail
  `∑_{j<N} 1/(2(q²)^(d+j)) = (1 - (q²)^{-N}) / (2(q²-1)(q²)^(d-1))`
  is strictly `< 1/(2(q²-1)(q²)^(d-1))` for `N ≥ 1`; the Ramanujan wave vanishes
  identically on `[0, 1)` for `q > 1`.
- **Metrics and RNS (Chapters 2, 5, 7, 8, 10).** `M₈ ∣ (Δ*-1)Δ*(Δ*+1)` and
  `w_H(13090) = 3`; `Coprime ((2m+1)·M_odd + 2^s) (2·M_odd)` for odd `M_odd` and
  `s ≥ 1`; `∑_{i<L} (E(i+1) - E(i)) = E(L) - E(0)` is confined to `[-2C, 2C]`;
  `p/(p-1)·(x - x/p) = x`; `𝓛_k^Dir(p^m) = δ_{m,1}`; `dualAdder p r δ = (r+δ) % p < p`
  and `dualAdder p r δ ≠ 0 ↔ PhaseDiodeOpen p (r+δ)`.

## 3. Build and Reproduction

### Requirements

- `git`, `curl`, `elan` (Lean version manager);
- Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0`);
- Mathlib pinned in `lakefile.toml` (tag `v4.35.0`);
- about 8 GB of free disk space (Mathlib cache and build artefacts).

### Installation from scratch

The commands are identical on Linux, macOS, WSL2 and (with the native elan installer)
Windows. On Windows, WSL2 with Ubuntu 24.04 is recommended.

```bash
# 1. System dependencies (Debian/Ubuntu example)
sudo apt-get update
sudo apt-get install -y curl git build-essential

# 2. Install elan (skip if already installed)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 3. Clone and build
git clone <REPOSITORY_URL> ttp
cd ttp
lake exe cache get   # ≈ 6–7 GB of precompiled Mathlib oleans
lake build
```

### Commands

```bash
elan --version          # expected: elan 4.2.4 or newer
lake exe cache get      # fetch the Mathlib cache (≈ 9000 olean files)
lake build              # build all 12 modules
```

Checking a single file without a full build:

```bash
lake env lean path/to/File.lean
```

`lake exe cache get` is idempotent and downloads only missing artefacts.

### Editor setup

Install the `leanprover.lean4` extension in VS Code **in the same environment**
(native, Remote-WSL, Remote-SSH or a dev container) where the toolchain and the
Mathlib cache are installed, then open the repository folder. The Lean server reads
`lean-toolchain` and `lakefile.toml` automatically.

## 4. Verification Status

Verified in **Ubuntu 24.04 LTS (WSL2), x86_64**: Lean 4.35.0
(commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Lake 5.0.0, elan 4.2.4,
Mathlib `v4.35.0`. Verification date: 2026-11-14.

```
Build completed successfully (2924 jobs).
BUILD_EXIT=0
WARNINGS=0
ERRORS=0
SORRY=0
```

| Metric | Value |
|---|---|
| `lake build` exit code | **0** |
| Compiler warnings | **0** |
| Errors | **0** |
| `sorry` in the sources | **0** |
| Build jobs | 2924 |
| Modules in `TTP/` | **12** |
| Rebuild after touching any module | yes (verified) |

Every module was additionally checked by a standalone `lake env lean` file on concrete
values: `p = 2, 3, 5, 7, 11, 13`, `n = 6, 10, 12, 30`, `q = 3, 5, 7, 11`,
`r = 2, 3, 5`, `B = 2, 3, 4, 5`, `M = 6, 30`; for the polynomial bridge —
`p = 2, 3`, polynomials over `ZMod 2` and `ZMod 3`, `q = 2, 3`, `d = 1, 2, 3`,
`q_ram = 6, 30`; for the metric/RNS layer — `M_odd = 15, 105`, `m = 0, 1, 2`,
`s = 1, 2, 3, 4`, `m_pow = 1, 2, 3, 4, 6`, `p = 5, 7, 19`; all with `exit code 0`.

### Axiom audit

`docs/VERIFICATION_AUDIT.md` contains the full build log and the output of
`#print axioms` for 15 key theorems across all 12 modules. Every theorem depends only
on the standard Lean/Mathlib axioms `propext`, `Classical.choice`, `Quot.sound`
(`stormer_resonance_13090` uses only `propext`). There is **no `sorryAx`** and no
`Lean.ofReduceBool`; the proofs use `decide`/`norm_num`, never `native_decide`.

### RTL verification

The three SystemVerilog modules in `rtl/` are checked with

```bash
verilator --lint-only --sv --Wall rtl/ttp_dual_adder_cell.sv \
  rtl/ttp_phase_diode_rns16.sv rtl/ttp_vector_landing_unit.sv \
  --top-module ttp_vector_landing_unit
```

which exits with code `0` and no warnings. Each file contains exactly one `module`
… `endmodule`, balanced delimiters, and no integer division or remainder operator in
the datapath.

## 5. Repository Structure

```
ttp/
├── TTP.lean                       # root module (imports all 12 modules)
├── TTP/
│   ├── Basic.lean                 # Lake template module
│   ├── Definitions.lean           # Chapter 1: primorial, torus, crystal
│   ├── ChordCharge.lean           # Chapter 6: Φ_q(1), prime powers, Λ
│   ├── SieveNilpotence.lean       # Chapter 7: finite nilpotence
│   ├── ExactSieve.lean            # Chapters 1, 7: exact sieve, B² horizon
│   ├── PhaseDiode.lean            # Chapters 3, 9: phase diode
│   ├── CombinatorialSieve.lean    # Chapters 7, 9: 𝓛_k cancellation
│   ├── MemoryKernel.lean          # Chapters 4, 9: Shannon memory kernel
│   ├── ProperTimeWhitening.lean   # Chapters 3, 4, 6: proper-time whitening
│   ├── CholeskyRamanujan.lean     # Chapters 3, 6, 8: Cholesky–Ramanujan
│   ├── FunctionFieldBridge.lean   # Chapter 8: bridge to 𝔽_q[t]
│   └── ToroidalMetricsAndRNS.lean # Chapters 2, 5, 7, 8, 10: metrics and RNS
├── docs/
│   ├── monograph_v2.md            # full monograph (10 chapters, Russian)
│   ├── VERIFICATION_AUDIT.md      # build log and #print axioms report
│   └── figures/                   # monograph figures
├── rtl/
│   ├── ttp_dual_adder_cell.sv     # comparator-free Dual-Adder cell
│   ├── ttp_phase_diode_rns16.sv   # 16-channel Phase Diode RNS core
│   └── ttp_vector_landing_unit.sv # 32-slice vector landing unit
├── LICENSE                        # Apache License 2.0
├── README.md
├── lean-toolchain                 # leanprover/lean4:v4.35.0
├── lakefile.toml                  # dependencies and Mathlib linter options
├── lake-manifest.json
└── .github/workflows/             # CI: Lean Action CI, release, update
```

### Release artefacts

| Path | Description |
|---|---|
| `docs/monograph_v2.md` | Full monograph (10 chapters, Russian): TTP–CCA theory, proofs, tables and Lean listings |
| `docs/VERIFICATION_AUDIT.md` | Machine-readable report: `lake build` (`2924 jobs`, `sorry = 0`) and `#print axioms` for 15 key theorems |
| `rtl/` | Synthesizable SystemVerilog for the Divider-less RNS-16 coprocessor: `ttp_dual_adder_cell.sv`, `ttp_phase_diode_rns16.sv`, `ttp_vector_landing_unit.sv` |
| `LICENSE` | Apache License 2.0, Copyright 2026 Andrei Lukianchikov |

## 6. Methodology & Formal Verification

This work was developed using a four-stage **human-architected, AI-augmented, logically verified, oracle-free (HALO)** pipeline that strictly separates conceptual authorship from tactical proof search and mechanical verification:

1. **H — Human (Architect of Ontology & Constraints — Andrei Lukianchikov):** Originated the core mathematical paradigm (eliminating 1D coordinate confounding via the projective tower of primorial tori $\mathbb{T}^k$), set structural constraints against conventional heuristic dead-ends, and unified number theory, Shannon information theory, and RNS hardware design.
2. **A — AI Assistant & Agent (Conceptual Synthesis & Tactical Proof Search — Gemini & DeepSeek):** Translated geometric and information-theoretic insights into formal algebraic and analytic specifications, and performed iterative Lean 4 / Mathlib tactic search, type alignment, and SystemVerilog RTL drafting inside the development environment.
3. **L — Logical Prover (Deterministic Arbitration — Lean 4 Kernel + Verilator RTL lint):** The Lean 4 kernel provides formal machine certification of every theorem; Verilator performs static RTL linting (syntax and structural checks) and is not presented as a formal equivalence proof.
4. **O — Oracle-free Verification (Machine-Certified Truth — `2924` jobs, `sorry = 0`, standard axioms only):** No generative model is used as an oracle. The trusted base is the Lean 4 kernel together with the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; every claim must pass full mechanical certification.

The author assumes full scientific and intellectual responsibility for every definition, theorem statement, and interpretation in this repository and the accompanying monograph.

## 7. Technical Notes

- The project uses the Mathlib **module system**: each file starts with a copyright
  header and contains `module`, `public import` and `@[expose] public section`. This is
  required: with a plain `import`, declarations become private and are not accessible
  from other modules.
- `primorial` and `cyclotomicEvalOne` are **noncomputable** (they depend on `Nat.nth`
  and `Polynomial.cyclotomic`), so `#eval`/`decide` are not applicable to them; values
  are proved via `Nat.nth_prime_*` and `eval_one_cyclotomic_*`.
- `Nat.nth` is imported from `Mathlib.Data.Nat.Prime.Nth` (it is absent from
  `Mathlib.Data.Nat.Prime.Basic`).
- Mathlib 4.35 has no `Mathlib.Data.Rat.Basic` or
  `Mathlib.Data.List.BigOperators.Lemmas`; the project uses `Mathlib.Data.Rat.Defs` +
  `Mathlib.Data.Rat.Lemmas` and `Mathlib.Algebra.(Order.)BigOperators.Group.List.*`.
- `properTimeDefect` is **noncomputable**: its predicate contains an unbounded
  `∀ p, …`, so the definition uses `classical`; `Nat.sum_divisorsAntidiagonal` is
  applied explicitly (rewriting does not match the `f i.1 i.2` pattern).
- Matrix inversion uses the `Finset.sum_bij` bijection (`d ↦ d/c`), and `J₂` uses
  Möbius inversion via `sum_eq_iff_sum_mul_moebius_eq` together with `Nat.sum_totient`;
  in Mathlib 4.35 the lemma is `Nat.Prime.divisors`, not `Nat.divisors_prime`.
- The function-field bridge needs an explicit import of
  `Mathlib.Algebra.Field.ZMod`: the `Field (ZMod p)` instance is not part of
  `Mathlib.Data.ZMod.Basic`. `push_neg` is deprecated in 4.35; the project uses
  `push Not`.
- `poly_quadratic_degree_horizon` relies on the contrapositive of
  `Polynomial.irreducible_iff_lt_natDegree_lt` (a monic divisor of degree
  `≤ deg F / 2`) and on `Polynomial.monic_mul_leadingCoeff_inv` (monic normalisation
  of an irreducible divisor); the heartbeat limit is raised with an explanatory
  comment.
- `Mathlib.Algebra.Parity` is absent in 4.35: parity is imported from
  `Mathlib.Algebra.Ring.Parity`. The `dualAdder` cell is computable, so its values are
  checked with `decide`; the projector reuses `TTP.sum_moebius_divisors` from
  `CholeskyRamanujan`.
- All lines must fit within 100 characters (`linter.style.longLine`).
- Key supporting lemmas: `ZMod.val_coe_unit_coprime`,
  `Polynomial.eval_one_cyclotomic_not_prime_pow`,
  `Nat.squarefree_and_prime_pow_iff_prime`, `Nat.minFac_sq_le_self`,
  `List.pow_length_le_prod`, `ArithmeticFunction.vonMangoldt_eq_zero_iff`.
- The RTL `Dual-Adder` implements `dualAdder p r δ` without `%` or `/`: a carry-save
  adder and a 2:1 multiplexer select `r + δ` or `r + δ - p`. The vector landing unit
  instantiates 16 combinational `ttp_dual_adder_cell` cells per slice and reduces their
  `diode_open` outputs with a 16-input AND.

## 8. License and Citation

The code is distributed under the **Apache License 2.0**
(<https://www.apache.org/licenses/LICENSE-2.0>); see the `LICENSE` file
(Copyright 2026 Andrei Lukianchikov). If you use this work, please cite the repository:

```bibtex
@misc{ttp_lean_2026,
  title        = {Toroidal Theory of Primes (TTP) in Lean 4},
  author       = {Lukianchikov, Andrei},
  year         = {2026},
  howpublished = {\url{https://github.com/halo-science/ttp}},
  note         = {Formalisation in Lean 4 with Mathlib;
                  Zenodo DOI: \url{https://doi.org/10.5281/zenodo.24209738}}
}
```
