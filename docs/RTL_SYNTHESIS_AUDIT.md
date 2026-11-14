# RTL Synthesis and Simulation Audit — TTP v1.1.0

## 1. Environment

| Component | Version |
|---|---|
| WSL | Ubuntu 24.04.5 LTS |
| Verilator | 5.020 (Debian 5.020-1) |
| Yosys | 0.33 (git sha1 2584903a060) |
| Python | 3.12.3 (metrology scripts, not used by RTL) |

All commands below are run from the repository root:

```bash
cd /mnt/d/___Work/TTP
```

## 2. RTL and testbench files

| File | Role |
|---|---|
| `rtl/ttp_dual_adder_cell.sv` | Comparator-free Dual-Adder cell, parameters `W`, `P` |
| `rtl/ttp_phase_diode_rns16.sv` | 16-channel RNS phase-diode core, `M16 = 53#` |
| `rtl/ttp_vector_landing_unit.sv` | 32-slice vector landing unit |
| `rtl/tb/tb_ttp_rns16.sv` | Self-checking testbench |
| `rtl/tb/ref_div64_checker.sv` | 64-bit reference divisibility checker using `%` |
| `rtl/tb/synth_yosys.ys` | Yosys synthesis flow |

## 3. RTL changes required for Yosys 0.33

The functional RTL was preserved; two synthesis-compatibility changes were made:

1. `` `timescale 1ns/1ps `` was added to the three RTL modules so that
   Verilator `--Wall` does not emit `TIMESCALEMOD` warnings.
2. `rtl/ttp_phase_diode_rns16.sv` previously used unpacked-array localparams
   (`localparam int unsigned W_ARR [16] = '{...};`) inside a `generate` loop.
   Yosys 0.33 rejects that construct. The 16 channels are now instantiated
   explicitly with the same `W`, `P`, offsets and port connections.

Behavioral equivalence after the rewrite was re-verified by the full Verilator
testbench: `TB PASS: 155974 checks, 0 errors`.

## 4. Verilator simulation

### Build and run

```bash
verilator --binary --sv --Wall --timing -j 4 \
  --top-module tb_ttp_rns16 \
  -Irtl -Irtl/tb \
  rtl/ttp_dual_adder_cell.sv \
  rtl/ttp_phase_diode_rns16.sv \
  rtl/ttp_vector_landing_unit.sv \
  rtl/tb/tb_ttp_rns16.sv \
  -o tb_ttp_rns16

./obj_dir/tb_ttp_rns16
```

Build result: `VERILATOR_BUILD_EXIT=0`, no `%Warning` and no `%Error`.
Simulation result: `VERILATOR_RUN_EXIT=0`.

### Simulation log

```text
==============================================================================
TTP RNS-16 SELF-CHECKING TESTBENCH
M16 = 53# = 32589158477190044730 = 128'h0000000000000001c443f2f861d29c3a
==============================================================================
  dual-adder exhaustive checks: P=2,3,5,53 passed
  phase-diode references: 1, 1e6, 1e12, 2e19, 2^64-1 (10,000 steps each)
  vector landing checks: 6 anchors x 33 requests passed
==============================================================================
TB PASS: 155974 checks, 0 errors
==============================================================================
- rtl/tb/tb_ttp_rns16.sv:359: Verilog $finish
```

### Coverage

* **Dual-Adder:** exhaustive over all `(r_in, delta_in) in [0, P-1]^2` for
  `P = 2, 3, 5, 53` (`W = 1, 2, 3, 6`).  Both `r_next == (r_in+delta_in) % P`
  and `diode_open == (r_next != 0)` are checked.
* **Phase-Diode RNS-16:** five reference points
  (`1`, `10^6`, `10^12`, `2*10^19`, `2^64-1`), 10,000 sequential steps each.
  Every step checks `r_state_bus`, `channel_open`, and `all_open` against
  `gcd(n, M16) == 1`; the literal 128-bit `gcd(n, M16)` is additionally
  evaluated at steps `k % 997 == 0` and at the final step.
* **Vector landing unit:** six anchors (`1001`, `1025`, `1501`, `2001`,
  `10^6`, `10^12`) times 33 `delta_n_req` values.  For the four small anchors
  the first open shift is additionally verified to land on a prime
  (`n0 + landing_offset_even < 53^2`).

### Verilator 5.020 workaround

Verilator 5.020 does not propagate later procedural updates of an
unpacked-array input port (`delta_rom`) to the generated slice cells.  The
testbench therefore drives the constant `delta_rom` at time 0, before any
delays; the packed anchor and `delta_n_req` are updated normally.

## 5. Yosys synthesis

### Command

```bash
yosys -s rtl/tb/synth_yosys.ys
```

Flow per top: `read_verilog -sv` → `synth -top` → `flatten` →
`abc -g AND,OR,XOR,MUX` → `opt_clean` → `stat` → `ltp -noff`.

The `ref_div64_checker` synthesis is dominated by the expansion of 16
constant 64-bit `%` operators; it took about 11 minutes on this machine.
The final `flatten` pass changes the reference count from the pre-flatten
`18 601` to `18 763` cells and the critical path from `460` to `459` levels.
The dual-adder and phase-diode tops complete in under a minute.

### Synthesis results

| Block | Cells | AND | OR | XOR | MUX | NOT | DFF | Critical path (levels) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `ttp_dual_adder_cell` (`P=53`, `W=6`) | **67** | 19 | 18 | 21 | 5 | 4 | 0 | **16** |
| `ttp_phase_diode_rns16` (`M16 = 53#`) | **898** | 230 | 201 | 229 | 119 | 47 | **72** | **20** |
| `ref_div64_checker` (64-bit, 16 primes) | **18 763** | 5 855 | 5 261 | 2 913 | 986 | 3 748 | 0 | **459** |

Cell sums: `19+18+21+5+4 = 67`; `230+201+229+119+47+72 = 898`;
`5855+5261+2913+986+3748 = 18 763`.

### Yosys log excerpt

```text
=== ttp_dual_adder_cell ===
   Number of cells:                 67
     $_AND_                         19
     $_MUX_                          5
     $_NOT_                          4
     $_OR_                          18
     $_XOR_                         21

Longest topological path in ttp_dual_adder_cell (length=16):

=== ttp_phase_diode_rns16 ===
   Number of cells:                898
     $_AND_                        230
     $_DFFE_PN0P_                   72
     $_MUX_                        119
     $_NOT_                         47
     $_OR_                         201
     $_XOR_                        229

Longest topological path in ttp_phase_diode_rns16 (length=20):

=== ref_div64_checker ===
   Number of cells:              18763
     $_AND_                       5855
     $_MUX_                        986
     $_NOT_                       3748
     $_OR_                        5261
     $_XOR_                       2913

Longest topological path in ref_div64_checker (length=459):
```

## 6. Comparative analysis

* The Dual-Adder cell needs **67 gates** per axis and has a critical path of
  **16 levels**.
* The full 16-channel Phase-Diode core needs **898 gates** and **72 DFFs**
  (one 72-bit register file), with a critical path of **20 levels**.
* The `%`-based 64-bit reference checker needs **18 763 gates**, i.e.
  **280.0×** the Dual-Adder cell and **20.9×** the entire 16-channel core.
  Per axis the reference is `18 763 / 16 ≈ 1 173` gates versus 67 gates for
  the Dual-Adder cell (a factor of about **17.5×**).
* The reference critical path is **459 levels**, i.e. **23×** the phase core
  and **28.7×** the Dual-Adder cell.
* The phase core has no inter-channel carry: all 16 channels are independent
  combinational Dual-Adders followed by a 4-level AND tree and a single
  72-bit register update.  The 72 DFFs are exactly the RNS state bus.

## 7. Reproduction checklist

```bash
cd /mnt/d/___Work/TTP

# 1. Simulation (0 warnings, 0 errors)
verilator --binary --sv --Wall --timing -j 4 \
  --top-module tb_ttp_rns16 \
  -Irtl -Irtl/tb \
  rtl/ttp_dual_adder_cell.sv \
  rtl/ttp_phase_diode_rns16.sv \
  rtl/ttp_vector_landing_unit.sv \
  rtl/tb/tb_ttp_rns16.sv \
  -o tb_ttp_rns16
./obj_dir/tb_ttp_rns16

# 2. Gate-level synthesis (about 11 minutes; dominated by ref_div64_checker)
yosys -s rtl/tb/synth_yosys.ys
```

Status: Verilator `TB PASS`, Yosys all three tops completed with the cell
counts and critical paths above.  No commit or push was performed for this
stage.
