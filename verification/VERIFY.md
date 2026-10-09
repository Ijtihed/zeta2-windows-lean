# VERIFY.md

The logs below come from the development tree, which contains the 403 modules of `lean/RequestProject` together with
unused modules (8672 build jobs including Mathlib). After this run, doc-comments in the 403 modules were edited: references to files that
are not part of this repository were removed, references to the paper were updated to its final numbering, and
notes describing intermediate stages as open were corrected. No code changed: with all comments removed, every module
is identical to the verified one.

All blocks below are verbatim command outputs.

## 1. `lake clean` then `lake build 2>&1 | tee /tmp/build.log; echo EXIT=${PIPESTATUS[0]}`

### `tail -20 /tmp/build.log`
```
✔ [8653/8672] Built RequestProject.Zeta7.Hankel2.CertData.I0B1 (51s)
✔ [8654/8672] Built RequestProject.Zeta7.Hankel2.CertData.I0B0 (50s)
✔ [8655/8672] Built RequestProject.TwoAdic.CertFinal (16s)
✔ [8656/8672] Built RequestProject.Zeta35.MainFinal (13s)
✔ [8657/8672] Built RequestProject.TwoAdic.MainR2 (12s)
✔ [8658/8672] Built RequestProject.TwoAdic.AsmChain (15s)
✔ [8659/8672] Built RequestProject.TwoAdic.AssemblyField (29s)
✔ [8660/8672] Built RequestProject.Zeta7.Hankel2.CertData.Interval4 (83s)
✔ [8661/8672] Built RequestProject.TwoAdic.MainR3 (11s)
✔ [8662/8672] Built RequestProject.Zeta7.Hankel2.CertData.Interval3 (89s)
✔ [8663/8672] Built RequestProject.Zeta7.Hankel2.CertData.Interval2 (89s)
✔ [8664/8672] Built RequestProject.Zeta7.Hankel2.CertData.Interval1 (89s)
✔ [8665/8672] Built RequestProject.Zeta7.Hankel2.CertData.Interval0 (78s)
✔ [8666/8672] Built RequestProject.TwoAdic.ArchField (20s)
✔ [8667/8672] Built RequestProject.Zeta7.Hankel2.CertC (11s)
✔ [8668/8672] Built RequestProject.TwoAdic.MainFinal (11s)
✔ [8669/8672] Built RequestProject.Zeta7.Hankel2.Main2adicR6 (7.5s)
✔ [8670/8672] Built RequestProject.Zeta7.Hankel2.Main2adicR7 (22s)
✔ [8671/8672] Built RequestProject.Zeta7.Hankel2.Main2adicFinal (7.4s)
Build completed successfully (8672 jobs).
```

### EXIT code
```
EXIT=0
```

### `grep -c "error" /tmp/build.log`
```
0
```

## 2. `lake env lean scripts/print_axioms_final.lean`
```
'TwoAdicWin.thm_1_1_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.cor_1_2_window_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.cor_1_2_sets_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.Arch.arch_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.assembly_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.thm_1_1_of_inputs_r3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.cor_1_2_of_inputs_r3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.Arch.arch_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.Arch.EB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.Arch.g_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.Arch.quad_sig0_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicWin.LogEnergy.outer_energy_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicWin.l1Mv_det_le' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

## 3. `/tmp/Check.lean`

### `cat /tmp/Check.lean`
```
import RequestProject.TwoAdic.MainFinal
#check @TwoAdicWin.thm_1_1_final
#check @TwoAdicWin.cor_1_2_window_final
#check @TwoAdicWin.cor_1_2_sets_final
#print TwoAdicWin.Thm11
#print TwoAdicWin.Cor12Window
#print TwoAdicWin.Cor12Sets
#print Hankel2.zeta2
#print Hankel2.volkInt
#print Hankel2.volkSum
#print axioms TwoAdicWin.thm_1_1_final
#print axioms TwoAdicWin.cor_1_2_window_final
#print axioms TwoAdicWin.cor_1_2_sets_final
```

### `lake env lean /tmp/Check.lean`
```
TwoAdicWin.thm_1_1_final : TwoAdicWin.Thm11
TwoAdicWin.cor_1_2_window_final : TwoAdicWin.Cor12Window
TwoAdicWin.cor_1_2_sets_final : TwoAdicWin.Cor12Sets
def TwoAdicWin.Thm11 : Prop :=
∀ (q d : ℕ),
  4 ≤ q →
    Even q →
      Odd d →
        q ≤ d + 1 → 7 * (d + 2) ≤ 10 * q → ∃ j ∈ Finset.Icc 1 (q / 2 - 1), ∀ (r : ℚ), Hankel2.zeta2 (d + 2 * j + 2) ≠ ↑r
def TwoAdicWin.Cor12Window : Prop :=
∀ (s : ℕ), Odd s → 7 ≤ s → ∃ j, Odd j ∧ s ≤ j ∧ 10 * j < 17 * s ∧ ∀ (r : ℚ), Hankel2.zeta2 j ≠ ↑r
def TwoAdicWin.Cor12Sets : Prop :=
(∀ (r : ℚ), Hankel2.zeta2 7 ≠ ↑r) ∧
  (∃ j ∈ {9, 11}, ∀ (r : ℚ), Hankel2.zeta2 j ≠ ↑r) ∧
    (∃ j ∈ {11, 13, 15}, ∀ (r : ℚ), Hankel2.zeta2 j ≠ ↑r) ∧ ∃ j ∈ {13, 15, 17}, ∀ (r : ℚ), Hankel2.zeta2 j ≠ ↑r
def Hankel2.zeta2 : ℕ → ℚ_[2] :=
fun s => (Hankel2.volkInt 2 fun t => ((t + 1 / 2) ^ (s - 1))⁻¹) / (↑(s - 1) * 2 ^ s)
def Hankel2.volkInt : (p : ℕ) → [inst : Fact (Nat.Prime p)] → (ℚ_[p] → ℚ_[p]) → ℚ_[p] :=
fun p [Fact (Nat.Prime p)] f => limUnder Filter.atTop (Hankel2.volkSum p f)
def Hankel2.volkSum : (p : ℕ) → [inst : Fact (Nat.Prime p)] → (ℚ_[p] → ℚ_[p]) → ℕ → ℚ_[p] :=
fun p [Fact (Nat.Prime p)] f N => (↑p ^ N)⁻¹ * ∑ t ∈ Finset.range (p ^ N), f ↑t
'TwoAdicWin.thm_1_1_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.cor_1_2_window_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicWin.cor_1_2_sets_final' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

## 4. Kernel replay

### `lake env leanchecker RequestProject.TwoAdic.MainFinal` (output, then exit code)
```
EXIT=0
```

### `lake env leanchecker --fresh RequestProject.TwoAdic.MainFinal` (`date -u` before, output, exit code, `date -u` after)
```
Wed Oct  7 06:28:32 UTC 2026
EXIT=0
Wed Oct  7 07:08:23 UTC 2026
```

## 5. Git

### `git status --short` (before committing VERIFY.md)
```
?? VERIFY.md
```

### `git diff --stat d2984d2 HEAD` (d2984d2 = start of this task; after committing VERIFY.md)
```
 VERIFY.md | 127 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 127 insertions(+)
```
