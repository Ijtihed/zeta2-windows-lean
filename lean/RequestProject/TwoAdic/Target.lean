import RequestProject.Zeta7.Hankel2.Volkenborn

/-!
# The fixed targets for Paper II

The 2-adic zeta value is `Hankel2.zeta2` from the ζ₂(7) library (unchanged):

  `zeta2 s = (∫_{ℤ₂} (t + 1/2)^{-(s-1)} dt) / ((s - 1) · 2^s)`,

that is, the normalisation `I_M = ∫_{ℤ₂} (t + 1/2)^{-M} dt = M · 2^{M+1} · ζ₂(M+1)` of Paper II,
Lemma 2.1 (normalisation), with `M = s - 1`.  The integral is the Volkenborn integral `Hankel2.volkInt 2`.
Its identification with the Kubota–Leopoldt value `L₂(s, ω^{1-s})` is the classical fact cited in
Paper II ([LSZ]); it is not formalised here.

The propositions below are the statements of Paper II, Theorem 1.1 and Corollary 1.2, written out
in full.  The final theorems of the project must prove them with no hypotheses:

* `theorem TwoAdicWin.thm_1_1_final : TwoAdicWin.Thm11`
* `theorem TwoAdicWin.cor_1_2_window_final : TwoAdicWin.Cor12Window`
* `theorem TwoAdicWin.cor_1_2_sets_final : TwoAdicWin.Cor12Sets`

This file must not be changed.
-/

namespace TwoAdicWin

open Hankel2

/-- **Paper II, Theorem 1.1.**  Let `q ≥ 4` be even and `d` odd with `q ≤ d + 1` and
`(d + 2)/q ≤ 10/7`.  Then at least one of `ζ₂(d+4), ζ₂(d+6), …, ζ₂(d+q)` is irrational.
(The values are `ζ₂(d + 2j + 2)` for `1 ≤ j ≤ q/2 - 1`.) -/
def Thm11 : Prop :=
  ∀ q d : ℕ, 4 ≤ q → Even q → Odd d → q ≤ d + 1 → 7 * (d + 2) ≤ 10 * q →
    ∃ j ∈ Finset.Icc 1 (q / 2 - 1), ∀ r : ℚ, zeta2 (d + 2 * j + 2) ≠ (r : ℚ_[2])

/-- **Paper II, Corollary 1.2, window part.**  For every odd `s ≥ 7` there is an odd `j` with
`s ≤ j < 1.7 s` and `ζ₂(j)` irrational. -/
def Cor12Window : Prop :=
  ∀ s : ℕ, Odd s → 7 ≤ s →
    ∃ j : ℕ, Odd j ∧ s ≤ j ∧ 10 * j < 17 * s ∧ ∀ r : ℚ, zeta2 j ≠ (r : ℚ_[2])

/-- **Paper II, Corollary 1.2, explicit sets.**  `ζ₂(7)` is irrational, and each of
`{ζ₂(9), ζ₂(11)}`, `{ζ₂(11), ζ₂(13), ζ₂(15)}` and `{ζ₂(13), ζ₂(15), ζ₂(17)}` contains an
irrational number. -/
def Cor12Sets : Prop :=
  (∀ r : ℚ, zeta2 7 ≠ (r : ℚ_[2])) ∧
  (∃ j ∈ ({9, 11} : Finset ℕ), ∀ r : ℚ, zeta2 j ≠ (r : ℚ_[2])) ∧
  (∃ j ∈ ({11, 13, 15} : Finset ℕ), ∀ r : ℚ, zeta2 j ≠ (r : ℚ_[2])) ∧
  (∃ j ∈ ({13, 15, 17} : Finset ℕ), ∀ r : ℚ, zeta2 j ≠ (r : ℚ_[2]))

end TwoAdicWin
