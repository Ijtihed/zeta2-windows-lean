import RequestProject.TwoAdic.Main
import RequestProject.TwoAdic.DecayMain

/-!
# Paper II, Theorem 1.1 — field (i) `decay` discharged

`decay_field` proves field (i) of `TwoAdicInputs` (II, Theorem 3.1) from `decay_holds`.
`TwoAdicInputsOpen` is `TwoAdicInputs` without the discharged field, and
`thm_1_1_of_open_inputs` derives `Thm11` from the inputs not yet discharged at this stage.
-/

namespace TwoAdicWin

open Polynomial Finset Filter Topology Hankel2

/-- **Field (i) of `TwoAdicInputs`, discharged** (II, Theorem 3.1, 2-adic decay). -/
theorem decay_field : ∀ q d n : ℕ, Admissible q d → Even n → 0 < n →
    ‖(hankelL q d n (q * n)).det‖ ≤ (2 : ℝ) ^ (-decayExp q d n (q * n)) := by
  intro q d n hadm hn hn0
  obtain ⟨h4, hq, hd, -, -⟩ := hadm
  exact decay_holds hq hd hn (by omega) hn0

/-- The inputs of Paper II not yet discharged at this stage (all are discharged by `MainFinal`): all fields of `TwoAdicInputs` except the
discharged `decay` (field (i)). -/
structure TwoAdicInputsOpen where
  /-- (ii) The archimedean size. -/
  arch : ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    hankelPoly q d n (q * n) ≠ 0 →
      Real.log (PadicWin.l1Mv (hankelPoly q d n (q * n))) ≤
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2
  /-- (iii-a) The tree bound. -/
  tree : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ.Prime → ℓ ≠ 2 →
    negTop (PadicWin.gaussValMv ℓ (hankelPoly q d n (q * n))) ≤ TP q d n ℓ (q * n)
  /-- The circle-model integral of II, Cor. 5.4. -/
  circ : ℝ → ℝ
  /-- (iii-b) II, Cor. 5.4 (assembly). -/
  assembly : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertensOddSum Y - Real.log Y) atTop (𝓝 M₀) →
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) →
    ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
        ∑ ℓ ∈ S, (TPplus q d n ℓ (q * n) : ℝ) * Real.logb 2 ℓ ≤
          (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n
            + (q : ℝ) ^ 2 * Ctil M₀ circ (deltaOf q d) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2
  /-- (iii-c) II, Prop. 7.1 (the certificate), relaxed to `4.3892`. -/
  certificate : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 3 / 7 → Ctil mertensOddConst circ δ ≤ 4.3892
  /-- (iv) II, Theorem 6.4 (strict dominance at `ℓ = 2n+1`). -/
  nonvanishing : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ = 2 * n + 1 → ℓ.Prime →
    q + d + 1 < ℓ →
      (hankelPoly q d n (q * n)).coeff 0 ≠ 0 ∧
      padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) = -((q * n * (d + 2) : ℕ) : ℤ) ∧
      ∀ m, m ≠ 0 → (hankelPoly q d n (q * n)).coeff m ≠ 0 →
        padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) <
          padicValRat ℓ ((hankelPoly q d n (q * n)).coeff m)

/-- These inputs together with the proved decay give all inputs. -/
def TwoAdicInputsOpen.toInputs (I : TwoAdicInputsOpen) : TwoAdicInputs where
  decay := decay_field
  arch := I.arch
  tree := I.tree
  circ := I.circ
  assembly := I.assembly
  certificate := I.certificate
  nonvanishing := I.nonvanishing

/-- **Paper II, Theorem 1.1, from the inputs not yet discharged at this stage.** -/
theorem thm_1_1_of_open_inputs (I : TwoAdicInputsOpen) : Thm11 :=
  thm_1_1_of_inputs I.toInputs

/-- **Paper II, Corollary 1.2, from the inputs not yet discharged at this stage.** -/
theorem cor_1_2_of_open_inputs (I : TwoAdicInputsOpen) : Cor12Window ∧ Cor12Sets :=
  cor_1_2_of_thm (thm_1_1_of_open_inputs I)

end TwoAdicWin
