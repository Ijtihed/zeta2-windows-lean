import RequestProject.TwoAdic.MainR1
import RequestProject.TwoAdic.TreeBound
import RequestProject.TwoAdic.CertFinal
import RequestProject.TwoAdic.NVMain

/-!
# Paper II, Theorem 1.1 — round 2: fields `tree`, `circ`, `certificate`, `nonvanishing` discharged

* `tree_field` (`TreeBound.lean`): field (iii-a) `tree`, II Theorem A.2, for general `q` and the
  multivariable Hankel polynomial, for every prime `ℓ`;
* `circ := circCert` (`CertFinal.lean`): the circle-model integral of II, Cor. 5.4, with the class
  types and measures of the certificate file;
* `certificate_field` (`CertFinal.lean`): field (iii-c) `certificate`, II Prop. 7.1,
  `C̃(δ) ≤ 4.3892` for `0 ≤ δ ≤ 3/7`, from the kernel-checked certificate;
* `Dom.nonvanishing_field` (`NVMain.lean`): field (iv) `nonvanishing`, II Theorem 6.4 (strict
  dominance at `ℓ = 2n + 1`), for all admissible `(q, d)`.

`TwoAdicInputsR2` is `TwoAdicInputsOpen` without these four fields; its `assembly` field is the
field (iii-b) of `TwoAdicInputsOpen` verbatim with `circ = circCert`.  `toOpen` rebuilds the open
inputs, and `thm_1_1_of_inputs_r2`, `cor_1_2_of_inputs_r2` derive Theorem 1.1 and Corollary 1.2 from
the remaining open fields `arch` and `assembly`.
-/

namespace TwoAdicWin

open Polynomial Finset Filter Topology Hankel2

/-- The inputs of Paper II not yet discharged at stage 2 (all are discharged by `MainFinal`). -/
structure TwoAdicInputsR2 where
  /-- (ii) The archimedean size. -/
  arch : ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    hankelPoly q d n (q * n) ≠ 0 →
      Real.log (PadicWin.l1Mv (hankelPoly q d n (q * n))) ≤
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2
  /-- (iii-b) II, Cor. 5.4 (assembly), with the circle-model integral
  `circ = circCert` of the certificate's class types. -/
  assembly : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertensOddSum Y - Real.log Y) atTop (𝓝 M₀) →
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) →
    ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
        ∑ ℓ ∈ S, (TPplus q d n ℓ (q * n) : ℝ) * Real.logb 2 ℓ ≤
          (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n
            + (q : ℝ) ^ 2 * Ctil M₀ circCert (deltaOf q d) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2

/-- The round-2 inputs together with the discharged fields give the inputs of stage 1. -/
noncomputable def TwoAdicInputsR2.toOpen (I : TwoAdicInputsR2) : TwoAdicInputsOpen where
  arch := I.arch
  tree := tree_field
  circ := circCert
  assembly := I.assembly
  certificate := certificate_field
  nonvanishing := Dom.nonvanishing_field

/-- **Paper II, Theorem 1.1, from the inputs of stage 2.** -/
theorem thm_1_1_of_inputs_r2 (I : TwoAdicInputsR2) : Thm11 :=
  thm_1_1_of_open_inputs I.toOpen

/-- **Paper II, Corollary 1.2, from the inputs of stage 2.** -/
theorem cor_1_2_of_inputs_r2 (I : TwoAdicInputsR2) : Cor12Window ∧ Cor12Sets :=
  cor_1_2_of_open_inputs I.toOpen

end TwoAdicWin
