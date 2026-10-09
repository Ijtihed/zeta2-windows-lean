import RequestProject.TwoAdic.AssemblyField

/-!
# Paper II, Theorem 1.1 — round 3: field `assembly` discharged

* `assembly_field` (`AssemblyField.lean`): the field `assembly` of `TwoAdicInputsR2` verbatim
  (II, Cor. 5.4), with `circ = circCert`.

`TwoAdicInputsR3` is `TwoAdicInputsR2` without `assembly`: its only field is `arch`, verbatim.
`toR2` rebuilds the round-2 inputs; `thm_1_1_of_inputs_r3` and `cor_1_2_of_inputs_r3` derive
Theorem 1.1 and Corollary 1.2 from the archimedean field alone.
-/

namespace TwoAdicWin

/-- The inputs of Paper II not yet discharged at stage 3: the archimedean bound only (discharged in `MainFinal`). -/
structure TwoAdicInputsR3 where
  /-- (ii) The archimedean size. -/
  arch : ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    hankelPoly q d n (q * n) ≠ 0 →
      Real.log (PadicWin.l1Mv (hankelPoly q d n (q * n))) ≤
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2

/-- The round-3 inputs together with `assembly_field` give the round-2 inputs. -/
def TwoAdicInputsR3.toR2 (I : TwoAdicInputsR3) : TwoAdicInputsR2 where
  arch := I.arch
  assembly := assembly_field

/-- **Paper II, Theorem 1.1, from the archimedean field alone.** -/
theorem thm_1_1_of_inputs_r3 (I : TwoAdicInputsR3) : Thm11 :=
  thm_1_1_of_inputs_r2 I.toR2

/-- **Paper II, Corollary 1.2, from the archimedean field alone.** -/
theorem cor_1_2_of_inputs_r3 (I : TwoAdicInputsR3) : Cor12Window ∧ Cor12Sets :=
  cor_1_2_of_inputs_r2 I.toR2

end TwoAdicWin
