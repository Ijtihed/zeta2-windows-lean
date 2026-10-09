import RequestProject.TwoAdic.ArchField

/-!
# Paper II: Theorem 1.1 and Corollary 1.2, unconditionally

All inputs of `TwoAdicInputsR3` are now proved: its only field `arch` is `Arch.arch_field`
(II Theorem 4.1; P, Theorem 6.1).  Together with the fields discharged in rounds 1–3
(`decay_field`, `tree_field`, `circCert`, `certificate_field`, `Dom.nonvanishing_field`,
`assembly_field`), this gives Theorem 1.1 for every admissible `(q, d)`.  Corollary 1.2 is
derived from Theorem 1.1 by `cor_1_2_of_thm`; in particular `Cor12Sets` comes from `Thm11` at
`(q, d) = (4, 3), (6, 5), (8, 7), (8, 9)`.
-/

namespace TwoAdicWin

/-- The inputs of round 3, all proved. -/
def inputsR3 : TwoAdicInputsR3 where
  arch := Arch.arch_field

/-- **Paper II, Theorem 1.1.** -/
theorem thm_1_1_final : Thm11 := thm_1_1_of_inputs_r3 inputsR3

/-- **Paper II, Corollary 1.2 (window form)**, from Theorem 1.1. -/
theorem cor_1_2_window_final : Cor12Window := (cor_1_2_of_thm thm_1_1_final).1

/-- **Paper II, Corollary 1.2 (sets form)**, from Theorem 1.1. -/
theorem cor_1_2_sets_final : Cor12Sets := (cor_1_2_of_thm thm_1_1_final).2

end TwoAdicWin
