import RequestProject.TwoAdic.Target

/-!
# Corollary 1.2 of Paper II from Theorem 1.1 (II, §7)

Pure arithmetic.  For odd `s ≥ 7` take `d = s − 4` and `q = 2⌈7(s−2)/20⌉`; then `(q, d)` is
admissible and the window `{d+4, …, d+q}` of Theorem 1.1 lies in `[s, 1.7 s)`.  The explicit sets
come from `(q, d) = (4,3), (6,5), (8,7), (8,9)`.
-/

namespace TwoAdicWin

open Hankel2

/-- `q(s) = 2⌈7(s−2)/20⌉`, written with natural division. -/
def qOf (s : ℕ) : ℕ := 2 * ((7 * (s - 2) + 19) / 20)

/-- **Corollary 1.2, window part, from Theorem 1.1.** -/
theorem cor_window_of_thm (h : Thm11) : Cor12Window := by
  intro s hs h7
  obtain ⟨t, rfl⟩ := hs
  have hq4 : 4 ≤ qOf (2 * t + 1) := by unfold qOf; omega
  have hqe : Even (qOf (2 * t + 1)) := ⟨(7 * (2 * t + 1 - 2) + 19) / 20, by unfold qOf; ring⟩
  have hdo : Odd (2 * t + 1 - 4) := ⟨t - 2, by omega⟩
  have hqd : qOf (2 * t + 1) ≤ 2 * t + 1 - 4 + 1 := by unfold qOf; omega
  have h710 : 7 * (2 * t + 1 - 4 + 2) ≤ 10 * qOf (2 * t + 1) := by unfold qOf; omega
  obtain ⟨j, hj, hirr⟩ := h (qOf (2 * t + 1)) (2 * t + 1 - 4) hq4 hqe hdo hqd h710
  rw [Finset.mem_Icc] at hj
  refine ⟨2 * t + 1 - 4 + 2 * j + 2, ⟨t + j - 1, by omega⟩, by omega, ?_, hirr⟩
  have hj2 := hj.2
  unfold qOf at hj2
  omega

/-- **Corollary 1.2, explicit sets, from Theorem 1.1** (cases `(q,d) = (4,3), (6,5), (8,7), (8,9)`). -/
theorem cor_sets_of_thm (h : Thm11) : Cor12Sets := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hj, hirr⟩ := h 4 3 le_rfl ⟨2, rfl⟩ ⟨1, rfl⟩ le_rfl (by norm_num)
    have hj1 : j = 1 := by simp only [Finset.mem_Icc] at hj; omega
    subst hj1
    exact hirr
  · obtain ⟨j, hj, hirr⟩ := h 6 5 (by norm_num) ⟨3, rfl⟩ ⟨2, rfl⟩ (by norm_num) (by norm_num)
    simp only [Finset.mem_Icc] at hj
    refine ⟨5 + 2 * j + 2, ?_, hirr⟩
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> decide
  · obtain ⟨j, hj, hirr⟩ := h 8 7 (by norm_num) ⟨4, rfl⟩ ⟨3, rfl⟩ (by norm_num) (by norm_num)
    simp only [Finset.mem_Icc] at hj
    refine ⟨7 + 2 * j + 2, ?_, hirr⟩
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl <;> decide
  · obtain ⟨j, hj, hirr⟩ := h 8 9 (by norm_num) ⟨4, rfl⟩ ⟨4, rfl⟩ (by norm_num) (by norm_num)
    simp only [Finset.mem_Icc] at hj
    refine ⟨9 + 2 * j + 2, ?_, hirr⟩
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl <;> decide

end TwoAdicWin
