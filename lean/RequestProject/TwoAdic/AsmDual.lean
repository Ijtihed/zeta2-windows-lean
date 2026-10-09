import Mathlib

/-!
# Weak duality for class sums

For classes `c ∈ C` (`|C| = M > 0`) with loads `S_c` summing to `K` and slopes `β_c`:

* **`weak_duality`**: `∑_c (S_c β_c − S_c²) ≤ K β̄ − K²/M + ∑_c (β_c − β̄)²/4`, `β̄ = ∑ β/M`
  (weak duality at `λ = β̄ − 2K/M`);
* **`popoviciu`**: if all `β_c` lie in an interval of length `w`, then `∑_c (β_c − β̄)² ≤ M w²/4`.
-/

open Finset

namespace TwoAdicWin.Asm

theorem weak_duality {ι : Type*} (C : Finset ι) (S β : ι → ℝ) (K : ℝ) (hC : 0 < C.card)
    (hS : ∑ c ∈ C, S c = K) :
    ∑ c ∈ C, (S c * β c - S c ^ 2) ≤
      K * ((∑ c ∈ C, β c) / C.card) - K ^ 2 / C.card +
        ∑ c ∈ C, (β c - (∑ c ∈ C, β c) / C.card) ^ 2 / 4 := by
  set M : ℝ := (C.card : ℝ) with hMdef
  have hM : 0 < M := by rw [hMdef]; exact_mod_cast hC
  set bb : ℝ := (∑ c ∈ C, β c) / M
  set lam : ℝ := bb - 2 * K / M
  have h1 : ∀ c ∈ C, S c * β c - S c ^ 2 ≤ lam * S c + (β c - lam) ^ 2 / 4 := by
    intro c _
    nlinarith [sq_nonneg ((β c - lam) / 2 - S c)]
  have h2 := sum_le_sum h1
  rw [sum_add_distrib, ← mul_sum, hS] at h2
  have hsum : ∑ c ∈ C, (β c - bb) = 0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← hMdef]
    simp only [bb]; field_simp; ring
  have h3 : ∑ c ∈ C, (β c - lam) ^ 2 / 4 =
      ∑ c ∈ C, (β c - bb) ^ 2 / 4 + K / M * ∑ c ∈ C, (β c - bb) + K ^ 2 / M := by
    have : ∀ c ∈ C, (β c - lam) ^ 2 / 4 = (β c - bb) ^ 2 / 4 + K / M * (β c - bb) + K ^ 2 / M / M := by
      intro c _; simp only [lam]; field_simp; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    simp only [M]; field_simp
  rw [h3, hsum] at h2
  have : lam * K + (∑ c ∈ C, (β c - bb) ^ 2 / 4 + K / M * 0 + K ^ 2 / M) =
      K * bb - K ^ 2 / M + ∑ c ∈ C, (β c - bb) ^ 2 / 4 := by
    simp only [lam]; field_simp; ring
  linarith

theorem popoviciu {ι : Type*} (C : Finset ι) (β : ι → ℝ) (m w : ℝ) (hC : 0 < C.card)
    (hβ : ∀ c ∈ C, m ≤ β c ∧ β c ≤ m + w) :
    ∑ c ∈ C, (β c - (∑ c ∈ C, β c) / C.card) ^ 2 ≤ C.card * w ^ 2 / 4 := by
  set M : ℝ := (C.card : ℝ) with hMdef
  have hM : 0 < M := by rw [hMdef]; exact_mod_cast hC
  set bb : ℝ := (∑ c ∈ C, β c) / M
  have hsum : ∑ c ∈ C, (β c - m) = M * (bb - m) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← hMdef]
    simp only [bb]; field_simp
  have e : ∑ c ∈ C, (β c - bb) ^ 2 = ∑ c ∈ C, (β c - m) ^ 2 - M * (bb - m) ^ 2 := by
    have : ∀ c ∈ C, (β c - bb) ^ 2 = (β c - m) ^ 2 - 2 * (bb - m) * (β c - m) + (bb - m) ^ 2 := by
      intro c _; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum, sum_const,
      nsmul_eq_mul]
    ring
  have h1 : ∑ c ∈ C, (β c - m) ^ 2 ≤ ∑ c ∈ C, w * (β c - m) := by
    refine sum_le_sum fun c hc => ?_
    obtain ⟨h1, h2⟩ := hβ c hc
    nlinarith
  rw [← mul_sum, hsum] at h1
  rw [e]
  nlinarith [sq_nonneg (bb - m - w / 2)]

end TwoAdicWin.Asm
