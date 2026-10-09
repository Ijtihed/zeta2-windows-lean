import RequestProject.Zeta7.Hankel2.CertCheck
import RequestProject.Zeta7.Hankel2.EulerGamma

/-!
# From a step majorant to the tabulated value of `c(κ)` (paper §8.5, Table 1)

* `log_twenty_gt`: `ln 20 > 2.9957` (from `ln 2 > 0.6931471803` and the series of `ln(4/5)`);
* **`cfunB_le`**: if `∑ h_i (a_i − a_{i−1}) ≤ S` and `κ ∈ [a, b] ⊆ [0, 3]`, then
  `c(κ) ≤ c` (for `c ≥ 0`) as soon as
  `a(6−a)(−0.5772 − 0.6931471803 − 2.9957) + S + 5b/20 + 12.5/400 ≤ 0.6931471803 c`
  (`A(κ) = κ(6−κ)` is increasing on `[0, 3]` and multiplies the negative constant
  `−γ − ln 2 − ln 20`; `γ ≥ 0.5772` is `EulerGamma.eulerMascheroni_ge`).
-/

open Finset

namespace Hankel2.CertC

open Hankel2.Fam3

/-- `ln 20 > 2.9957`. -/
theorem log_twenty_gt : (2.9957 : ℝ) < Real.log 20 := by
  have h2 := Real.log_two_gt_d9
  have hs := Real.abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ)) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlog : Real.log 20 = 4 * Real.log 2 - Real.log (4 / 5) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have habs := (abs_le.1 hs).2
  rw [hlog]
  norm_num at h2 ⊢
  linarith

/-- **The tabulated bound for `c(κ)` from a step majorant.** -/
theorem cfunB_le {K₁ K₂ : ℝ} (C : StepMajorant K₁ K₂) {S : ℝ}
    (hS : ∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc) ≤ S)
    {a b κ c : ℝ} (ha : 0 ≤ a) (hb : b ≤ 3) (hκ1 : a ≤ κ) (hκ2 : κ ≤ b)
    (hc0 : 0 ≤ c)
    (hc : a * (6 - a) * (-0.5772 - 0.6931471803 - 2.9957) + S + 5 * b / 20 + 12.5 / 400 ≤
      0.6931471803 * c) :
    cfunB C κ ≤ c := by
  have hγ := EulerGamma.eulerMascheroni_ge
  have h2 := Real.log_two_gt_d9
  have h20 := log_twenty_gt
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set E := -Real.eulerMascheroniConstant - Real.log 2 - Real.log 20
  have hE : E ≤ -0.5772 - 0.6931471803 - 2.9957 := by
    simp only [E]; norm_num at h2 ⊢; linarith
  have hA : a * (6 - a) ≤ κ * (6 - κ) := by nlinarith
  have hA0 : 0 ≤ a * (6 - a) := by nlinarith
  have hAE : κ * (6 - κ) * E ≤ a * (6 - a) * (-0.5772 - 0.6931471803 - 2.9957) := by
    have hEneg : E ≤ 0 := by linarith
    calc κ * (6 - κ) * E ≤ a * (6 - a) * E := mul_le_mul_of_nonpos_right hA hEneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hA0
  have hnum : κ * (6 - κ) * E + ∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc)
      + 5 * κ / 20 + 12.5 / 400 ≤ 0.6931471803 * c := by linarith
  unfold cfunB
  rw [one_div, inv_mul_le_iff₀ hl2]
  have : 0.6931471803 * c ≤ Real.log 2 * c := by
    norm_num at h2 ⊢; exact mul_le_mul_of_nonneg_right h2.le hc0
  linarith

end Hankel2.CertC
