import RequestProject.TwoAdic.NVHk
import RequestProject.Zeta7.Hankel2.ArchTaylor
import RequestProject.Frame.L1Mv

/-!
# Archimedean bounds for the local data

* `Hk_zero_eq`: `h_k = H_k[0] = ∏_j (ez_j/2)^q ∏_{k' ≠ k} (k' − k)^{−q}`, where
  `ez_j/2 = −k − z_j` (a half-odd integer, so `|ez_j/2| ≥ 1/2`);
* `log_abs_Hk_zero`: `ln|h_k| = q ∑_j ln|ez_j/2| − q ∑_{k' ≠ k} ln|k' − k|` (exact);
* `abs_Hk_le`: `|H_k[b]| ≤ |h_k| Λ^b`, `Λ = q(2n + 2R + 1)` (roots and poles of the normalised
  local weight have absolute value `≥ 1/2`);
* `abs_Tk_le`: `|T_k(M)| ≤ 2M 2^{M+1}` (harmonic sums of order `M + 1 ≥ 2`);
* `l1_cMv_le`: `‖c_{k,m}‖₁ ≤ Q |h_k|`, `Q = q C_{q,d} Λ^q`, `C_{q,d} = 2q(q+d)^{d+1} 2^{q+d+1}`.
-/

open Finset Polynomial PadicWin Hankel2.ArchB

namespace TwoAdicWin.Arch

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

/-- `|ez/2| ≥ 1/2` for even `n` (`ez = 2j + 1 − 2k − n` is odd). -/
theorem abs_ez_half_ge {n : ℕ} (hn : Even n) (j : ℕ) (k : ℤ) :
    (1 / 2 : ℝ) ≤ |(((Dom.ez n j k : ℚ) / 2 : ℚ) : ℝ)| := by
  obtain ⟨m, rfl⟩ := hn
  have hne : Dom.ez (m + m) j k ≠ 0 := by unfold Dom.ez; push_cast; omega
  have h1 : (1 : ℝ) ≤ |((Dom.ez (m + m) j k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
  push_cast
  rw [abs_div, abs_two]
  linarith

theorem ez_half_ne_zero {n : ℕ} (hn : Even n) (j : ℕ) (k : ℤ) : ((Dom.ez n j k : ℚ) / 2) ≠ 0 := by
  intro h
  have := abs_ez_half_ge hn j k
  rw [h] at this
  norm_num at this

theorem Hk_zero_eq (q n : ℕ) (k : ℤ) :
    Hk q n k 0 = (∏ j ∈ range n, ((Dom.ez n j k : ℚ) / 2) ^ q) *
      ∏ k' ∈ (nodes n).erase k, (((k' - k : ℤ) : ℚ)⁻¹) ^ q := by
  rw [Dom.Hk_eq_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_prod, map_prod]
  congr 1
  · refine prod_congr rfl fun j _ => ?_
    simp
  · refine prod_congr rfl fun k' _ => ?_
    rw [map_pow, PowerSeries.constantCoeff_inv]
    simp

theorem Hk_zero_ne_zero {q n : ℕ} (hn : Even n) (k : ℤ) : Hk q n k 0 ≠ 0 := by
  rw [Hk_zero_eq]
  refine mul_ne_zero (prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (ez_half_ne_zero hn j k))
    (prod_ne_zero_iff.2 fun k' hk' => pow_ne_zero _ (inv_ne_zero ?_))
  exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk')

/-- **`ln|h_k|`, exactly.** -/
theorem log_abs_Hk_zero {q n : ℕ} (hn : Even n) (k : ℤ) :
    Real.log |((Hk q n k 0 : ℚ) : ℝ)| =
      q * ∑ j ∈ range n, Real.log |(((Dom.ez n j k : ℚ) / 2 : ℚ) : ℝ)| -
        q * ∑ k' ∈ (nodes n).erase k, Real.log |((k' - k : ℤ) : ℝ)| := by
  have hA' : ∀ j ∈ range n, |((((Dom.ez n j k : ℚ) / 2) ^ q : ℚ) : ℝ)| ≠ 0 := fun j _ =>
    abs_ne_zero.2 (by rw [Rat.cast_ne_zero]; exact pow_ne_zero _ (ez_half_ne_zero hn j k))
  have hB' : ∀ k' ∈ (nodes n).erase k, |(((((k' - k : ℤ) : ℚ)⁻¹) ^ q : ℚ) : ℝ)| ≠ 0 :=
    fun k' hk' => abs_ne_zero.2 (by
      rw [Rat.cast_ne_zero]
      exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk'))))
  have hA : |((∏ j ∈ range n, ((Dom.ez n j k : ℚ) / 2) ^ q : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.2 (by
      rw [Rat.cast_ne_zero]
      exact prod_ne_zero_iff.2 fun j _ => pow_ne_zero q (ez_half_ne_zero hn j k))
  have hB : |((∏ k' ∈ (nodes n).erase k, (((k' - k : ℤ) : ℚ)⁻¹) ^ q : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.2 (by
      rw [Rat.cast_ne_zero]
      exact prod_ne_zero_iff.2 fun k' hk' =>
        pow_ne_zero _ (inv_ne_zero (by exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk'))))
  rw [Hk_zero_eq, Rat.cast_mul, abs_mul, Real.log_mul, Rat.cast_prod, Rat.cast_prod, abs_prod,
    abs_prod, Real.log_prod, Real.log_prod, mul_sum, mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
  · congr 1
    · refine sum_congr rfl fun j _ => ?_
      rw [Rat.cast_pow, abs_pow, Real.log_pow]
    · refine sum_congr rfl fun k' _ => ?_
      rw [Rat.cast_pow, Rat.cast_inv, abs_pow, abs_inv, Real.log_pow, Real.log_inv]
      push_cast; ring
  all_goals first | exact hA | exact hB | exact hA' | exact hB'

/-- `Λ = q (2n + 2R + 1)`. -/
noncomputable def LamT (q n : ℕ) : ℝ := q * (2 * n + (2 * R n + 1 : ℕ))

theorem LamT_nonneg (q n : ℕ) : 0 ≤ LamT q n := by unfold LamT; positivity

/-- **`|H_k[b]| ≤ |h_k| Λ^b`**. -/
theorem abs_Hk_le {q n : ℕ} (hn : Even n) (k : ℤ) (b : ℕ) :
    |((Hk q n k b : ℚ) : ℝ)| ≤ |((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ b := by
  have hz : ∀ j ∈ range n, SerBound ((PowerSeries.C ((Dom.ez n j k : ℚ) / 2) + PowerSeries.X) ^ q)
      (|(((Dom.ez n j k : ℚ) / 2 : ℚ) : ℝ)| ^ q) ((q : ℝ) * 2) := by
    intro j _
    have h := SerBound.lin (d := (Dom.ez n j k : ℚ) / 2) (e := 1) (ez_half_ne_zero hn j k)
    rw [map_one, one_mul] at h
    have h2 := (h.pow (abs_nonneg _) (by positivity) q)
    refine h2.mono (by positivity) (by positivity) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_ez_half_ge hn j k
    rw [Rat.cast_one, abs_one, div_le_iff₀ (by linarith)]
    linarith
  have hp : ∀ k' ∈ (nodes n).erase k, SerBound
      ((PowerSeries.C (((k' - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q)
      ((|(((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ q) ((q : ℝ) * 1) := by
    intro k' hk'
    have hne : (((k' - k : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk')
    have h := (SerBound.inv_lin hne).pow (by positivity) (by positivity) q
    refine h.mono (by positivity) (by positivity) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : (1 : ℝ) ≤ |(((k' - k : ℤ) : ℚ) : ℝ)| := by
      have := Int.one_le_abs (sub_ne_zero.2 (ne_of_mem_erase hk'))
      push_cast; exact_mod_cast this
    exact inv_le_one_of_one_le₀ h1
  have hZ := SerBound.prod (range n) hz (fun _ _ => by positivity) (fun _ _ => by positivity)
  have hP := SerBound.prod ((nodes n).erase k) hp (fun _ _ => by positivity)
    (fun _ _ => by positivity)
  have hall := hZ.mul hP (prod_nonneg fun _ _ => by positivity)
    (prod_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity)
  have hA : (∏ j ∈ range n, |(((Dom.ez n j k : ℚ) / 2 : ℚ) : ℝ)| ^ q) *
      ∏ k' ∈ (nodes n).erase k, (|(((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ q = |((Hk q n k 0 : ℚ) : ℝ)| := by
    rw [Hk_zero_eq, Rat.cast_mul, abs_mul, Rat.cast_prod, Rat.cast_prod, abs_prod, abs_prod]
    congr 1
    · refine prod_congr rfl fun j _ => by rw [Rat.cast_pow, abs_pow]
    · refine prod_congr rfl fun k' _ => by rw [Rat.cast_pow, Rat.cast_inv, abs_pow, abs_inv]
  have hΛ : ∑ _j ∈ range n, (q : ℝ) * 2 + ∑ _k' ∈ (nodes n).erase k, (q : ℝ) * 1 ≤ LamT q n := by
    rw [sum_const, sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul, LamT]
    have : (((nodes n).erase k).card : ℝ) ≤ ((2 * R n + 1 : ℕ) : ℝ) := by
      rw [← card_nodes]; exact_mod_cast card_erase_le
    have hq : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have h := (hall.mono (by positivity) (by positivity) hΛ) b
  rw [hA, ← Dom.Hk_eq_coeff] at h
  exact h

theorem one_le_LamT {q n : ℕ} (hq : 1 ≤ q) : 1 ≤ LamT q n := by
  unfold LamT
  have : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have : (1 : ℝ) ≤ ((2 * R n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem abs_Hk_le_pow {q n : ℕ} (hq : 1 ≤ q) (hn : Even n) (k : ℤ) {b : ℕ} (hb : b ≤ q) :
    |((Hk q n k b : ℚ) : ℝ)| ≤ |((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q :=
  (abs_Hk_le hn k b).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_LamT hq) hb) (abs_nonneg _))

/-! ### Harmonic corrections -/

theorem sum_inv_sq_le (s : Finset ℕ) : ∑ m ∈ s, 1 / (m : ℝ) ^ 2 ≤ 2 := by
  have h := sum_le_hasSum s (fun _ _ => by positivity) hasSum_zeta_two
  have : Real.pi ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  linarith

theorem abs_Tk_le (k : ℤ) (M : ℕ) : |((Tk k M : ℚ) : ℝ)| ≤ 2 * M * 2 ^ (M + 1) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Tk]
  have hpow : ∀ x : ℝ, 1 ≤ x → 1 / x ^ (M + 1) ≤ 1 / x ^ 2 := fun x hx =>
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx (by omega))
  unfold Tk
  split_ifs with hk
  · push_cast
    rw [abs_mul, abs_mul, abs_neg, Nat.abs_cast, abs_pow, abs_two]
    have hs : |∑ j ∈ range k.natAbs, (((2 * j + 1 : ℕ) : ℝ) ^ (M + 1))⁻¹| ≤ 2 := by
      rw [abs_of_nonneg (sum_nonneg fun _ _ => by positivity)]
      calc ∑ j ∈ range k.natAbs, (((2 * j + 1 : ℕ) : ℝ) ^ (M + 1))⁻¹
          ≤ ∑ j ∈ range k.natAbs, 1 / ((j + 1 : ℕ) : ℝ) ^ 2 := by
            refine sum_le_sum fun j _ => ?_
            rw [← one_div]
            refine (hpow _ (by exact_mod_cast (by omega : 1 ≤ 2 * j + 1))).trans ?_
            exact one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ 2 * j + 1)) 2)
        _ ≤ ∑ m ∈ range (k.natAbs + 1), 1 / (m : ℝ) ^ 2 := by
            rw [sum_range_succ']; simp
        _ ≤ 2 := sum_inv_sq_le _
    push_cast at hs
    calc (M : ℝ) * 2 ^ (M + 1) * |∑ j ∈ range k.natAbs, ((2 * (j : ℝ) + 1) ^ (M + 1))⁻¹|
        ≤ M * 2 ^ (M + 1) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * M * 2 ^ (M + 1) := by ring
  · push_cast
    rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
      mul_one, abs_two]
    have hs : |∑ i ∈ Icc 1 k.natAbs, (((2 * i - 1 : ℕ) : ℝ) ^ (M + 1))⁻¹| ≤ 2 := by
      rw [abs_of_nonneg (sum_nonneg fun _ _ => by positivity)]
      calc ∑ i ∈ Icc 1 k.natAbs, (((2 * i - 1 : ℕ) : ℝ) ^ (M + 1))⁻¹
          ≤ ∑ i ∈ Icc 1 k.natAbs, 1 / (i : ℝ) ^ 2 := by
            refine sum_le_sum fun i hi => ?_
            have hi1 := (mem_Icc.1 hi).1
            rw [← one_div]
            refine (hpow _ (by exact_mod_cast (by omega : 1 ≤ 2 * i - 1))).trans ?_
            exact one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : i ≤ 2 * i - 1)) 2)
        _ ≤ 2 := sum_inv_sq_le _
    calc (M : ℝ) * 2 ^ (M + 1) * |∑ i ∈ Icc 1 k.natAbs, (((2 * i - 1 : ℕ) : ℝ) ^ (M + 1))⁻¹|
        ≤ M * 2 ^ (M + 1) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * M * 2 ^ (M + 1) := by ring

/-! ### The local constants -/

theorem rising_le (i d : ℕ) : |((rising i d : ℚ) : ℝ)| ≤ ((i + d : ℕ) : ℝ) ^ d := by
  unfold rising
  push_cast
  rw [abs_prod]
  calc ∏ l ∈ range d, |(i : ℝ) + l| ≤ ∏ _l ∈ range d, ((i : ℝ) + d) := by
        refine prod_le_prod (fun _ _ => abs_nonneg _) fun l hl => ?_
        rw [abs_of_nonneg (by positivity)]
        have : (l : ℝ) ≤ d := by exact_mod_cast (mem_range.1 hl).le
        linarith
    _ = ((i : ℝ) + d) ^ d := by rw [prod_const, card_range]

/-- `C_{q,d} = 2q (q+d)^{d+1} 2^{q+d+1}`. -/
def Cqd (q d : ℕ) : ℕ := 2 * q * (q + d) ^ (d + 1) * 2 ^ (q + d + 1)

theorem abs_alphaC_le {q d n : ℕ} (hq : 1 ≤ q) (hn : Even n) (j : ℕ) (k : ℤ) (a : ℕ) :
    |((alphaC q d n j k a : ℚ) : ℝ)| ≤ Cqd q d * LamT q n ^ q * |((Hk q n k 0 : ℚ) : ℝ)| := by
  have hh : 0 ≤ |((Hk q n k 0 : ℚ) : ℝ)| := abs_nonneg _
  have hL := one_le_LamT (n := n) hq
  unfold alphaC
  split_ifs with hj
  · push_cast
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_two]
    have hr := rising_le (2 * j + 3) d
    have hr' : ((2 * j + 3 + d : ℕ) : ℝ) ^ d ≤ ((q + d : ℕ) : ℝ) ^ d :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega)) d
    have hH := abs_Hk_le_pow (k := k) hq hn (b := q - (2 * j + 3) - a) (by omega)
    have h3 : |((2 * j + 3 + d : ℕ) : ℝ)| ≤ ((q + d : ℕ) : ℝ) := by
      rw [Nat.abs_cast]; exact_mod_cast (by omega)
    have h4 : (2 : ℝ) ^ (2 * j + 3 + d + 1) ≤ 2 ^ (q + d + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    push_cast at hr hr' h3
    have e : (((2 * j + 3 + d : ℕ) : ℚ) : ℝ) = ((2 * j + 3 + d : ℕ) : ℝ) := by push_cast; ring
    unfold Cqd
    push_cast
    calc |((rising (2 * j + 3) d : ℚ) : ℝ)| * |((Hk q n k (q - (2 * j + 3) - a) : ℚ) : ℝ)| *
          (|(2 * (j : ℝ) + 3 + d)| * 2 ^ (2 * j + 3 + d + 1))
        ≤ ((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
          (((q : ℝ) + d) * 2 ^ (q + d + 1)) := by
          gcongr
          · exact hr.trans hr'
      _ ≤ 2 * q * ((q : ℝ) + d) ^ (d + 1) * 2 ^ (q + d + 1) * LamT q n ^ q *
            |((Hk q n k 0 : ℚ) : ℝ)| := by
          have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
          have hX : 0 ≤ ((q : ℝ) + d) ^ (d + 1) * 2 ^ (q + d + 1) * LamT q n ^ q *
            |((Hk q n k 0 : ℚ) : ℝ)| := by positivity
          have e1 : ((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
              (((q : ℝ) + d) * 2 ^ (q + d + 1)) = ((q : ℝ) + d) ^ (d + 1) * 2 ^ (q + d + 1) *
              LamT q n ^ q * |((Hk q n k 0 : ℚ) : ℝ)| := by ring
          rw [e1]
          nlinarith
  · simp only [Rat.cast_zero, abs_zero]; positivity

theorem abs_betaC_le {q d n : ℕ} (hq : 1 ≤ q) (hn : Even n) (k : ℤ) (a : ℕ) :
    |((betaC q d n k a : ℚ) : ℝ)| ≤ Cqd q d * LamT q n ^ q * |((Hk q n k 0 : ℚ) : ℝ)| := by
  have hh : 0 ≤ |((Hk q n k 0 : ℚ) : ℝ)| := abs_nonneg _
  have hL := one_le_LamT (n := n) hq
  unfold betaC
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Icc 1 (q - a), |(-1 : ℝ) ^ d * ((rising i d : ℚ) : ℝ) *
      ((Hk q n k (q - i - a) : ℚ) : ℝ) * ((Tk k (i + d) : ℚ) : ℝ)| ≤
      ((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
        (2 * ((q : ℝ) + d) * 2 ^ (q + d + 1)) := by
    intro i hi
    have hiq := (mem_Icc.1 hi).2
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hr := rising_le i d
    have hr' : ((i + d : ℕ) : ℝ) ^ d ≤ ((q + d : ℕ) : ℝ) ^ d :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega)) d
    have hH := abs_Hk_le_pow (k := k) hq hn (b := q - i - a) (by omega)
    have hT := abs_Tk_le k (i + d)
    have hT' : 2 * ((i + d : ℕ) : ℝ) * 2 ^ (i + d + 1) ≤ 2 * ((q : ℝ) + d) * 2 ^ (q + d + 1) := by
      have h1 : ((i + d : ℕ) : ℝ) ≤ (q : ℝ) + d := by exact_mod_cast (by omega : i + d ≤ q + d)
      have h2 : (2 : ℝ) ^ (i + d + 1) ≤ 2 ^ (q + d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      gcongr
    push_cast at hr' hT'
    gcongr
    · exact hr.trans (by push_cast; exact hr')
    · exact hT.trans (by push_cast; exact hT')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hc : ((q - a + 1 - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega)
  unfold Cqd
  push_cast
  have hX : 0 ≤ ((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
      (2 * ((q : ℝ) + d) * 2 ^ (q + d + 1)) := by positivity
  calc ((q - a + 1 - 1 : ℕ) : ℝ) * (((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
        (2 * ((q : ℝ) + d) * 2 ^ (q + d + 1)))
      ≤ q * (((q : ℝ) + d) ^ d * (|((Hk q n k 0 : ℚ) : ℝ)| * LamT q n ^ q) *
        (2 * ((q : ℝ) + d) * 2 ^ (q + d + 1))) := mul_le_mul_of_nonneg_right hc hX
    _ = 2 * q * ((q : ℝ) + d) ^ (d + 1) * 2 ^ (q + d + 1) * LamT q n ^ q *
          |((Hk q n k 0 : ℚ) : ℝ)| := by ring

/-- `Q = q C_{q,d} Λ^q`. -/
noncomputable def Qc (q d n : ℕ) : ℝ := q * Cqd q d * LamT q n ^ q

theorem Qc_pos {q d n : ℕ} (hq : 1 ≤ q) : 0 < Qc q d n := by
  have := one_le_LamT (n := n) hq
  have : 0 < Cqd q d := by unfold Cqd; positivity
  unfold Qc; positivity

/-- **`‖c_{k,m}‖₁ ≤ Q |h_k|`**. -/
theorem l1_cMv_le {q d n : ℕ} (hq : 2 ≤ q) (hn : Even n) (k : ℤ) (m : ℕ) :
    l1Mv (cMv q d n k m) ≤ Qc q d n * |((Hk q n k 0 : ℚ) : ℝ)| := by
  have hq1 : 1 ≤ q := by omega
  set B := (Cqd q d : ℝ) * LamT q n ^ q * |((Hk q n k 0 : ℚ) : ℝ)| with hB
  have hB0 : 0 ≤ B := by have := one_le_LamT (n := n) hq1; positivity
  unfold cMv
  split_ifs with hm
  · refine (l1Mv_add_le _ _).trans ?_
    rw [l1Mv_C]
    have hsum : l1Mv (∑ j : Fin (rr q), MvPolynomial.C (alphaC q d n j k m) * MvPolynomial.X j) ≤
        ∑ _j : Fin (rr q), B := by
      refine (l1Mv_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      refine (l1Mv_mul_le _ _).trans ?_
      rw [l1Mv_C, l1Mv_X, mul_one]
      exact abs_alphaC_le hq1 hn j k m
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hb := abs_betaC_le (d := d) hq1 hn k m
    have hr : ((rr q : ℕ) : ℝ) + 1 ≤ q := by
      unfold rr; exact_mod_cast (by omega : q / 2 - 1 + 1 ≤ q)
    calc |((betaC q d n k m : ℚ) : ℝ)| + l1Mv (∑ j : Fin (rr q),
          MvPolynomial.C (alphaC q d n j k m) * MvPolynomial.X j)
        ≤ B + (rr q : ℝ) * B := add_le_add hb hsum
      _ = ((rr q : ℝ) + 1) * B := by ring
      _ ≤ q * B := mul_le_mul_of_nonneg_right hr hB0
      _ = Qc q d n * |((Hk q n k 0 : ℚ) : ℝ)| := by rw [hB, Qc]; ring
  · rw [l1Mv_zero]; have := Qc_pos (d := d) (n := n) hq1; positivity

end TwoAdicWin.Arch
