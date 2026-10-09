import RequestProject.Frame.PSSlope
import RequestProject.Frame.NvMv
import RequestProject.TwoAdic.NVLocal

/-!
# Taylor coefficients and the leaf bound (`A = q`)

For every odd prime `ℓ`, even `n ≥ 2` and node `k`, with
`D_k = q ∑_{m ≠ k} v_ℓ(m − k) − q ∑_j v_ℓ(2(−k − z_j))` (`Dk`) and `L_ℓ = ⌊log_ℓ (4n − 1)⌋` (`Lell`):

* `Hk_VB_general`: `v_ℓ(H_k[b]) ≥ −D_k − b L_ℓ`;
* `Tk_VB_general`: `v_ℓ(T_k(M)) ≥ −(M + 1) L_ℓ`;
* `betaC_VB_general`, `alphaC_VB_general`: `v_ℓ(c_{k,a}) ≥ −D_k − (q + d + 1 − a) L_ℓ`;
* `nvMv_cMv_le`: the Gauss valuation of `c_{k,m} ∈ ℚ[X_1..X_r]` is `≥ −D_k − (q+d+1) L_ℓ`;
* **`leaf_bound`**: `f_ℓ(k, s) ≤ s D_k + (2q + d + 1) s L_ℓ` for `s ≥ 1`.

The integers whose valuations occur are the node differences (`|m − k| ≤ 3n`), the doubled
node–zero differences `2(−k − z_j)` (odd, `|·| ≤ 4n − 1`) and the harmonic denominators
(`≤ 3n − 1`); all are nonzero and at most `4n − 1` in absolute value, so their valuations are
`≤ L_ℓ`.
-/

open Finset Polynomial PadicWin

namespace TwoAdicWin.Leaf

open Dom

/-- `L_ℓ = ⌊log_ℓ (4n − 1)⌋`. -/
def Lell (n ℓ : ℕ) : ℕ := Nat.log ℓ (4 * n - 1)

/-- `D_k = q ∑_{m ≠ k} v_ℓ(m − k) − q ∑_j v_ℓ(2(−k − z_j))` (family (b), `A = q`). -/
noncomputable def Dk (q n ℓ : ℕ) (k : ℤ) : ℤ :=
  q * ∑ m ∈ (nodes n).erase k, (padicValInt ℓ (m - k) : ℤ) -
    q * ∑ j ∈ range n, (padicValInt ℓ (ez n j k) : ℤ)

variable {q d n ℓ : ℕ} [hp : Fact ℓ.Prime]

theorem padicValInt_le_log {z : ℤ} (hz : z ≠ 0) {X : ℕ} (hX : z.natAbs ≤ X) :
    padicValInt ℓ z ≤ Nat.log ℓ X := by
  have h1 : ℓ ^ padicValInt ℓ z ∣ z.natAbs := by
    unfold padicValInt; exact pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  exact Nat.le_log_of_pow_le hp.out.one_lt (h2.trans hX)

theorem VB_int_val (z : ℤ) : VB ℓ (z : ℚ) (padicValInt ℓ z) :=
  VB_of_padicValRat (le_of_eq (padicValRat.of_int).symm)

theorem VB_int_inv_val {z : ℤ} : VB ℓ ((z : ℚ))⁻¹ (-(padicValInt ℓ z : ℤ)) := by
  refine VB_of_padicValRat (le_of_eq ?_)
  rw [padicValRat.inv, padicValRat.of_int]

theorem VB_half {x : ℚ} {e : ℤ} (h2 : ℓ ≠ 2) (h : VB ℓ x e) : VB ℓ (x / 2) e := by
  unfold VB at h ⊢
  rw [padicNorm.div, padicNorm_two_eq_one h2, div_one]
  exact h

theorem nodes_diff_natAbs {m k : ℤ} (hm : m ∈ nodes n) (hk : k ∈ nodes n) (hn : 1 ≤ n) :
    (m - k).natAbs ≤ 4 * n - 1 := by
  rw [mem_nodes_iff] at hm hk
  unfold R at hm hk
  omega

theorem ez_ne_zero (hn : Even n) (j : ℕ) (k : ℤ) : ez n j k ≠ 0 := by
  obtain ⟨c, hc⟩ := hn
  unfold ez; omega

theorem ez_natAbs (hk : k ∈ nodes n) {j : ℕ} (hj : j < n) : (ez n j k).natAbs ≤ 4 * n - 1 := by
  rw [mem_nodes_iff] at hk
  unfold R at hk
  unfold ez
  omega

/-- **Taylor coefficients (`H_k`)**: `v_ℓ(H_k[b]) ≥ −D_k − b L_ℓ`. -/
theorem Hk_VB_general (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ} (hk : k ∈ nodes n) (b : ℕ) :
    VB ℓ (Hk q n k b) (-Dk q n ℓ k - b * (Lell n ℓ : ℤ)) := by
  rw [Hk_eq_coeff]
  set L : ℤ := (Lell n ℓ : ℤ)
  have hA : PSL ℓ (∑ j ∈ range n, (q : ℤ) * padicValInt ℓ (ez n j k)) L
      (∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) := by
    refine PSL.prod _ _ _ fun j hj => PSL_C_add_X_pow (VB_half h2 (VB_int_val _)) ?_ q
    have := padicValInt_le_log (ℓ := ℓ) (ez_ne_zero hn j k) (ez_natAbs hk (mem_range.1 hj))
    simp only [L, Lell]; exact_mod_cast this
  have hB : PSL ℓ (∑ m ∈ (nodes n).erase k, (q : ℤ) * -(padicValInt ℓ (m - k) : ℤ)) L
      (∏ m ∈ (nodes n).erase k, (PowerSeries.C (((m - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q) := by
    refine PSL.prod _ _ _ fun m hm => ?_
    rw [mem_erase] at hm
    have hne : m - k ≠ 0 := sub_ne_zero.2 hm.1
    refine (PSL_inv_C_add_X (by exact_mod_cast hne) VB_int_inv_val ?_).pow q
    have := padicValInt_le_log (ℓ := ℓ) hne (nodes_diff_natAbs hm.2 hk hn1)
    simp only [L, Lell]; exact_mod_cast this
  have := (hA.mul hB) b
  refine this.mono (le_of_eq ?_)
  unfold Dk
  rw [mul_sum, mul_sum]
  simp only [mul_neg, sum_neg_distrib]
  ring

/-- **Harmonic sums (`T_k`)**: `v_ℓ(T_k(M)) ≥ −(M + 1) L_ℓ`. -/
theorem Tk_VB_general (hn1 : 1 ≤ n) {k : ℤ} (hk : k ∈ nodes n) (M : ℕ) :
    VB ℓ (Tk k M) (-((M + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ)) := by
  have hkk : k.natAbs ≤ 3 * n / 2 := by
    rw [mem_nodes_iff] at hk; unfold R at hk; omega
  have hterm : ∀ j ∈ range k.natAbs,
      VB ℓ ((((2 * j + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹) (-((M + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ)) := by
    intro j hj
    rw [mem_range] at hj
    refine VB_of_padicValRat ?_
    rw [padicValRat.inv, padicValRat.pow (by positivity), padicValRat.of_nat]
    have : padicValNat ℓ (2 * j + 1) ≤ Lell n ℓ := by
      have := padicValInt_le_log (ℓ := ℓ) (z := ((2 * j + 1 : ℕ) : ℤ)) (by omega)
        (X := 4 * n - 1) (by simp only [Int.natAbs_natCast]; omega)
      simpa [padicValInt] using this
    have h' : ((padicValNat ℓ (2 * j + 1) : ℕ) : ℤ) ≤ (Lell n ℓ : ℤ) := by exact_mod_cast this
    push_cast
    nlinarith
  have hsum := VB.sum _ _ hterm
  have hM : VB ℓ (M : ℚ) 0 := VB_natCast M
  have h2 : VB ℓ ((2 : ℚ) ^ (M + 1)) 0 := by simpa using (VB_natCast (ℓ := ℓ) 2).pow (M + 1)
  unfold Tk
  split_ifs
  · have := ((hM.neg.mul h2)).mul hsum
    simpa using this
  · rw [sum_Icc_odd_eq_range]
    have hs : VB ℓ ((-1 : ℚ) ^ (M + 1)) 0 := by simpa using ((VB_one (ℓ := ℓ)).neg).pow (M + 1)
    have := ((hM.mul hs).mul h2).mul hsum
    simpa using this

/-- `v_ℓ(β_{k,a}) ≥ −D_k − (q + d + 1 − a) L_ℓ` for `a < q`. -/
theorem betaC_VB_general (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ} (hk : k ∈ nodes n)
    {a : ℕ} (ha : a < q) :
    VB ℓ (betaC q d n k a) (-Dk q n ℓ k - ((q + d + 1 - a : ℕ) : ℤ) * (Lell n ℓ : ℤ)) := by
  refine betaC_VB_gen k a (fun i => -Dk q n ℓ k - ((q - i - a : ℕ) : ℤ) * (Lell n ℓ : ℤ))
    (fun i => -((i + d + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ))
    (fun i _ => Hk_VB_general hn hn1 h2 hk _) (fun i _ => Tk_VB_general hn1 hk _) _ (fun i hi => ?_)
  rw [mem_Icc] at hi
  dsimp only
  have e : ((q + d + 1 - a : ℕ) : ℤ) = ((q - i - a : ℕ) : ℤ) + ((i + d + 1 : ℕ) : ℤ) := by omega
  rw [e]; ring_nf; rfl

/-- `v_ℓ(α^{(j)}_{k,a}) ≥ −D_k − (q + d + 1 − a) L_ℓ`. -/
theorem alphaC_VB_general (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ} (hk : k ∈ nodes n)
    (j : ℕ) {a : ℕ} (ha : a < q) :
    VB ℓ (alphaC q d n j k a) (-Dk q n ℓ k - ((q + d + 1 - a : ℕ) : ℤ) * (Lell n ℓ : ℤ)) := by
  by_cases hq : 2 * j + 3 + a ≤ q
  · refine alphaC_VB_gen k j a _ ((Hk_VB_general hn hn1 h2 hk _).mono ?_)
    have hL : (0 : ℤ) ≤ Lell n ℓ := by positivity
    have : ((q - (2 * j + 3) - a : ℕ) : ℤ) ≤ ((q + d + 1 - a : ℕ) : ℤ) := by omega
    nlinarith
  · unfold alphaC; rw [if_neg hq]; exact VB_zero _

theorem norm_le_of_VB {x : ℚ} {e : ℤ} (h : VB ℓ x e) : ‖(x : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-e) := by
  rw [Padic.eq_padicNorm]
  unfold VB at h
  have := (Rat.cast_le (K := ℝ)).2 h
  push_cast at this
  exact this

theorem nvMv_X_le {σ : Type*} (j : σ) : nvMv ℓ (MvPolynomial.X j : MvPolynomial σ ℚ) ≤ 0 := by
  classical
  have := (nvMv_le_iff (p := ℓ) (MvPolynomial.X j : MvPolynomial σ ℚ) 0).2 (fun m => by
    rw [MvPolynomial.coeff_X']
    split_ifs <;> simp)
  simpa using this

/-- The Gauss valuation of the local constant `c_{k,m}`. -/
theorem nvMv_cMv_le (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ} (hk : k ∈ nodes n) (m : ℕ) :
    nvMv ℓ (cMv q d n k m) ≤ ((Dk q n ℓ k + ((q + d + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ) : ℤ) : WithBot ℤ) := by
  unfold cMv
  split_ifs with hm
  · set B : ℤ := Dk q n ℓ k + ((q + d + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ)
    have hL : (0 : ℤ) ≤ Lell n ℓ := by positivity
    have hcoef : ∀ c : ℚ, VB ℓ c (-Dk q n ℓ k - ((q + d + 1 - m : ℕ) : ℤ) * (Lell n ℓ : ℤ)) →
        nvMv ℓ (MvPolynomial.C c : MvPolynomial (Fin (rr q)) ℚ) ≤ (B : WithBot ℤ) := by
      intro c hc
      refine nvMv_C_le ((norm_le_of_VB hc).trans (zpow_le_zpow_right₀ ?_ ?_))
      · exact_mod_cast hp.out.one_lt.le
      · have : ((q + d + 1 - m : ℕ) : ℤ) ≤ ((q + d + 1 : ℕ) : ℤ) := by omega
        nlinarith
    refine (nvMv_add_le _ _).trans (max_le (hcoef _ (betaC_VB_general hn hn1 h2 hk hm)) ?_)
    refine (nvMv_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (nvMv_mul_le _ _).trans ?_
    have h1 := hcoef _ (alphaC_VB_general (d := d) hn hn1 h2 hk j hm)
    have h3 := nvMv_X_le (ℓ := ℓ) j
    calc nvMv ℓ (MvPolynomial.C (alphaC q d n (↑j) k m)) + nvMv ℓ (MvPolynomial.X j)
        ≤ (B : WithBot ℤ) + 0 := add_le_add h1 h3
      _ = (B : WithBot ℤ) := add_zero _
  · simp

theorem nvMv_zsmul_units {σ : Type*} (u : ℤˣ) (F : MvPolynomial σ ℚ) :
    nvMv ℓ (u • F) = nvMv ℓ F := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, nvMv_neg]

theorem nvMv_det_le {σ ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (B : ℤ) (hM : ∀ i j, nvMv ℓ (M i j) ≤ (B : WithBot ℤ)) :
    nvMv ℓ M.det ≤ ((Fintype.card ι * B : ℤ) : WithBot ℤ) := by
  rw [Matrix.det_apply]
  refine (nvMv_sum_le _ _).trans (Finset.sup_le fun σ' _ => ?_)
  rw [nvMv_zsmul_units]
  refine (nvMv_prod_le _ _).trans ?_
  calc ∑ i, nvMv ℓ (M (σ' i) i) ≤ ∑ _i : ι, (B : WithBot ℤ) := sum_le_sum fun i _ => hM _ _
    _ = ((Fintype.card ι * B : ℤ) : WithBot ℤ) := by
      rw [sum_const, card_univ]
      induction Fintype.card ι with
      | zero => simp
      | succ c ih => rw [succ_nsmul, ih, ← WithBot.coe_add]; congr 1; push_cast; ring

theorem lambdaP_le (hn1 : 1 ≤ n) {k : ℤ} (hk : k ∈ nodes n) : lambdaP n ℓ k ≤ Lell n ℓ := by
  unfold lambdaP
  refine Finset.sup_le fun m hm => ?_
  rw [mem_erase] at hm
  have hne : k - m ≠ 0 := sub_ne_zero.2 (Ne.symm hm.1)
  refine padicValInt_le_log hne ?_
  have := nodes_diff_natAbs hk hm.2 hn1
  exact this

/-- **Leaf bound**: `f_ℓ(k, s) ≤ s D_k + (2q + d + 1) s L_ℓ`. -/
theorem leaf_bound (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ} (hk : k ∈ nodes n) {s : ℕ}
    (hs1 : 1 ≤ s) :
    fP q d n ℓ k s ≤ ((s * Dk q n ℓ k + ((2 * q + d + 1) * s : ℕ) * (Lell n ℓ : ℤ) : ℤ) : WithBot ℤ) := by
  unfold fP
  rw [if_neg (by omega)]
  refine Finset.sup_le fun j hj => ?_
  rw [mem_range] at hj
  set B : ℤ := Dk q n ℓ k + ((q + d + 1 : ℕ) : ℤ) * (Lell n ℓ : ℤ)
  have heP : eP q d n ℓ k s j ≤ ((s * B : ℤ) : WithBot ℤ) := by
    unfold eP
    refine Finset.sup_le fun Rs hRs => ?_
    simp only [mem_filter, mem_univ, true_and] at hRs
    have := nvMv_det_le (ℓ := ℓ) (Matrix.of fun i j : Fin Rs.card =>
      CmatQ q d n k (Rs.orderEmbOfFin rfl i) (Fin.castLE (by simpa using Rs.card_le_univ) j)) B
      (fun i j => nvMv_cMv_le hn hn1 h2 hk _)
    have hc : ((Fintype.card (Fin Rs.card) : ℕ) : ℤ) * B = s * B := by
      rw [Fintype.card_fin, hRs.1]
    rw [hc] at this
    exact this
  have hjl : ((j * lambdaP n ℓ k : ℕ) : ℤ) ≤ ((s * q : ℕ) : ℤ) * (Lell n ℓ : ℤ) := by
    have h1 := lambdaP_le (ℓ := ℓ) hn1 hk
    have h3 : j ≤ s * q := by
      have : s * (q - s) ≤ s * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
    have : j * lambdaP n ℓ k ≤ (s * q) * Lell n ℓ := Nat.mul_le_mul h3 h1
    exact_mod_cast this
  calc eP q d n ℓ k s j + (((j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ)
      ≤ ((s * B : ℤ) : WithBot ℤ) + ((((s * q : ℕ) : ℤ) * (Lell n ℓ : ℤ) : ℤ) : WithBot ℤ) :=
        add_le_add heP (WithBot.coe_le_coe.2 hjl)
    _ = ((s * Dk q n ℓ k + ((2 * q + d + 1) * s : ℕ) * (Lell n ℓ : ℤ) : ℤ) : WithBot ℤ) := by
        rw [← WithBot.coe_add]
        congr 1
        simp only [B]
        push_cast
        ring

end TwoAdicWin.Leaf
