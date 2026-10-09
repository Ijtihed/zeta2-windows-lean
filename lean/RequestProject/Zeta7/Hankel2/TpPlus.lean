import RequestProject.Zeta7.Hankel2.SingleLevel

/-!
# Single-level primes: the class knapsack `T_p^+` (paper §8.3)

Assume `p² > 6n`.  For a node `k` put (paper §8.3)

* `o_k = N_c − 1` (other nodes in the class of `k` mod `p`, `oK`), `z_k = z_c` (`zK`),
* `g_k = 1[p ∣ n − 2k]` (`gK`), `hs_k = 1[p ≤ 2|k| − 1]` (`hsK`),
* `μ_k = 1[o_k + z_k + g_k > 0]` (`muI`),

and the lower bounds (`vbar`)

  `v̄_a = min( min_{1≤i≤4−a} [−D_k − (4−i−a) μ_k − (i+4) hs_k],  −D_k − (1−a) μ_k [a ≤ 1] )`.

`f⁺(k, s)` (`fPlus`) is the maximum over row sets `R` (`|R| = s`) and admissible permutations
`π` (`R_t + π_t ≤ 3`) of `∑_t −v̄_{R_t+π_t} + ℓ(R) 1[o_k > 0]`, clipped at `0`.

* `nv_cPoly_le_vbar`: `v_p(c_{k,a}) ≥ v̄_a` (from Lemma 7.2);
* `fP_le_fPlus`: `f_p(k, s) ≤ f⁺(k, s)` (the unclipped `e_p` and the ultrametric inequality).
-/

open Finset Polynomial

namespace Hankel2.Fam3

section Defs

variable (p n : ℕ)

/-- `o_k`: the number of other nodes in the class of `k` mod `p`. -/
def oK (k : ℤ) : ℕ := cntL n p k

/-- `z_k = #{j < n : p ∣ 2k − 2j − 1}`. -/
def zK (k : ℤ) : ℕ := zL n p k

/-- `g_k = 1[p ∣ n − 2k]`. -/
def gK (k : ℤ) : ℕ := if (p : ℤ) ∣ (n : ℤ) - 2 * k then 1 else 0

/-- `hs_k = 1[p ≤ 2|k| − 1]`. -/
def hsK (k : ℤ) : ℕ := if (p : ℤ) ≤ 2 * |k| - 1 then 1 else 0

/-- `μ_k = 1[o_k + z_k + g_k > 0]`. -/
def muI (k : ℤ) : ℕ := if 0 < oK p n k + zK p n k + gK p n k then 1 else 0

/-- `1[o_k > 0]`. -/
def oI (k : ℤ) : ℕ := if 0 < oK p n k then 1 else 0

/-- The `β`-part of `v̄_a`: `min_{1≤i≤4−a} [−D_k − (4−i−a) μ_k − (i+4) hs_k]` (`a ≤ 3`). -/
noncomputable def vbarBeta (k : ℤ) (a : ℕ) : ℤ :=
  if h : a ≤ 3 then (Icc 1 (4 - a)).inf' (nonempty_Icc.2 (by omega)) fun i =>
    -Dk p n k - ((4 - i - a : ℕ) : ℤ) * muI p n k - ((i + 4 : ℕ) : ℤ) * hsK p k
  else 0

/-- `v̄_a`, including the `α`-part `−D_k − (1−a) μ_k` for `a ≤ 1`. -/
noncomputable def vbar (k : ℤ) (a : ℕ) : ℤ :=
  if a ≤ 1 then min (vbarBeta p n k a) (-Dk p n k - ((1 - a : ℕ) : ℤ) * muI p n k)
  else vbarBeta p n k a

/-- The admissible permutations of a row set `R`: `R_{σ(i)} + i ≤ 3` for all `i`. -/
def admPerms (R : Finset (Fin 4)) : Finset (Equiv.Perm (Fin R.card)) :=
  univ.filter fun σ => ∀ i, ((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + (i : ℕ) ≤ 3

/-- The unclipped `f⁺`: `max_{R, π} ∑_t −v̄_{R_t+π_t} + ℓ(R) 1[o_k > 0]` (`⊥` if empty). -/
noncomputable def fPlusRaw (k : ℤ) (s : ℕ) : WithBot ℤ :=
  (univ.filter fun R : Finset (Fin 4) => R.card = s).sup fun R =>
    (admPerms R).sup fun σ =>
      (((∑ i, -vbar p n k (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i)) +
        (ellR R : ℤ) * oI p n k : ℤ) : WithBot ℤ)

/-- `f⁺(k, s)`, clipped at `0`. -/
noncomputable def fPlus (k : ℤ) (s : ℕ) : ℤ := WithBot.unbotD 0 (max (fPlusRaw p n k s) 0)

end Defs

theorem coe_fPlus (p n : ℕ) (k : ℤ) (s : ℕ) :
    ((fPlus p n k s : ℤ) : WithBot ℤ) = max (fPlusRaw p n k s) 0 := by
  unfold fPlus
  induction fPlusRaw p n k s with
  | bot => simp
  | coe a =>
    rcases le_total a 0 with h | h
    · rw [max_eq_right (by exact_mod_cast h : (a : WithBot ℤ) ≤ 0)]; rfl
    · rw [max_eq_left (by exact_mod_cast h : (0 : WithBot ℤ) ≤ a)]; rfl

theorem fPlus_nonneg (p n : ℕ) (k : ℤ) (s : ℕ) : 0 ≤ fPlus p n k s := by
  have h := coe_fPlus p n k s
  have : (0 : WithBot ℤ) ≤ (fPlus p n k s : WithBot ℤ) := by rw [h]; exact le_max_right _ _
  exact_mod_cast this

theorem sup_add_le {ι : Type*} (s : Finset ι) (g : ι → WithBot ℤ) (c B : WithBot ℤ)
    (h : ∀ i ∈ s, g i + c ≤ B) : s.sup g + c ≤ B := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup s hne g
    rw [heq]; exact h i hi

/-- `−v_p(det M) ≤ max_σ ∑_i −v_p(M_{σ(i), i})`. -/
theorem nv_det_le_sup {p : ℕ} [Fact p.Prime] {s : ℕ} (M : Matrix (Fin s) (Fin s) ℚ[X]) :
    nv p M.det ≤ univ.sup fun σ : Equiv.Perm (Fin s) => ∑ i, nv p (M (σ i) i) := by
  rw [Matrix.det_apply]
  refine (nv_sum_le _ _).trans (Finset.sup_mono_fun fun σ _ => ?_)
  have hsign : nv p (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = nv p (∏ i, M (σ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1, nv_neg]
  rw [hsign]
  exact nv_prod_le _ _

section Bounds

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {k : ℤ}

theorem one_le_padicValInt_dvd {x : ℤ} (h : 1 ≤ padicValInt p x) : (p : ℤ) ∣ x := by
  have := (padicValInt_dvd_iff (p := p) 1 x).2 (Or.inr h)
  simpa using this

theorem oK_pos_of {m : ℤ} (hm : m ∈ (Fam3PF.nodes n).erase k) (h : 1 ≤ padicValInt p (k - m)) :
    0 < oK p n k := by
  unfold oK cntL
  exact card_pos.2 ⟨m, mem_filter.2 ⟨hm, one_le_padicValInt_dvd h⟩⟩

theorem lambdaP_le_oI (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) :
    lambdaP p n k ≤ oI p n k := by
  have h1 := lambdaP_le_one h6 hk
  rcases Nat.eq_zero_or_pos (lambdaP p n k) with h0 | h0
  · omega
  · obtain ⟨m, hm, hmax⟩ := exists_mem_eq_sup ((Fam3PF.nodes n).erase k)
      (by by_contra hne; rw [not_nonempty_iff_eq_empty] at hne; simp [lambdaP, hne] at h0)
      (fun m => padicValInt p (k - m))
    have : 1 ≤ padicValInt p (k - m) := by unfold lambdaP at h0; omega
    unfold oI; rw [if_pos (oK_pos_of hm this)]; omega

theorem muK_le_muI (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) : muK p n k ≤ muI p n k := by
  have h1 := muK_le_one h6 hk
  rcases Nat.eq_zero_or_pos (muK p n k) with h0 | h0
  · omega
  unfold muI
  rw [if_pos]
  · omega
  unfold muK at h0
  rcases le_max_iff.1 (show 1 ≤ max (max (lambdaP p n k) ((range n).sup fun j =>
      padicValInt p (2 * k - 2 * j - 1))) (padicValInt p ((n : ℤ) - 2 * k)) from h0) with h | h
  · rcases le_max_iff.1 h with h | h
    · have := lambdaP_le_oI h6 hk
      unfold oI at this; split_ifs at this with ho <;> omega
    · obtain ⟨j, hj, hjv⟩ := exists_mem_eq_sup (range n)
        (by by_contra hne; rw [not_nonempty_iff_eq_empty] at hne; simp [hne] at h)
        (fun j : ℕ => padicValInt p (2 * k - 2 * j - 1))
      rw [hjv] at h
      have hz : 0 < zK p n k := by
        unfold zK zL
        exact card_pos.2 ⟨j, mem_filter.2 ⟨hj, one_le_padicValInt_dvd h⟩⟩
      omega
  · have hg : gK p n k = 1 := by unfold gK; rw [if_pos (one_le_padicValInt_dvd h)]
    omega

theorem hsMax_le_hsK (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) : hsMax p k ≤ hsK p k := by
  have h1 := hsMax_le_one h6 hk
  rcases Nat.eq_zero_or_pos (hsMax p k) with h0 | h0
  · omega
  obtain ⟨l, hl, hlv⟩ := exists_mem_eq_sup (hsRange k)
    (by by_contra hne; rw [not_nonempty_iff_eq_empty] at hne; simp [hsMax, hne] at h0)
    (fun l => padicValInt p (2 * l - 1))
  have hv : 1 ≤ padicValInt p (2 * l - 1) := by unfold hsMax at h0; omega
  have hd := one_le_padicValInt_dvd hv
  have hle : (p : ℤ) ≤ |2 * l - 1| :=
    Int.le_of_dvd (abs_pos.2 (by omega)) ((dvd_abs _ _).2 hd)
  unfold hsK
  rw [if_pos]
  · omega
  unfold hsRange at hl
  split_ifs at hl with hk0
  · have := mem_Icc.1 hl
    rw [abs_of_pos (by omega : (0 : ℤ) < 2 * l - 1)] at hle
    rw [abs_of_pos hk0]; omega
  · have := mem_Icc.1 hl
    rw [abs_of_neg (by omega : 2 * l - 1 < (0 : ℤ))] at hle
    rw [abs_of_nonpos (by omega)]; omega

omit hp in
theorem vbarBeta_le (ha : a ≤ 3) {i : ℕ} (hi : i ∈ Icc 1 (4 - a)) :
    vbarBeta p n k a ≤
      -Dk p n k - ((4 - i - a : ℕ) : ℤ) * muI p n k - ((i + 4 : ℕ) : ℤ) * hsK p k := by
  unfold vbarBeta
  rw [dif_pos ha]
  exact inf'_le _ hi

omit hp in
theorem vbar_le_beta (a : ℕ) : vbar p n k a ≤ vbarBeta p n k a := by
  unfold vbar; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

omit hp in
theorem vbar_le_alpha {a : ℕ} (ha : a ≤ 1) :
    vbar p n k a ≤ -Dk p n k - ((1 - a : ℕ) : ℤ) * muI p n k := by
  unfold vbar; rw [if_pos ha]; exact min_le_right _ _

/-- **`v_p(c_{k,a}) ≥ v̄_a`** for `p² > 6n` (paper §8.3). -/
theorem nv_cPoly_le_vbar (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) {a : ℕ}
    (ha : a ≤ 3) : nv p (cPoly n k a) ≤ ((-vbar p n k a : ℤ) : WithBot ℤ) := by
  have hmu := muK_le_muI (p := p) h6 hk
  have hhs := hsMax_le_hsK (p := p) h6 hk
  have hp0 := p_pos_q (p := p)
  have hbeta : padicNorm p (betaC n k a) ≤ (p : ℚ) ^ (-vbar p n k a) := by
    unfold betaC
    refine padicNorm.sum_le' (fun i hi => ?_) (by positivity)
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    have hc : phi i * ((i : ℚ) + 3) = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
      simp only [phi]; push_cast; ring
    rw [padicNorm.mul, padicNorm.mul, hc]
    have h1 := padicNorm_natCast_le_one (p := p) (i * (i + 1) * (i + 2) * (i + 3))
    have h2 : padicNorm p (HS k (i + 4)) ≤ (p : ℚ) ^ (((i + 4 : ℕ) : ℤ) * hsK p k) :=
      (norm_HS_le hp2 k (i + 4)).trans (zpow_le_zpow_right₀ one_le_p_q
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hhs) (by positivity)))
    have h3 : padicNorm p (Hk n k (4 - i - a)) ≤
        (p : ℚ) ^ (Dk p n k + ((4 - i - a : ℕ) : ℤ) * muI p n k) :=
      (norm_Hk_le hp2 n k _).trans (zpow_le_zpow_right₀ one_le_p_q (by
        have : ((4 - i - a : ℕ) : ℤ) * muK p n k ≤ ((4 - i - a : ℕ) : ℤ) * muI p n k :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hmu) (by positivity)
        linarith))
    have hv := (vbar_le_beta (p := p) (n := n) (k := k) a).trans (vbarBeta_le ha hi)
    calc padicNorm p ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) * padicNorm p (HS k (i + 4)) *
          padicNorm p (Hk n k (4 - i - a))
        ≤ 1 * (p : ℚ) ^ (((i + 4 : ℕ) : ℤ) * hsK p k) *
            (p : ℚ) ^ (Dk p n k + ((4 - i - a : ℕ) : ℤ) * muI p n k) := by
          gcongr
          · exact padicNorm.nonneg _
          · exact padicNorm.nonneg _
      _ = (p : ℚ) ^ (((i + 4 : ℕ) : ℤ) * hsK p k + (Dk p n k + ((4 - i - a : ℕ) : ℤ) * muI p n k)) := by
          rw [one_mul, ← zpow_add₀ hp0.ne']
      _ ≤ (p : ℚ) ^ (-vbar p n k a) := zpow_le_zpow_right₀ one_le_p_q (by linarith)
  have halpha : padicNorm p (alphaC n k a) ≤ (p : ℚ) ^ (-vbar p n k a) := by
    unfold alphaC
    split_ifs with h
    · have hc : -(phi 3) * 6 * 2 ^ 7 = -((46080 : ℕ) : ℚ) := by norm_num [phi]
      rw [hc, padicNorm.mul, padicNorm.neg]
      have h1 := padicNorm_natCast_le_one (p := p) 46080
      have hv := vbar_le_alpha (p := p) (n := n) (k := k) h
      have h3 : padicNorm p (Hk n k (1 - a)) ≤ (p : ℚ) ^ (-vbar p n k a) :=
        (norm_Hk_le hp2 n k _).trans (zpow_le_zpow_right₀ one_le_p_q (by
          have : ((1 - a : ℕ) : ℤ) * muK p n k ≤ ((1 - a : ℕ) : ℤ) * muI p n k :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hmu) (by positivity)
          linarith))
      calc padicNorm p ((46080 : ℕ) : ℚ) * padicNorm p (Hk n k (1 - a))
          ≤ 1 * (p : ℚ) ^ (-vbar p n k a) := mul_le_mul h1 h3 (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    · simp; positivity
  unfold cPoly
  rw [if_pos ha, nv_le_iff]
  intro i
  rw [coeff_add, coeff_C, coeff_C_mul_X]
  rcases i with _ | _ | i
  · simpa using norm_le_of_padicNorm_le hbeta
  · simpa using norm_le_of_padicNorm_le halpha
  · simp; positivity

/-- **`f_p(k, s) ≤ f⁺(k, s)`** for `p² > 6n` (paper §8.3). -/
theorem fP_le_fPlus (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) (s : ℕ) :
    fP p n k s ≤ ((fPlus p n k s : ℤ) : WithBot ℤ) := by
  rw [coe_fPlus]
  unfold fP
  split_ifs with hs0
  · exact le_max_right _ _
  refine le_trans (Finset.sup_le fun ℓ _ => ?_) (le_max_left _ _)
  unfold eP
  refine sup_add_le _ _ _ _ fun R hR => ?_
  simp only [mem_filter, mem_univ, true_and] at hR
  obtain ⟨hRc, hRℓ⟩ := hR
  have hmin := nv_det_le_sup (p := p) (Matrix.of fun i j : Fin R.card =>
    Cmat n k (R.orderEmbOfFin rfl i) (Fin.castLE (by simpa using R.card_le_univ) j))
  refine le_trans (add_le_add_left hmin _) ?_
  refine sup_add_le _ _ _ _ fun σ _ => ?_
  by_cases hadm : σ ∈ admPerms R
  · have hsum : ∑ i, nv p ((Matrix.of fun i j : Fin R.card =>
        Cmat n k (R.orderEmbOfFin rfl i) (Fin.castLE (by simpa using R.card_le_univ) j)) (σ i) i) ≤
        ((∑ i, -vbar p n k (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i) : ℤ) : WithBot ℤ) := by
      rw [WithBot.coe_sum]
      refine sum_le_sum fun i _ => ?_
      simp only [Matrix.of_apply, Cmat, Fin.val_castLE]
      exact nv_cPoly_le_vbar hp2 h6 hk ((mem_filter.1 hadm).2 i)
    have hlam := lambdaP_le_oI (p := p) h6 hk
    have hval : (((∑ i, -vbar p n k (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i) : ℤ) : WithBot ℤ)) +
        (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) ≤
        (((∑ i, -vbar p n k (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i)) +
          (ellR R : ℤ) * oI p n k : ℤ) : WithBot ℤ) := by
      rw [← WithBot.coe_add, WithBot.coe_le_coe, ← hRℓ]
      push_cast
      have : ((ellR R : ℕ) : ℤ) * lambdaP p n k ≤ (ellR R : ℤ) * oI p n k :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (by positivity)
      linarith
    refine le_trans (add_le_add_left hsum _) (hval.trans ?_)
    unfold fPlusRaw
    exact Finset.le_sup_of_le (mem_filter.2 ⟨mem_univ _, hRc⟩) (Finset.le_sup_of_le hadm le_rfl)
  · simp only [admPerms, mem_filter, mem_univ, true_and, not_forall, not_le] at hadm
    obtain ⟨i, hi⟩ := hadm
    have hbot : ∑ i, nv p ((Matrix.of fun i j : Fin R.card =>
        Cmat n k (R.orderEmbOfFin rfl i) (Fin.castLE (by simpa using R.card_le_univ) j)) (σ i) i) = ⊥ := by
      rw [WithBot.sum_eq_bot_iff]
      refine ⟨i, mem_univ _, ?_⟩
      simp only [Matrix.of_apply, Cmat, Fin.val_castLE, cPoly]
      rw [if_neg (by omega), nv_zero]
    rw [hbot, WithBot.bot_add]; exact bot_le

end Bounds

/-! ### The class knapsack `T_p^+` -/

section Knapsack

variable (p n : ℕ)

/-- Profiles `0 ≤ s_k ≤ 4` supported on the class `c` mod `p`, with total `S`. -/
def clsProfiles (c S : ℕ) : Finset (Fin (3 * n + 1) → ℕ) :=
  (Fintype.piFinset fun _ => range 5).filter fun s =>
    (∀ i, nodeOf n i % (p : ℤ) ≠ c → s i = 0) ∧ ∑ i, s i = S

/-- `V_c(S) = max_{∑_{k∈c} s_k = S} [∑_{k∈c} f⁺(k, s_k) − S² + ∑_{k∈c} s_k²]` (`⊥` if
infeasible). -/
noncomputable def Vc (c S : ℕ) : WithBot ℤ :=
  (clsProfiles p n c S).sup fun s =>
    (((∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), fPlus p n (nodeOf n i) (s i))
      - (S : ℤ) ^ 2 + ∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), (s i : ℤ) ^ 2 : ℤ) :
        WithBot ℤ)

/-- `T_p^+ = max_{∑_c S_c = K} ∑_c V_c(S_c)` (the class knapsack, paper §8.3). -/
noncomputable def TPp (K : ℕ) : WithBot ℤ :=
  ((Fintype.piFinset fun _ : Fin p => range (K + 1)).filter fun S => ∑ c, S c = K).sup fun S =>
    ∑ c : Fin p, Vc p n c (S c)

end Knapsack

theorem le_TPp (p n K : ℕ) (S : Fin p → ℕ) (hS : ∀ c, S c ≤ K) (hSK : ∑ c, S c = K) :
    ∑ c : Fin p, Vc p n c (S c) ≤ TPp p n K := by
  unfold TPp
  apply Finset.le_sup (f := fun S : Fin p → ℕ => ∑ c : Fin p, Vc p n c (S c))
  rw [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun c => mem_range.2 (Nat.lt_succ_of_le (hS c)), hSK⟩

theorem sum_by_classes {M : Type*} [AddCommMonoid M] {n q : ℕ} (hq : 0 < q)
    (G : Fin (3 * n + 1) → M) :
    ∑ c ∈ range q, ∑ i ∈ univ.filter (fun i => nodeOf n i % (q : ℤ) = c), G i = ∑ i, G i := by
  rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (q : ℤ)).toNat) (t := range q)
    (fun i _ => toNat_emod_mem_range hq _)]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  exact sum_congr rfl fun c _ =>
    sum_congr (filter_congr fun i _ => (toNat_emod_eq_iff hq' _ _).symm) fun _ _ => rfl

theorem penL_nonneg (n q : ℕ) (s : Fin (3 * n + 1) → ℕ) : 0 ≤ penL n q s := by
  unfold penL
  refine sum_nonneg fun c _ => ?_
  have := sqCls_ge (n := n) (q := q) s c
  have : (sqCls n q s c : ℤ) ≤ (Scls n q s c : ℤ) ^ 2 := by exact_mod_cast this
  linarith

theorem penL_le_penalty (p n : ℕ) (s : Fin (3 * n + 1) → ℕ) : penL n p s ≤ penalty p n s := by
  rw [penalty_eq_sum_penL]
  have := single_le_sum (f := fun j => penL n (p ^ j) s) (fun j _ => penL_nonneg n _ s)
    (mem_Icc.2 ⟨le_rfl, by omega⟩ : 1 ∈ Icc 1 (3 * n + 1))
  simpa using this

/-- If `∑ x_c = t` and each finite `x_c` is `≤ b_c`, then `t ≤ ∑ b_c`. -/
theorem sum_coe_le {ι : Type*} (s : Finset ι) (x : ι → WithBot ℤ) (b : ι → ℝ)
    (h : ∀ c ∈ s, ∀ v : ℤ, x c = v → (v : ℝ) ≤ b c) :
    ∀ t : ℤ, ∑ c ∈ s, x c = t → (t : ℝ) ≤ ∑ c ∈ s, b c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro t ht
    rw [sum_empty, ← WithBot.coe_zero, WithBot.coe_inj] at ht
    subst ht; simp
  | insert a s ha ih =>
    intro t ht
    rw [sum_insert ha] at ht
    obtain ⟨u, w, hu, hw, huw⟩ := WithBot.add_eq_coe.1 ht
    have h1 := h a (mem_insert_self _ _) u hu.symm
    have h2 := ih (fun c hc v hv => h c (mem_insert_of_mem hc) v hv) w hw.symm
    rw [sum_insert ha, ← huw]; push_cast; linarith

section KnapsackThms

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- **`T_p ≤ T_p^+`** for `p² > 6n` (paper §8.3). -/
theorem TP_le_TPp (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (K : ℕ) : TP p n K ≤ TPp p n K := by
  have hp0 : 0 < p := hp.out.pos
  refine Finset.sup_le fun s hs => ?_
  obtain ⟨hs4, hK⟩ := mem_profiles_iff.1 hs
  obtain ⟨S, hSdef⟩ : ∃ S : Fin p → ℕ, ∀ c, S c = Scls n p s c := ⟨_, fun _ => rfl⟩
  have hSK : ∑ c, S c = K := by
    have := sum_by_classes (n := n) hp0 (fun i => s i)
    simp only [hSdef]
    rw [Fin.sum_univ_eq_sum_range (fun c => Scls n p s c) p]; simpa [Scls] using this.trans hK
  have hSle : ∀ c, S c ≤ K := by
    intro c
    have : S c ≤ ∑ c, S c := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
    omega
  -- the restriction of `s` to a class
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ → Fin (3 * n + 1) → ℕ,
      ∀ c i, r c i = if nodeOf n i % (p : ℤ) = c then s i else 0 := ⟨_, fun _ _ => rfl⟩
  have hr : ∀ c : ℕ, r c ∈ clsProfiles p n c (Scls n p s c) := by
    intro c
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => mem_range.2 ?_, fun i hi => ?_, ?_⟩
    · rw [hrdef]; split_ifs
      · have := hs4 i; omega
      · omega
    · rw [hrdef, if_neg hi]
    · simp only [hrdef]; rw [← sum_filter]; rfl
  obtain ⟨w, hwdef⟩ : ∃ w : ℕ → ℤ, ∀ c, w c =
    (∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), fPlus p n (nodeOf n i) (s i))
      - (Scls n p s c : ℤ) ^ 2 + (sqCls n p s c : ℤ) := ⟨_, fun _ => rfl⟩
  have hw : ∀ c : ℕ, (w c : WithBot ℤ) ≤ Vc p n c (Scls n p s c) := by
    intro c
    unfold Vc
    refine Finset.le_sup_of_le (hr c) (le_of_eq ?_)
    rw [WithBot.coe_inj, hwdef]
    have e1 : ∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), fPlus p n (nodeOf n i) (r c i) =
        ∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), fPlus p n (nodeOf n i) (s i) :=
      sum_congr rfl fun i hi => by rw [hrdef, if_pos (mem_filter.1 hi).2]
    have e2 : ∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), ((r c i : ℕ) : ℤ) ^ 2 =
        (sqCls n p s c : ℤ) := by
      rw [sqCls]; push_cast
      exact sum_congr rfl fun i hi => by rw [hrdef, if_pos (mem_filter.1 hi).2]
    rw [e1, e2]
  have hsumw : ∑ c ∈ range p, w c = (∑ i, fPlus p n (nodeOf n i) (s i)) - penL n p s := by
    simp only [hwdef, penL]
    rw [sum_add_distrib, sum_sub_distrib, sum_by_classes hp0, sum_sub_distrib]
    ring
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((fPlus p n (nodeOf n i) (s i) : ℤ) : WithBot ℤ)) + (((-penL n p s : ℤ)) : WithBot ℤ) :=
        add_le_add (sum_le_sum fun i _ => fP_le_fPlus hp2 h6 (nodeOf_mem n i) (s i))
          (WithBot.coe_le_coe.2 (by have := penL_le_penalty p n s; omega))
    _ = ((∑ c ∈ range p, w c : ℤ) : WithBot ℤ) := by
        rw [hsumw, ← WithBot.coe_sum, ← WithBot.coe_add]; congr 1
    _ = ∑ c : Fin p, ((w c : ℤ) : WithBot ℤ) := by
        rw [WithBot.coe_sum, Fin.sum_univ_eq_sum_range (fun c => ((w c : ℤ) : WithBot ℤ)) p]
    _ ≤ ∑ c : Fin p, Vc p n c (S c) := sum_le_sum fun c _ => by rw [hSdef]; exact hw c
    _ ≤ TPp p n K := le_TPp p n K S hSle hSK

omit hp in
/-- **Weak duality for `T_p^+`** (paper eq. (dual)): for every `λ` and every family `ψ_c` with
`V_c(S) − λ S ≤ ψ_c` for all `S` (e.g. `ψ_c = ψ_c(λ) = max_S (V_c(S) − λ S)`),
`T_p^+ ≤ λ K + ∑_c ψ_c`. -/
theorem TPp_le_dual (K : ℕ) (lam : ℝ) (ψ : ℕ → ℝ)
    (hψ : ∀ c < p, ∀ S : ℕ, ∀ v : ℤ, Vc p n c S = v → (v : ℝ) - lam * S ≤ ψ c) :
    ∀ t : ℤ, TPp p n K = t → (t : ℝ) ≤ lam * K + ∑ c ∈ range p, ψ c := by
  intro t ht
  unfold TPp at ht
  set D := (Fintype.piFinset fun _ : Fin p => range (K + 1)).filter fun S => ∑ c, S c = K
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, sup_empty] at ht; exact absurd ht WithBot.bot_ne_coe
  obtain ⟨S, hS, hSeq⟩ := exists_mem_eq_sup D hD (fun S => ∑ c : Fin p, Vc p n c (S c))
  rw [hSeq] at ht
  have hSK : ∑ c, S c = K := (mem_filter.1 hS).2
  have := sum_coe_le univ (fun c : Fin p => Vc p n c (S c)) (fun c => ψ c + lam * S c)
    (fun c _ v hv => by have := hψ c c.isLt (S c) v hv; linarith) t ht
  rw [sum_add_distrib, ← mul_sum, Fin.sum_univ_eq_sum_range (fun c => ψ c) p] at this
  have hSK' : (∑ c, (S c : ℝ)) = K := by exact_mod_cast hSK
  rw [hSK'] at this; linarith

/-- **Weak duality** (paper eq. (dual)): for `p² > 6n`, every `λ` and every family `ψ_c` bounding
`V_c(S) − λ S`, `T_p ≤ T_p^+ ≤ λ K + ∑_c ψ_c`. -/
theorem TP_le_dual (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (K : ℕ) (lam : ℝ) (ψ : ℕ → ℝ)
    (hψ : ∀ c < p, ∀ S : ℕ, ∀ v : ℤ, Vc p n c S = v → (v : ℝ) - lam * S ≤ ψ c) :
    ∀ t : ℤ, TP p n K = t → (t : ℝ) ≤ lam * K + ∑ c ∈ range p, ψ c := by
  intro t ht
  have hle := TP_le_TPp hp2 h6 K
  rw [ht] at hle
  induction h : TPp p n K with
  | bot => rw [h] at hle; exact absurd (le_bot_iff.1 hle) WithBot.coe_ne_bot
  | coe t' =>
    rw [h, WithBot.coe_le_coe] at hle
    have := TPp_le_dual K lam ψ hψ t' h
    have : (t : ℝ) ≤ t' := by exact_mod_cast hle
    linarith

end KnapsackThms

/-! ### Lemma 8.4: the leaf identities -/

section LeafId

variable {p n : ℕ} {k : ℤ}

theorem vbar_eq_of (ho : 1 ≤ oK p n k) {c0 : ℤ}
    (hc0 : (hsK p k = 1 ∧ c0 = 8) ∨ (hsK p k = 0 ∧ c0 = 3)) {a : ℕ} (ha : a ≤ 3) :
    vbar p n k a = -Dk p n k - c0 + a := by
  have hmu : muI p n k = 1 := by unfold muI; rw [if_pos (by omega)]
  have hbeta : vbarBeta p n k a = -Dk p n k - c0 + a := by
    unfold vbarBeta
    rw [dif_pos ha]
    refine le_antisymm ((inf'_le _ (mem_Icc.2 ⟨le_rfl, by omega⟩ : 1 ∈ Icc 1 (4 - a))).trans ?_)
      (le_inf' _ _ fun i hi => ?_)
    · rw [hmu]
      rcases hc0 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rw [h1] <;>
        push_cast [Nat.cast_sub (show a ≤ 4 - 1 by omega), Nat.cast_sub (show 1 ≤ 4 by omega)] <;>
        omega
    · have hi' := mem_Icc.1 hi
      rw [hmu, show (4 - i - a : ℕ) = 4 - (i + a) by omega]
      rcases hc0 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rw [h1] <;>
        push_cast [Nat.cast_sub (show i + a ≤ 4 by omega)] <;> omega
  unfold vbar
  split_ifs with h1
  · rw [hbeta, hmu]
    refine min_eq_left ?_
    rcases hc0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> push_cast [Nat.cast_sub h1] <;> omega
  · exact hbeta

/-- The value of an admissible pair `(R, σ)` in `f⁺` under the hypotheses of Lemma 8.4. -/
theorem fPlus_term_eq (ho : 1 ≤ oK p n k) {c0 : ℤ}
    (hc0 : (hsK p k = 1 ∧ c0 = 8) ∨ (hsK p k = 0 ∧ c0 = 3)) (R : Finset (Fin 4))
    {σ : Equiv.Perm (Fin R.card)} (hσ : σ ∈ admPerms R) :
    (∑ i, -vbar p n k (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i)) + (ellR R : ℤ) * oI p n k =
      R.card * Dk p n k + c0 * R.card - R.card * (R.card - 1) := by
  have hoI : oI p n k = 1 := by unfold oI; rw [if_pos (by omega)]
  have hadm := (mem_filter.1 hσ).2
  rw [sum_congr rfl fun i _ => by rw [vbar_eq_of ho hc0 (hadm i)], hoI]
  have h1 : ∑ i : Fin R.card, (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) : ℤ) = ∑ r ∈ R, (r : ℕ) := by
    rw [Equiv.sum_comp σ (fun i => (((R.orderEmbOfFin rfl i : Fin 4) : ℕ) : ℤ))]
    exact_mod_cast sum_orderEmbOfFin R
  have h2 : ∑ i : Fin R.card, ((i : ℕ) : ℤ) = R.card.choose 2 := by exact_mod_cast sum_fin_val R.card
  have hc := choose_le_sum R
  have hell : ((ellR R : ℕ) : ℤ) = (∑ r ∈ R, (r : ℕ) : ℕ) - R.card.choose 2 := by
    rw [ellR]; push_cast [Nat.cast_sub hc]; ring
  have hch : ((R.card.choose 2 : ℕ) : ℤ) * 2 = R.card * (R.card - 1) := by
    have h2 : R.card.choose 2 * 2 = R.card * (R.card - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd
    rcases Nat.eq_zero_or_pos R.card with h0 | h0
    · rw [h0]; simp
    have h3 : ((R.card.choose 2 * 2 : ℕ) : ℤ) = ((R.card * (R.card - 1) : ℕ) : ℤ) := by rw [h2]
    push_cast [Nat.cast_sub (by omega : 1 ≤ R.card)] at h3
    exact h3
  have e : ∑ i : Fin R.card, -(-Dk p n k - c0 + ((((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i : ℕ) : ℤ)) =
      R.card * (Dk p n k + c0) - (∑ r ∈ R, (r : ℕ) : ℕ) - R.card.choose 2 := by
    have e' : ∀ i : Fin R.card, -(-Dk p n k - c0 +
        ((((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i : ℕ) : ℤ)) =
        (Dk p n k + c0) - (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
      fun i => by push_cast; ring
    rw [sum_congr rfl fun i _ => e' i, sum_sub_distrib, sum_sub_distrib, h1, h2, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e, hell]
  push_cast
  linarith

theorem card_filter_lt (s : ℕ) (hs : s ≤ 4) :
    (univ.filter fun r : Fin 4 => (r : ℕ) < s).card = s := by
  interval_cases s <;> decide

theorem exists_adm (s : ℕ) (hs : s ≤ 4) :
    ∃ R ∈ univ.filter (fun R : Finset (Fin 4) => R.card = s), (admPerms R).Nonempty := by
  set R0 := univ.filter fun r : Fin 4 => (r : ℕ) < s
  have hc : R0.card = s := card_filter_lt s hs
  refine ⟨R0, mem_filter.2 ⟨mem_univ _, hc⟩, Fin.revPerm, mem_filter.2 ⟨mem_univ _, fun i => ?_⟩⟩
  have hemb : ∀ j : Fin R0.card, ((R0.orderEmbOfFin rfl j : Fin 4) : ℕ) = j := by
    intro j
    have := orderEmbOfFin_unique (s := R0) (rfl : R0.card = R0.card)
      (f := fun j : Fin R0.card => (⟨j, by have := j.isLt; omega⟩ : Fin 4))
      (fun x => by simp only [R0, mem_filter, mem_univ, true_and]; have := x.isLt; omega)
      (fun a b hab => by simpa using hab)
    rw [← this]
  rw [hemb, Fin.revPerm_apply, Fin.val_rev]
  have := i.isLt; omega

/-- **Lemma 8.4 (leaf identities).**  If `o_k ≥ 1` and `D_k ≥ 0`, then for `0 ≤ s ≤ 4`
`f⁺(k, s) = s D_k + 8 s − s(s−1)` if `hs_k = 1`, and `f⁺(k, s) = s D_k + 3 s − s(s−1)` if `hs_k = 0`. -/
theorem leaf_identities (ho : 1 ≤ oK p n k) (hD : 0 ≤ Dk p n k) {s : ℕ} (hs : s ≤ 4) :
    fPlus p n k s = if hsK p k = 1 then (s : ℤ) * Dk p n k + 8 * s - s * (s - 1)
      else (s : ℤ) * Dk p n k + 3 * s - s * (s - 1) := by
  obtain ⟨c0, hc0, hval⟩ : ∃ c0 : ℤ, ((hsK p k = 1 ∧ c0 = 8) ∨ (hsK p k = 0 ∧ c0 = 3)) ∧
      (if hsK p k = 1 then (s : ℤ) * Dk p n k + 8 * s - s * (s - 1)
        else (s : ℤ) * Dk p n k + 3 * s - s * (s - 1)) = s * Dk p n k + c0 * s - s * (s - 1) := by
    by_cases h : hsK p k = 1
    · exact ⟨8, Or.inl ⟨h, rfl⟩, by rw [if_pos h]⟩
    · have : hsK p k = 0 := by unfold hsK at h ⊢; split_ifs at h ⊢ <;> simp_all
      exact ⟨3, Or.inr ⟨this, rfl⟩, by rw [if_neg h]⟩
  rw [hval]
  have hc3 : 3 ≤ c0 := by rcases hc0 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  have hraw : fPlusRaw p n k s = (((s : ℤ) * Dk p n k + c0 * s - s * (s - 1) : ℤ) : WithBot ℤ) := by
    refine le_antisymm (Finset.sup_le fun R hR => Finset.sup_le fun σ hσ => ?_) ?_
    · rw [fPlus_term_eq ho hc0 R hσ, (mem_filter.1 hR).2]
    · obtain ⟨R, hR, σ, hσ⟩ := exists_adm s hs
      refine Finset.le_sup_of_le hR (Finset.le_sup_of_le hσ (le_of_eq ?_))
      rw [fPlus_term_eq ho hc0 R hσ, (mem_filter.1 hR).2]
  have hnn : (0 : ℤ) ≤ s * Dk p n k + c0 * s - s * (s - 1) := by
    have : (0 : ℤ) ≤ s * Dk p n k := by positivity
    have : (s : ℤ) * (s - 1) ≤ c0 * s := by
      have hs' : (s : ℤ) ≤ 4 := by exact_mod_cast hs
      nlinarith [(Nat.cast_nonneg s : (0 : ℤ) ≤ s)]
    linarith
  have := coe_fPlus p n k s
  rw [hraw, max_eq_left (by exact_mod_cast hnn)] at this
  exact_mod_cast this

end LeafId

end Hankel2.Fam3
