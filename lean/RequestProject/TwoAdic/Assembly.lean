import RequestProject.TwoAdic.InputDefs
import RequestProject.Zeta35.Main

/-!
# Auxiliary facts for the logical assembly of Paper II, §7

* `totalDegree_hankelPoly_le`: `Δ_K` has total degree `≤ K`;
* `eval_ne_zero_of_dominant`: strict dominance of the constant coefficient at a prime `ℓ`
  (II, Theorem 6.4) forces `Δ(x) ≠ 0` at every rational point with `ℓ`-integral coordinates;
* `v2fact_ge`, `decayExp_ge`: the decay exponent of II, Theorem 3.1 at `K = qn` is
  `≥ 5q²n² − C n (1 + log₂ n)`;
* `log_three_gt`, `Fdag_le`: `F/ln 2 ≤ 0.59788 q²`;
* `budget_margin`: `5 − 0.59788 − 4.3892 ≥ 0.0129`.
-/

open Finset

namespace TwoAdicWin

open Hankel2

/-! ### The total degree of `Δ_K` -/

theorem totalDegree_LX_le (q d n : ℕ) (P : Polynomial ℚ) : (LX q d n P).totalDegree ≤ 1 := by
  unfold LX
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; exact zero_le_one
  · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- `Δ_K` has total degree at most `K`. -/
theorem totalDegree_hankelPoly_le (q d n K : ℕ) : (hankelPoly q d n K).totalDegree ≤ K := by
  unfold hankelPoly
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i : Fin K, ((Matrix.of fun i j : Fin K => LX q d n (Polynomial.X ^ ((i : ℕ) + j)))
          (σ i) i).totalDegree ≤ ∑ _i : Fin K, 1 :=
        Finset.sum_le_sum fun i _ => totalDegree_LX_le _ _ _ _
    _ = K := by simp

/-! ### Strict dominance implies non-vanishing -/

theorem norm_ratCast_le_one_of_not_dvd {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {y : ℚ} (hy : ¬ ℓ ∣ y.den) :
    ‖((y : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
  have hy' : (y : ℚ_[ℓ]) = ((y.num : ℤ) : ℚ_[ℓ]) / ((y.den : ℕ) : ℚ_[ℓ]) := by
    rw [← Rat.num_div_den y]; push_cast; rw [Rat.num_div_den y]
  have hd : ‖((y.den : ℕ) : ℚ_[ℓ])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hℓ.out).2 hy)
  rw [hy', norm_div, hd, div_one]
  exact Padic.norm_int_le_one _

theorem norm_ratCast_eq_zpow {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {c : ℚ} (hc : c ≠ 0) :
    ‖((c : ℚ) : ℚ_[ℓ])‖ = (ℓ : ℝ) ^ (-padicValRat ℓ c) := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hc]
  push_cast; rfl

/-- **Strict dominance forces non-vanishing** (the last step of II, Theorem 6.4): if the constant
coefficient of `Δ` is nonzero and has strictly smaller `ℓ`-adic valuation than every other nonzero
coefficient, then `Δ(x) ≠ 0` whenever no denominator of `x` is divisible by `ℓ`. -/
theorem eval_ne_zero_of_dominant {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {r : ℕ}
    (Δ : MvPolynomial (Fin r) ℚ) (h0 : Δ.coeff 0 ≠ 0)
    (hdom : ∀ m, m ≠ 0 → Δ.coeff m ≠ 0 → padicValRat ℓ (Δ.coeff 0) < padicValRat ℓ (Δ.coeff m))
    (x : Fin r → ℚ) (hx : ∀ j, ¬ ℓ ∣ (x j).den) : MvPolynomial.eval x Δ ≠ 0 := by
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  set c0 : ℚ_[ℓ] := ((Δ.coeff 0 : ℚ) : ℚ_[ℓ])
  have hc0 : ‖c0‖ = (ℓ : ℝ) ^ (-padicValRat ℓ (Δ.coeff 0)) := norm_ratCast_eq_zpow h0
  have hc0pos : 0 < ‖c0‖ := by rw [hc0]; positivity
  -- every other term is strictly smaller
  have hterm : ∀ m ∈ Δ.support.erase 0,
      ‖(((Δ.coeff m * ∏ i, x i ^ m i : ℚ)) : ℚ_[ℓ])‖ < ‖c0‖ := by
    intro m hm
    have hm0 : m ≠ 0 := Finset.ne_of_mem_erase hm
    have hcm : Δ.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hm)
    push_cast
    rw [norm_mul, norm_prod]
    have hprod : ∏ i, ‖((x i : ℚ) : ℚ_[ℓ]) ^ m i‖ ≤ 1 := by
      refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_ratCast_le_one_of_not_dvd (hx i))
    have hlt : ‖((Δ.coeff m : ℚ) : ℚ_[ℓ])‖ < ‖c0‖ := by
      rw [norm_ratCast_eq_zpow hcm, hc0]
      exact zpow_lt_zpow_right₀ hℓ1 (neg_lt_neg (hdom m hm0 hcm))
    calc ‖((Δ.coeff m : ℚ) : ℚ_[ℓ])‖ * ∏ i, ‖((x i : ℚ) : ℚ_[ℓ]) ^ m i‖
        ≤ ‖((Δ.coeff m : ℚ) : ℚ_[ℓ])‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ < ‖c0‖ := by rw [mul_one]; exact hlt
  have hrest : ‖∑ m ∈ Δ.support.erase 0, (((Δ.coeff m * ∏ i, x i ^ m i : ℚ)) : ℚ_[ℓ])‖ < ‖c0‖ := by
    rcases (Δ.support.erase 0).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact hc0pos
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hne
        (fun m => (((Δ.coeff m * ∏ i, x i ^ m i : ℚ)) : ℚ_[ℓ]))
      exact hle.trans_lt (hterm i hi)
  intro hev
  have hsum : MvPolynomial.eval x Δ = ∑ m ∈ Δ.support, Δ.coeff m * ∏ i, x i ^ m i := by
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact PadicWin.prod_pow_eq_eval_monomial x m
  have h0mem : (0 : Fin r →₀ ℕ) ∈ Δ.support := MvPolynomial.mem_support_iff.mpr h0
  rw [hsum, ← Finset.add_sum_erase _ _ h0mem] at hev
  have hev' : c0 + ∑ m ∈ Δ.support.erase 0, (((Δ.coeff m * ∏ i, x i ^ m i : ℚ)) : ℚ_[ℓ]) = 0 := by
    have := congrArg (fun y : ℚ => (y : ℚ_[ℓ])) hev
    simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_zero] at this
    simpa [c0] using this
  have : ∑ m ∈ Δ.support.erase 0, (((Δ.coeff m * ∏ i, x i ^ m i : ℚ)) : ℚ_[ℓ]) = -c0 := by
    linear_combination hev'
  rw [this, norm_neg] at hrest
  exact lt_irrefl _ hrest

/-! ### The decay exponent -/

/-- `v₂(i!) ≥ i − 1 − log₂ i` (Legendre). -/
theorem v2fact_ge (i : ℕ) : (i : ℝ) - 1 - Real.logb 2 i ≤ (v2fact i : ℝ) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [v2fact]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) i
  simp only [show 2 - 1 = 1 from rfl, one_mul] at h
  have hdig : (Nat.digits 2 i).sum ≤ Nat.log 2 i + 1 := by
    have h1 := List.sum_le_card_nsmul (Nat.digits 2 i) 1 fun x hx => by
      have := Nat.digits_lt_base (by norm_num : 1 < 2) hx; omega
    rw [Nat.digits_len 2 i (by norm_num) hi.ne', smul_eq_mul, mul_one] at h1
    exact h1
  have hle : (Nat.digits 2 i).sum ≤ i := Nat.digit_sum_le 2 i
  have hv : v2fact i + (Nat.digits 2 i).sum = i := by unfold v2fact; omega
  have hlog := Real.natLog_le_logb i 2
  push_cast at hlog
  have hv' : (v2fact i : ℝ) + ((Nat.digits 2 i).sum : ℝ) = i := by exact_mod_cast hv
  have hdig' : ((Nat.digits 2 i).sum : ℝ) ≤ (Nat.log 2 i : ℝ) + 1 := by exact_mod_cast hdig
  linarith

theorem logb_two_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.logb 2 x ≤ Real.logb 2 y :=
  Real.logb_le_logb_of_le (by norm_num) hx hxy

/-- **The decay exponent at `K = qn`**: `decayExp ≥ 5 q² n² − C n (1 + log₂ n)` for `n ≥ 1`, with
`C = q (q + d + 6 + 2 log₂ q + (d+1) log₂ (3q))`. -/
theorem decayExp_ge (q d n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    5 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2 -
        (q : ℝ) * (q + d + 6 + 2 * Real.logb 2 q + (d + 1) * Real.logb 2 (3 * q)) *
          ((n : ℝ) * (1 + Real.logb 2 n)) ≤ decayExp q d n (q * n) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set K : ℕ := q * n with hK
  have hKR : (K : ℝ) = q * n := by rw [hK]; push_cast; ring
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the factorial sum
  have hlogq : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hqR
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hnR
  have hlogK : Real.logb 2 K = Real.logb 2 q + Real.logb 2 n := by
    rw [hKR, Real.logb_mul (by positivity) (by positivity)]
  have hsum : (K : ℝ) ^ 2 - 3 * K - 2 * K * Real.logb 2 K ≤ 2 * ∑ i ∈ range K, (v2fact i : ℝ) := by
    have h1 : ∑ i ∈ range K, ((i : ℝ) - 1 - Real.logb 2 K) ≤ ∑ i ∈ range K, (v2fact i : ℝ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i < K := Finset.mem_range.mp hi
      refine le_trans ?_ (v2fact_ge i)
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [Nat.cast_zero, Real.logb_zero, sub_zero]
        have : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) (by exact_mod_cast hK1)
        linarith
      · have : Real.logb 2 i ≤ Real.logb 2 K :=
          logb_two_mono (by exact_mod_cast hi0) (by exact_mod_cast hi'.le)
        linarith
    have h2 : ∑ i ∈ range K, ((i : ℝ) - 1 - Real.logb 2 K) =
        (K : ℝ) * (K - 1) / 2 - K - K * Real.logb 2 K := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
        Finset.card_range]
      have := Finset.sum_range_id_mul_two K
      have h3 : ∑ i ∈ range K, (i : ℝ) = (K : ℝ) * (K - 1) / 2 := by
        have h4 : ((∑ i ∈ range K, i : ℕ) : ℝ) * 2 = (K : ℝ) * (K - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, this, Nat.cast_mul, Nat.cast_sub hK1]; simp
        push_cast at h4; linarith
      rw [h3]; simp
    linarith
  -- `v₂(n!)`
  have hvn := v2fact_ge n
  -- the logarithms of `D`
  set D : ℕ := decayD q n K with hD
  have hDR : (D : ℝ) + 1 ≤ 3 * q * n := by
    have : D + 1 ≤ 3 * (q * n) := by
      simp only [hD, decayD, hK]
      have : 1 ≤ q * n := hK1
      omega
    have h' : ((D + 1 : ℕ) : ℝ) ≤ ((3 * (q * n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hD1 : (1 : ℝ) ≤ D := by
    have : 1 ≤ D := by
      simp only [hD, decayD, hK]
      have : 1 ≤ q * n := hK1
      omega
    exact_mod_cast this
  have hlogD1 : Real.logb 2 ((D : ℝ) + 1) ≤ Real.logb 2 (3 * q) + Real.logb 2 n := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact logb_two_mono (by positivity) (by linarith)
  have hlogD : Real.logb 2 (D : ℝ) ≤ Real.logb 2 ((D : ℝ) + 1) :=
    logb_two_mono (by linarith) (by linarith)
  have hlogD0 : 0 ≤ Real.logb 2 (D : ℝ) := Real.logb_nonneg (by norm_num) hD1
  have hlog3q : 0 ≤ Real.logb 2 (3 * q) := Real.logb_nonneg (by norm_num) (by linarith)
  -- assemble
  unfold decayExp
  rw [← hD]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdlog : (d : ℝ) * Real.logb 2 D ≤ d * (Real.logb 2 (3 * q) + Real.logb 2 n) :=
    mul_le_mul_of_nonneg_left (hlogD.trans hlogD1) hd0
  have hinner : (q : ℝ) * (3 * n + 1) + q * (v2fact n : ℝ) - d * Real.logb 2 D
      - Real.logb 2 ((D : ℝ) + 1) ≥
      4 * q * n - q * Real.logb 2 n - (d + 1) * (Real.logb 2 (3 * q) + Real.logb 2 n) := by
    have : (q : ℝ) * (v2fact n : ℝ) ≥ q * (n - 1 - Real.logb 2 n) :=
      mul_le_mul_of_nonneg_left hvn (by positivity)
    nlinarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h5 := mul_le_mul_of_nonneg_left hinner.le hK0
  rw [hKR] at h5 hsum
  rw [hKR, hlogK] at *
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n)) hlogn,
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n)) hlogq,
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n))
      hlogn) (by positivity : (0:ℝ) ≤ q),
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n))
      hlogn) hd0,
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n))
      hlog3q) hd0,
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ q) (by positivity : (0:ℝ) ≤ n)) hlog3q]

/-! ### The archimedean constant and the budget -/

/-- `ln 3 > ln 2 + ∑_{i<20} 3^{-(i+1)}/(i+1) − 10^{-9}`, hence `ln 3 > 1.0986122`. -/
theorem log_three_gt : (1.0986122 : ℝ) < Real.log 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num [abs_of_pos]) 20
  have h23 : Real.log (1 - 1 / 3) = Real.log 2 - Real.log 3 := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h23] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  have l2 := Real.log_two_gt_d9
  rw [abs_le] at h
  linarith [h.1, h.2]

/-- **`F† = F/(n² ln 2) ≤ 0.59788 q²`** (the exact value is `0.5978769… q²`). -/
theorem Fdag_le (q : ℕ) : Fconst q / Real.log 2 ≤ 0.59788 * (q : ℝ) ^ 2 := by
  have l2a := Real.log_two_gt_d9
  have l3 := log_three_gt
  have hl2 : 0 < Real.log 2 := by linarith
  rw [div_le_iff₀ hl2, Fconst]
  have hq : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
  have hkey : 6 + 8 * Real.log 2 - 9 * Real.log 3 ≤ 4 * 0.59788 * Real.log 2 := by
    -- `ln 3` is controlled through `ln 3 − ln 2 = ∑ 3^{-k}/k`
    have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num [abs_of_pos]) 20
    have h23 : Real.log (1 - 1 / 3) = Real.log 2 - Real.log 3 := by
      rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    rw [h23] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [abs_of_pos] at h
    rw [abs_le] at h
    linarith [h.1, h.2]
  nlinarith [mul_le_mul_of_nonneg_left hkey hq]

/-- **The budget (II, Prop. 7.1)**: `5 − 0.59788 − 4.3892 ≥ 0.0129`. -/
theorem budget_margin : (0.0129 : ℝ) ≤ 5 - 0.59788 - 4.3892 := by norm_num

/-! ### Small facts for the ledger -/

/-- From `−g ≤ T_ℓ` to `max(−g, 0) ≤ max(T_ℓ, 0)`. -/
theorem max_neg_le_unbotD {g : ℤ} {T : WithBot ℤ} (h : negTop (g : WithTop ℤ) ≤ T) :
    max (-g) 0 ≤ WithBot.unbotD 0 (max T 0) := by
  have h' : (((-g : ℤ)) : WithBot ℤ) ≤ T := h
  induction T using WithBot.recBotCoe with
  | bot => exact absurd h' (by simp)
  | coe t =>
      have ht : -g ≤ t := by exact_mod_cast h'
      rw [show max ((t : WithBot ℤ)) 0 = ((max t 0 : ℤ) : WithBot ℤ) by
        rw [← WithBot.coe_zero, ← WithBot.coe_max]]
      simp only [WithBot.unbotD_coe]
      exact max_le_max ht le_rfl

/-- A nonzero polynomial has a finite Gauss valuation. -/
theorem gaussValMv_eq_coe {r : ℕ} {F : MvPolynomial (Fin r) ℚ} (hF : F ≠ 0) (ℓ : ℕ) :
    ∃ g : ℤ, PadicWin.gaussValMv ℓ F = g := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hF
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf F.support hne
    (fun m => ((padicValRat ℓ (F.coeff m) : ℤ) : WithTop ℤ))
  exact ⟨_, hi⟩

/-- `‖F‖₁ > 0` for `F ≠ 0`. -/
theorem l1Mv_pos {r : ℕ} {F : MvPolynomial (Fin r) ℚ} (hF : F ≠ 0) : 0 < PadicWin.l1Mv F := by
  unfold PadicWin.l1Mv
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hF
  obtain ⟨m, hm⟩ := hne
  refine Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨m, hm, ?_⟩
  have := MvPolynomial.mem_support_iff.mp hm
  simpa [abs_pos] using this

end TwoAdicWin
