import RequestProject.TwoAdic.Purity
import RequestProject.TwoAdic.Assembly
import RequestProject.TwoAdic.Corollary
import RequestProject.Zeta7.PNT.PsiAsymp

/-!
# Paper II, Theorem 1.1 and Corollary 1.2: the logical assembly (II, §7)

`TwoAdicWin.TwoAdicInputs` collects, as explicit fields, exactly the inputs of Paper II that are not
yet formalised.  Each is stated as in II for **every admissible `(q, d)`** (`4 ≤ q` even, `d` odd,
`q ≤ d + 1`, `7(d+2) ≤ 10q`, see `Admissible`) and `K = qn`, in terms of the true objects of
`Defs.lean`: the functional `L(P) = ∫_{ℤ₂} (PW)^{(d)}(t + 1/2) dt`, its Hankel matrix `hankelL`, and
the Hankel polynomial `Δ_K = hankelPoly q d n K ∈ ℚ[X_1, …, X_r]`.

* (i)    `decay` — II, Theorem 3.1 (2-adic decay), in norm form;
* (ii)   `arch` — the archimedean size, with `Δ_{qn} ≠ 0` assumed;
* (iii)  `tree` — the tree bound for every odd prime;
         `circ`, `assembly` — II, Cor. 5.4 (the prime sum with constant `C̃(δ)`),
         stated for any limit `M₀` of Mertens' sum with `ℓ = 2` removed and assuming the prime
         number theorem `θ(x)/x → 1`;
         `certificate` — II, Prop. 7.1: `C̃(δ) ≤ 4.3892` for `0 ≤ δ ≤ 3/7` (relaxed from
         `4.388838`), with the true Mertens constant `−γ − ln 2`;
* (iv)   `nonvanishing` — II, Theorem 6.4 (strict dominance of the constant coefficient at
         `ℓ = 2n+1`).

`thm_1_1_of_inputs` derives `Thm11` from these fields and the **proved** ingredients: purity
(`aeval_zeta_hankelPoly`, II Lemma 2.2), the multivariable criterion (`PadicWin.mv_criterion`,
II Lemma 2.3), infinitely many primes `ℓ ≡ 1 mod 4` (`Nat.exists_prime_gt_modEq_one`),
Mertens' theorem `PNT.tendsto_mertens_odd` and the prime number theorem `PNT.tendsto_theta_div`,
the decay asymptotics (`decayExp_ge`), the closed bound `F/ln 2 ≤ 0.59788 q²` (`Fdag_le`) and the
budget `5 − 0.59788 − 4.3892 ≥ 0.0129` (II §7).

`cor_1_2_of_thm` derives Corollary 1.2 (both parts) from `Thm11` by arithmetic.
-/

open Polynomial Finset Filter Topology

namespace TwoAdicWin

open Hankel2

/-- **The inputs of Paper II still missing**, each stated as in II for every admissible `(q,d)`
and `K = qn`. -/
structure TwoAdicInputs where
  /-- (i) **II, Theorem 3.1 (2-adic decay)**, `A = q`, `K = qn ≥ 2`:
  `v₂(Δ_K(ζ)) ≥ 2 ∑_{i<K} v₂(i!) + K(q(3n+1) + q v₂(n!) − d log₂ D − log₂(D+1))`, `D = 2K − 2 + qn`,
  in norm form `‖det[L(x^{i+j})]_{i,j<K}‖₂ ≤ 2^{−(…)}` (meaningful also when the value is `0`). -/
  decay : ∀ q d n : ℕ, Admissible q d → Even n → 0 < n →
    ‖(hankelL q d n (q * n)).det‖ ≤ (2 : ℝ) ^ (-decayExp q d n (q * n))
  /-- (ii) **The archimedean size**, family (b), `A = κ = q`:
  for every `ε > 0` and all large even `n` with `Δ_{qn} ≠ 0`,
  `ln ‖Δ_{qn}‖₁ ≤ −q² n² ln n + (F + ε) n²`, `F = (q²/4)(6 + 8 ln 2 − 9 ln 3)`. -/
  arch : ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    hankelPoly q d n (q * n) ≠ 0 →
      Real.log (PadicWin.l1Mv (hankelPoly q d n (q * n))) ≤
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2
  /-- (iii-a) **The tree bound**: `−v_ℓ(Δ_{qn}) ≤ T_ℓ` for every odd prime `ℓ`, where
  `v_ℓ` is the minimum over the coefficients. -/
  tree : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ.Prime → ℓ ≠ 2 →
    negTop (PadicWin.gaussValMv ℓ (hankelPoly q d n (q * n))) ≤ TP q d n ℓ (q * n)
  /-- The circle-model integral `I(δ) = ∫_ε^{7/2} min_{τ ≥ 0}(τ + ∑_t meas_t(u) ψ̃_t(τ)) du` of II,
  Cor. 5.4 (a function of `δ` only, by homogeneity). -/
  circ : ℝ → ℝ
  /-- (iii-b) **II, Cor. 5.4 (assembly)**, `A = κ = q`: if Mertens' sum with `ℓ = 2`
  removed is `ln Y + M₀ + o(1)` and `θ(x) ~ x`, then for every `ε > 0`, all large even `n` and every
  finite set `S` of odd primes,
  `∑_{ℓ ∈ S} max(T_ℓ, 0) log₂ ℓ ≤ q² n² log₂ n + q² C̃(δ) n² + ε n²`, `δ = (d+2)/q − 1`. -/
  assembly : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertensOddSum Y - Real.log Y) atTop (𝓝 M₀) →
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) →
    ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
        ∑ ℓ ∈ S, (TPplus q d n ℓ (q * n) : ℝ) * Real.logb 2 ℓ ≤
          (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n
            + (q : ℝ) ^ 2 * Ctil M₀ circ (deltaOf q d) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2
  /-- (iii-c) **II, Prop. 7.1 (the certificate)**: `C̃(δ) ≤ 4.3892` for `0 ≤ δ ≤ 3/7`, with the
  true Mertens constant `−γ − ln 2` (relaxed from `C̃(3/7) ≤ 4.388838`; monotonicity in `δ`). -/
  certificate : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 3 / 7 → Ctil mertensOddConst circ δ ≤ 4.3892
  /-- (iv) **II, Theorem 6.4 (strict dominance at `ℓ = 2n+1`)**: for `ℓ = 2n + 1` prime,
  `ℓ > q + d + 1`, `n` even, the constant coefficient of `Δ_{qn}` is nonzero with
  `v_ℓ([X⁰]Δ) = −2∑_x ℓ_x = −qn(d+2)`, strictly below `v_ℓ` of every other nonzero coefficient. -/
  nonvanishing : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ = 2 * n + 1 → ℓ.Prime →
    q + d + 1 < ℓ →
      (hankelPoly q d n (q * n)).coeff 0 ≠ 0 ∧
      padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) = -((q * n * (d + 2) : ℕ) : ℤ) ∧
      ∀ m, m ≠ 0 → (hankelPoly q d n (q * n)).coeff m ≠ 0 →
        padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) <
          padicValRat ℓ ((hankelPoly q d n (q * n)).coeff m)

theorem deltaOf_nonneg {q d : ℕ} (h : Admissible q d) : 0 ≤ deltaOf q d := by
  obtain ⟨h4, -, -, hqd, -⟩ := h
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have : (q : ℝ) ≤ d + 2 := by exact_mod_cast (show q ≤ d + 2 by omega)
  unfold deltaOf
  rw [sub_nonneg, le_div_iff₀ hq]; linarith

theorem deltaOf_le {q d : ℕ} (h : Admissible q d) : deltaOf q d ≤ 3 / 7 := by
  obtain ⟨h4, -, -, -, h7⟩ := h
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have : (7 : ℝ) * (d + 2) ≤ 10 * q := by exact_mod_cast h7
  unfold deltaOf
  rw [sub_le_iff_le_add, div_le_iff₀ hq]; linarith

/-- **Paper II, Theorem 1.1, from the inputs** (II, §7). -/
theorem thm_1_1_of_inputs (I : TwoAdicInputs) : Thm11 := by
  intro q d h4 hqe hdo hqd h7
  have hadm : Admissible q d := ⟨h4, hqe, hdo, hqd, h7⟩
  by_contra hcon
  push_neg at hcon
  choose! xr hxr using hcon
  set x : Fin (rr q) → ℚ := fun j => xr ((j : ℕ) + 1) with hx_def
  have hζ : zetaVec q d = fun j => ((x j : ℚ) : ℚ_[2]) := by
    funext j
    simp only [zetaVec, hx_def]
    apply hxr
    have := j.2
    unfold rr at this
    simp only [Finset.mem_Icc]
    omega
  -- constants
  have hq4R : (4 : ℝ) ≤ q := by exact_mod_cast h4
  have hq16 : (16 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  set H : ℕ := PadicWin.heightMv x with hH_def
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast PadicWin.one_le_heightMv x
  have hlogH : 0 ≤ Real.logb 2 H := Real.logb_nonneg (by norm_num) hH1
  set Cd : ℝ := (q : ℝ) * (q + d + 6 + 2 * Real.logb 2 q + (d + 1) * Real.logb 2 (3 * q))
    with hCd_def
  have hCd : 0 ≤ Cd := by
    have h1 : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) (by linarith)
    have h2 : 0 ≤ Real.logb 2 (3 * q) := Real.logb_nonneg (by norm_num) (by linarith)
    positivity
  obtain ⟨NB, hNB⟩ := I.arch q d hadm (1 / 100) (by norm_num)
  obtain ⟨NT, hNT⟩ := I.assembly mertensOddConst PNT.tendsto_mertens_odd PNT.tendsto_theta_div q d
    hadm (1 / 100) (by norm_num)
  obtain ⟨NL, hNL⟩ := Zeta35.eventually_lower_order3 (100 * Cd) (100 * ((q : ℝ) * Real.logb 2 H))
    (by positivity) (by positivity)
  -- the auxiliary prime `ℓ ≡ 1 mod 4`, `n = (ℓ − 1)/2`
  obtain ⟨ℓ, hℓ, hℓbig, hℓmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := 4) (2 * (NB + NT + NL + q + d + PadicWin.commonDen x + 2))
      (by norm_num)
  have hℓ4 : ℓ % 4 = 1 := hℓmod
  set n : ℕ := (ℓ - 1) / 2 with hn_def
  have hn2 : ℓ = 2 * n + 1 := by omega
  have hn : Even n := ⟨(ℓ - 1) / 4, by omega⟩
  have hnB : NB ≤ n := by omega
  have hnT : NT ≤ n := by omega
  have hnL : NL ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hℓqd : q + d + 1 < ℓ := by omega
  have hℓden : PadicWin.commonDen x < ℓ := by omega
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- (iv) non-vanishing at `x`
  obtain ⟨h0, -, hdom⟩ := I.nonvanishing q d n ℓ hadm hn hn2 hℓ hℓqd
  have hxℓ : ∀ j, ¬ ℓ ∣ (x j).den := by
    intro j hdvd
    have h1 : (x j).den ∣ PadicWin.commonDen x :=
      Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ j)
    have h2 := Nat.le_of_dvd (PadicWin.commonDen_pos x) (hdvd.trans h1)
    omega
  have hev := eval_ne_zero_of_dominant _ h0 hdom x hxℓ
  set K : ℕ := q * n with hK_def
  set Δ := hankelPoly q d n K with hΔ_def
  have hΔ0 : Δ ≠ 0 := fun h => hev (by rw [h, map_zero])
  have hne : MvPolynomial.aeval (fun j => ((x j : ℚ) : ℚ_[2])) Δ ≠ 0 := by
    rw [PadicWin.aeval_ratCast_eq]; exact_mod_cast hev
  -- the criterion
  obtain ⟨S, E, hSE, hcrit⟩ := PadicWin.mv_criterion 2 Δ (totalDegree_hankelPoly_le q d n K) x hne
  set Z : ℚ_[2] := MvPolynomial.aeval (fun j => ((x j : ℚ) : ℚ_[2])) Δ with hZ_def
  -- (i) the decay, via purity
  have hdec := I.decay q d n hadm hn (by omega)
  rw [← aeval_zeta_hankelPoly hqe hdo hn (by nlinarith), hζ] at hdec
  change ‖Z‖ ≤ _ at hdec
  have hZpos : 0 < ‖Z‖ := norm_pos_iff.mpr hne
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hnR
  have hKR : (K : ℝ) = q * n := by rw [hK_def]; push_cast; ring
  have hA : Real.logb 2 ‖Z‖ ≤
      -(5 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2) + Cd * ((n : ℝ) * (1 + Real.logb 2 n)) := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hZpos hdec
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    have h2 := decayExp_ge q d n (by omega) hn1
    rw [← hCd_def] at h2
    linarith
  -- (ii) the archimedean size
  have hl1pos : 0 < PadicWin.l1Mv Δ := l1Mv_pos hΔ0
  have hl2a := Real.log_two_gt_d9
  have hl2 : 0 < Real.log 2 := by linarith
  have hB : Real.logb 2 (PadicWin.l1Mv Δ) ≤
      -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n) + 0.59788 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2
        + (n : ℝ) ^ 2 / 69 := by
    have h1 := hNB n hnB hn hΔ0
    have hF := Fdag_le q
    rw [div_le_iff₀ hl2] at hF
    rw [Real.logb, div_le_iff₀ hl2]
    have e : (-((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n) + 0.59788 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2
        + (n : ℝ) ^ 2 / 69) * Real.log 2 =
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + 0.59788 * (q : ℝ) ^ 2 * Real.log 2 * (n : ℝ) ^ 2
          + (n : ℝ) ^ 2 * Real.log 2 / 69 := by
      rw [Real.logb]; field_simp
    rw [e]
    have hN2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have h3 : Fconst q * (n : ℝ) ^ 2 ≤ 0.59788 * (q : ℝ) ^ 2 * Real.log 2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hN2
    have h4 : (1 / 100 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * Real.log 2 / 69 := by
      have := mul_le_mul_of_nonneg_left hl2a.le hN2
      linarith
    linarith
  -- (iii) the denominators
  have hS : ∀ ℓ' ∈ S, ℓ'.Prime ∧ ℓ' ≠ 2 := fun ℓ' h => ⟨(hSE ℓ' h).1, (hSE ℓ' h).2.1⟩
  have hEle : ∀ ℓ' ∈ S, (E ℓ' : ℝ) ≤ TPplus q d n ℓ' K := by
    intro ℓ' hℓ'
    obtain ⟨hp, hp2, hEq⟩ := hSE ℓ' hℓ'
    obtain ⟨g, hg⟩ := gaussValMv_eq_coe hΔ0 ℓ'
    have hT := I.tree q d n ℓ' hadm hn hp hp2
    rw [← hΔ_def, hg] at hT
    have h1 := hEq g hg
    have h2 := max_neg_le_unbotD hT
    exact_mod_cast h1.trans h2
  have hdpos : 0 < ∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ' :=
    Finset.prod_pos fun ℓ' h => pow_pos (by exact_mod_cast (hS ℓ' h).1.pos) _
  have hT : Real.logb 2 (∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') ≤
      (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n + 4.3892 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2
        + 1 / 100 * (n : ℝ) ^ 2 := by
    rw [Real.logb_prod S _ (fun ℓ' h => pow_ne_zero _ (by exact_mod_cast (hS ℓ' h).1.ne_zero))]
    have h1 : ∑ ℓ' ∈ S, Real.logb 2 ((ℓ' : ℝ) ^ E ℓ') ≤
        ∑ ℓ' ∈ S, (TPplus q d n ℓ' K : ℝ) * Real.logb 2 ℓ' := by
      refine Finset.sum_le_sum fun ℓ' h => ?_
      rw [Real.logb_pow]
      have hq1 : (1 : ℝ) ≤ ℓ' := by exact_mod_cast (hS ℓ' h).1.one_lt.le
      exact mul_le_mul_of_nonneg_right (hEle ℓ' h) (Real.logb_nonneg (by norm_num) hq1)
    have h2 := hNT n hnT hn S hS
    have hc := I.certificate (deltaOf q d) (deltaOf_nonneg hadm) (deltaOf_le hadm)
    have h3 : (q : ℝ) ^ 2 * Ctil mertensOddConst I.circ (deltaOf q d) * (n : ℝ) ^ 2 ≤
        4.3892 * (q : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hc h0
      linarith
    linarith
  -- the height of `x`
  have hHK : Real.logb 2 ((H : ℝ) ^ K) = (q : ℝ) * Real.logb 2 H * n := by
    rw [Real.logb_pow, hKR]; ring
  -- lower-order terms
  have hlow := hNL n hnL
  -- assemble
  have hHKpos : 0 < (H : ℝ) ^ K := pow_pos (by linarith) _
  have hYpos : 0 < (∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') * PadicWin.l1Mv Δ * (H : ℝ) ^ K * ‖Z‖ := by
    positivity
  have hlogY : Real.logb 2 ((∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') * PadicWin.l1Mv Δ * (H : ℝ) ^ K * ‖Z‖) =
      Real.logb 2 (∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') + Real.logb 2 (PadicWin.l1Mv Δ) +
        Real.logb 2 ((H : ℝ) ^ K) + Real.logb 2 ‖Z‖ := by
    rw [Real.logb_mul (by positivity) hZpos.ne', Real.logb_mul (by positivity) hHKpos.ne',
      Real.logb_mul hdpos.ne' hl1pos.ne']
  have hsum : Real.logb 2 ((∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') * PadicWin.l1Mv Δ * (H : ℝ) ^ K * ‖Z‖)
      < 0 := by
    rw [hlogY, hHK]
    have hN2 : (16 : ℝ) * (n : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hq16 (by positivity)
    have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hlow' : Cd * ((n : ℝ) * (1 + Real.logb 2 n)) + (q : ℝ) * Real.logb 2 H * n <
        (n : ℝ) ^ 2 / 100 := by
      have : 100 * Cd * (n : ℝ) * (1 + Real.logb 2 n) + 100 * ((q : ℝ) * Real.logb 2 H) * n =
          100 * (Cd * ((n : ℝ) * (1 + Real.logb 2 n)) + (q : ℝ) * Real.logb 2 H * n) := by ring
      linarith
    linarith
  have hcrit' : 1 ≤ (∏ ℓ' ∈ S, (ℓ' : ℝ) ^ E ℓ') * PadicWin.l1Mv Δ * (H : ℝ) ^ K * ‖Z‖ := hcrit
  rw [Real.logb_neg_iff (by norm_num) hYpos] at hsum
  exact absurd hcrit' (not_le.mpr hsum)

/-- **Paper II, Corollary 1.2 (both parts) from Theorem 1.1** (II, §7). -/
theorem cor_1_2_of_thm (h : Thm11) : Cor12Window ∧ Cor12Sets :=
  ⟨cor_window_of_thm h, cor_sets_of_thm h⟩

end TwoAdicWin
