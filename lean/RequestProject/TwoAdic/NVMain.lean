import RequestProject.TwoAdic.NVGramId

/-!
# II, Theorem 6.4 (strict dominance at `ℓ = 2n + 1`) — field `nonvanishing`

For admissible `(q, d)`, even `n`, `ℓ = 2n + 1` prime with `ℓ > q + d + 1` and `K = qn`:
`v_ℓ([X⁰]Δ_K) = −qn(d+2)` and `v_ℓ([X⁰]Δ_K) < v_ℓ([X^α]Δ_K)` for every other monomial with a nonzero
coefficient (`dominance`; `nonvanishing_field` is the field `nonvanishing` of `TwoAdicInputsOpen`
verbatim).

Proof (II, §6).  Let `E` be the basis dual to the jets at the affected nodes (`exists_basis`) and
`C` its coefficient matrix, which is unimodular (`padicNorm_det_coeff`), and let
`G = [L_X(E_x E_y)]`, so that `det(C)^2 Δ_K = det G` (`hankel_gram`).  The scaled matrix
`S = [ℓ^{ϖ_x+ϖ_y} G_{xy}]` has entries in `domSub` (constant coefficient `ℓ`-integral, all other
coefficients divisible by `ℓ`: `aL_entry`, `bL_entry`), and its constant part is congruent modulo `ℓ`
to the block-diagonal matrix `Nm` of unit determinant (`padicNorm_det_Nm`).  Hence `det S ∈ domSub`
with unit constant coefficient (`det_mem_domSub`, `coeff_zero_det`, `det_congr_mod`), and
`det S = ℓ^{2∑ϖ} det(C)^2 Δ_K` with `2∑ϖ = qn(d+2)` (`two_sum_wt`).
-/

open Polynomial Finset PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ}

theorem mem_domSub_C_mul_X [Fact ℓ.Prime] {σ : Type*} {c : ℚ} (hc : VB ℓ c 1) (j : σ) :
    MvPolynomial.C c * MvPolynomial.X j ∈ domSub ℓ σ := by
  classical
  refine mem_domSub_of_VB_one fun m => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using (VB_zero (ℓ := ℓ) 1)

theorem coeff_zero_C_mul_X {σ : Type*} (c : ℚ) (j : σ) :
    (MvPolynomial.C c * MvPolynomial.X j : MvPolynomial σ ℚ).coeff 0 = 0 := by
  classical
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', if_neg]
  · simp
  · intro h
    have := congrArg (fun f => f j) h
    simp at this

/-- **II, Theorem 6.4 (strict dominance).** -/
theorem dominance (h : Hyp q d n ℓ) :
    (hankelPoly q d n (q * n)).coeff 0 ≠ 0 ∧
      padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) = -((q * n * (d + 2) : ℕ) : ℤ) ∧
      ∀ m, m ≠ 0 → (hankelPoly q d n (q * n)).coeff m ≠ 0 →
        padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) <
          padicValRat ℓ ((hankelPoly q d n (q * n)).coeff m) := by
  haveI := Fact.mk h.prime
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_basis h
  have hcard := card_HIdx h
  set K := q * n with hK
  let e : HIdx q n ≃ Fin K := Fintype.equivFinOfCardEq hcard
  set Cm : Matrix (Fin K) (Fin K) ℚ := fun dd c => (E (e.symm c)).coeff dd with hCm
  have hsum : ∀ c, E (e.symm c) = ∑ dd : Fin K, Polynomial.C (Cm dd c) * X ^ (dd : ℕ) :=
    fun c => Hankel2.W3.Fam3.poly_eq_sum_fin _ (fun m hm => hE3 _ m (by omega))
  -- the change of basis is unimodular
  have hCm1 : padicNorm ℓ Cm.det = 1 := by
    refine padicNorm_det_coeff K e E Cm hsum (fun y => (y.1 : ℤ)) (fun y => (y.2 : ℕ))
      (fun x y => ?_) (fun dd c => ?_)
    · rw [hE1 x y.1 y.2 y.2.isLt]
    · simpa [VB] using hE2 _ _
  -- the Gram matrix
  set G : Matrix (HIdx q n) (HIdx q n) (MvPolynomial (Fin (rr q)) ℚ) :=
    Matrix.of fun x y => LX q d n (E x * E y) with hG
  have hgram : MvPolynomial.C Cm.det ^ 2 * hankelPoly q d n K = G.det :=
    hankel_gram K e E Cm hsum
  -- the scaled matrix
  set S : Matrix (HIdx q n) (HIdx q n) (MvPolynomial (Fin (rr q)) ℚ) :=
    Matrix.of fun x y => MvPolynomial.C ((ℓ : ℚ) ^ (wt q d x + wt q d y)) * G x y with hSdef
  set N := q * n * (d + 2) with hN
  have hS : S.det = MvPolynomial.C ((ℓ : ℚ) ^ N) * G.det := by
    have e1 : S = Matrix.of fun x y => MvPolynomial.C ((ℓ : ℚ) ^ (wt q d y)) *
        (Matrix.of fun x y => MvPolynomial.C ((ℓ : ℚ) ^ (wt q d x)) * G x y) x y := by
      ext1 x y
      simp only [hSdef, Matrix.of_apply, pow_add, map_mul]
      ring
    rw [e1, Matrix.det_mul_row, Matrix.det_mul_column, ← mul_assoc, ← map_prod,
      ← map_mul, prod_pow_eq_pow_sum, ← pow_add, ← two_mul, two_sum_wt h]
  have hSentry : ∀ x y, S x y = MvPolynomial.C ((ℓ : ℚ) ^ (wt q d x + wt q d y) * bL q d n (E x * E y)) +
      ∑ j : Fin (rr q), MvPolynomial.C ((ℓ : ℚ) ^ (wt q d x + wt q d y) * aL q d n j (E x * E y)) *
        MvPolynomial.X j := by
    intro x y
    simp only [hSdef, hG, Matrix.of_apply, LX, mul_add, Finset.mul_sum, map_mul, mul_assoc]
  have hmem : ∀ x y, S x y ∈ domSub ℓ (Fin (rr q)) := by
    intro x y
    rw [hSentry]
    refine (domSub ℓ _).add_mem (C_mem_domSub ?_)
      ((domSub ℓ _).sum_mem fun j _ => mem_domSub_C_mul_X (aL_entry h E hE1 hE2 x y j) j)
    have h1 := bL_entry h E hE1 hE2 x y
    have h2 := Nm_int h x y
    simpa using (h1.mono (by norm_num)).add h2
  have hcoeff0 : ∀ x y, (S x y).coeff 0 = (ℓ : ℚ) ^ (wt q d x + wt q d y) * bL q d n (E x * E y) := by
    intro x y
    rw [hSentry, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.coeff_sum,
      Finset.sum_eq_zero (fun j _ => coeff_zero_C_mul_X _ j), add_zero]
  have hdom := det_mem_domSub S hmem
  have hcong := det_congr_mod (S.map fun P => P.coeff 0) (Matrix.of (Nm ℓ q d n))
    (fun x y => Nm_int h x y) (fun x y => by
      simp only [Matrix.map_apply, Matrix.of_apply, hcoeff0]
      exact bL_entry h E hE1 hE2 x y)
  have hNm := padicNorm_det_Nm h
  have hS0n : padicNorm ℓ (S.det.coeff 0) = 1 := by
    rw [coeff_zero_det]
    set a := (S.map fun P => P.coeff 0).det
    set b := (Matrix.of (Nm ℓ q d n)).det
    have hab : padicNorm ℓ (a - b) < 1 := by
      have := hcong
      unfold VB at this
      refine lt_of_le_of_lt this ?_
      have : (1 : ℚ) < ℓ := one_lt_ell
      rw [zpow_neg, zpow_one]
      exact inv_lt_one_of_one_lt₀ this
    have hne : padicNorm ℓ (a - b) ≠ padicNorm ℓ b := by rw [hNm]; exact hab.ne
    have := padicNorm.add_eq_max_of_ne hne
    rw [sub_add_cancel, hNm, max_eq_right hab.le] at this
    exact this
  -- relation between the coefficients
  have hrel : ∀ m, S.det.coeff m =
      ((ℓ : ℚ) ^ N * Cm.det ^ 2) * (hankelPoly q d n K).coeff m := by
    intro m
    rw [hS, ← hgram, ← mul_assoc, ← map_pow, ← map_mul, MvPolynomial.coeff_C_mul]
  have hl0 : (0 : ℚ) < ℓ := ell_pos
  have hl1 : (1 : ℚ) < ℓ := one_lt_ell
  have hA : padicNorm ℓ ((ℓ : ℚ) ^ N * Cm.det ^ 2) = ((ℓ : ℚ)⁻¹) ^ N := by
    rw [padicNorm.mul, padicNorm_pow', padicNorm_pow', hCm1, padicNorm.padicNorm_p_of_prime]
    simp
  have hlN : (0 : ℚ) < (ℓ : ℚ) ^ N := pow_pos hl0 N
  have hinv : ((ℓ : ℚ)⁻¹) ^ N * (ℓ : ℚ) ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  -- the constant coefficient
  have h0 : padicNorm ℓ ((hankelPoly q d n K).coeff 0) = (ℓ : ℚ) ^ N := by
    have := congrArg (padicNorm ℓ) (hrel 0)
    rw [padicNorm.mul, hA, hS0n] at this
    have e2 : padicNorm ℓ ((hankelPoly q d n K).coeff 0) =
        (ℓ : ℚ) ^ N * (((ℓ : ℚ)⁻¹) ^ N * padicNorm ℓ ((hankelPoly q d n K).coeff 0)) := by
      rw [← mul_assoc, mul_comm ((ℓ : ℚ) ^ N), hinv, one_mul]
    rw [e2, ← this, mul_one]
  have hΔ0 : (hankelPoly q d n K).coeff 0 ≠ 0 := by
    intro h0'
    rw [h0', padicNorm.zero] at h0
    exact hlN.ne' h0.symm
  have hv0 : padicValRat ℓ ((hankelPoly q d n K).coeff 0) = -(N : ℤ) := by
    have := padicNorm.eq_zpow_of_nonzero (p := ℓ) hΔ0
    rw [h0, ← zpow_natCast] at this
    have := (zpow_right_inj₀ hl0 hl1.ne').1 this
    omega
  refine ⟨hΔ0, hv0, fun m hm hΔm => ?_⟩
  -- the other coefficients
  have hVB : VB ℓ (S.det.coeff m) 1 := by
    have := hdom m
    rwa [if_neg hm] at this
  have hlt : padicNorm ℓ ((hankelPoly q d n K).coeff m) <
      padicNorm ℓ ((hankelPoly q d n K).coeff 0) := by
    rw [h0]
    unfold VB at hVB
    rw [hrel, padicNorm.mul, hA, zpow_neg, zpow_one] at hVB
    have hx := padicNorm.nonneg (p := ℓ) ((hankelPoly q d n K).coeff m)
    have e2 : padicNorm ℓ ((hankelPoly q d n K).coeff m) =
        (ℓ : ℚ) ^ N * (((ℓ : ℚ)⁻¹) ^ N * padicNorm ℓ ((hankelPoly q d n K).coeff m)) := by
      rw [← mul_assoc, mul_comm ((ℓ : ℚ) ^ N), hinv, one_mul]
    rw [e2]
    calc (ℓ : ℚ) ^ N * (((ℓ : ℚ)⁻¹) ^ N * padicNorm ℓ ((hankelPoly q d n K).coeff m))
        ≤ (ℓ : ℚ) ^ N * (ℓ : ℚ)⁻¹ := mul_le_mul_of_nonneg_left hVB hlN.le
      _ < (ℓ : ℚ) ^ N * 1 := mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hl1) hlN
      _ = (ℓ : ℚ) ^ N := mul_one _
  rw [padicNorm.eq_zpow_of_nonzero hΔm, padicNorm.eq_zpow_of_nonzero hΔ0,
    zpow_lt_zpow_iff_right₀ hl1] at hlt
  omega

/-- **Field (iv) `nonvanishing` of `TwoAdicInputsOpen`, discharged** (II, Theorem 6.4), verbatim. -/
theorem nonvanishing_field : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ = 2 * n + 1 → ℓ.Prime →
    q + d + 1 < ℓ →
      (hankelPoly q d n (q * n)).coeff 0 ≠ 0 ∧
      padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) = -((q * n * (d + 2) : ℕ) : ℤ) ∧
      ∀ m, m ≠ 0 → (hankelPoly q d n (q * n)).coeff m ≠ 0 →
        padicValRat ℓ ((hankelPoly q d n (q * n)).coeff 0) <
          padicValRat ℓ ((hankelPoly q d n (q * n)).coeff m) :=
  fun _ _ _ _ hadm hn hℓ hp hbig => dominance ⟨hadm, hn, hℓ, hp, hbig⟩

end TwoAdicWin.Dom
