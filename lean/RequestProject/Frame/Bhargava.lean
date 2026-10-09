import RequestProject.Zeta7.Hankel2.Valuation

/-!
# Bhargava basis bound for a `ℚ`-linear moment functional (any prime `p`)

For a `ℚ`-linear functional `Λ : ℚ[x] → ℚ_p` and the shifted binomial basis
`B_i(x) = C(x − a₀, i) = (x − a₀)(x − a₀ − 1)⋯(x − a₀ − i + 1)/i!` (`shBinom`), if all entries
`Λ(B_i B_k)` (`i, k < K`) have norm `≤ c`, then
`‖det[Λ(x^{i+j})]_{i,j<K}‖_p ≤ c^K ∏_{i<K} ‖i!‖_p²` (`norm_hankel_det_le_shBinom`).
(P, Lemma 4.2; II, proof of Theorem 3.1, with `a₀ = 1/2`.)  This is
`Hankel2.norm_hankel_det_le_of_binom` with the basis shifted by `a₀` and `Λ` defined on `ℚ[x]`.
-/

open Finset Matrix Polynomial

namespace PadicWin

/-- `B_i(x) = C(x − a₀, i)`. -/
noncomputable def shBinom (a0 : ℚ) (i : ℕ) : ℚ[X] :=
  C ((i.factorial : ℚ)⁻¹) * (descPochhammer ℚ i).comp (X - C a0)

theorem natDegree_shBinom (a0 : ℚ) (i : ℕ) : (shBinom a0 i).natDegree = i := by
  unfold shBinom
  rw [natDegree_C_mul (inv_ne_zero (by exact_mod_cast (Nat.factorial_pos i).ne')),
    natDegree_comp, descPochhammer_natDegree, natDegree_X_sub_C, mul_one]

theorem coeff_shBinom_self (a0 : ℚ) (i : ℕ) :
    (shBinom a0 i).coeff i = (i.factorial : ℚ)⁻¹ := by
  unfold shBinom
  rw [coeff_C_mul]
  have hm : ((descPochhammer ℚ i).comp (X - C a0)).Monic :=
    (monic_descPochhammer ℚ i).comp (monic_X_sub_C a0) (by rw [natDegree_X_sub_C]; omega)
  have hd : ((descPochhammer ℚ i).comp (X - C a0)).natDegree = i := by
    rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_sub_C, mul_one]
  have := hm.coeff_natDegree
  rw [hd] at this
  rw [this, mul_one]

theorem coeff_shBinom_eq_zero (a0 : ℚ) {i a : ℕ} (h : i < a) : (shBinom a0 i).coeff a = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_shBinom]; exact h)

/-- `B_i(a₀ + u) = C(u, i)` at natural `u`. -/
theorem shBinom_eval_nat (a0 : ℚ) (i u : ℕ) :
    (shBinom a0 i).eval ((u : ℚ) + a0) = (u.choose i : ℚ) := by
  unfold shBinom
  rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- The coefficient matrix `T_{a i} = [x^a] B_i`. -/
noncomputable def shMat (a0 : ℚ) (K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun a i => (shBinom a0 i).coeff a

theorem shMat_det (a0 : ℚ) (K : ℕ) : (shMat a0 K).det = ∏ i : Fin K, ((i : ℕ).factorial : ℚ)⁻¹ := by
  rw [Matrix.det_of_upperTriangular]
  · simp [shMat, coeff_shBinom_self]
  · intro i j hij
    simp only [shMat, Matrix.of_apply]
    exact coeff_shBinom_eq_zero a0 hij

theorem shBinom_eq_sum (a0 : ℚ) (K : ℕ) (i : Fin K) :
    shBinom a0 i = ∑ a : Fin K, C (shMat a0 K a i) * X ^ (a : ℕ) := by
  conv_lhs => rw [(shBinom a0 i).as_sum_range' K (by rw [natDegree_shBinom]; exact i.isLt)]
  rw [← Fin.sum_univ_eq_sum_range (fun a => monomial a ((shBinom a0 i).coeff a)) K]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [shMat, C_mul_X_pow_eq_monomial]

variable {p : ℕ} [Fact p.Prime]

theorem Lam_binom_mul (a0 : ℚ) (K : ℕ) (Λ : ℚ[X] →ₗ[ℚ] ℚ_[p]) (i k : Fin K) :
    Λ (shBinom a0 i * shBinom a0 k) =
      ∑ a : Fin K, ∑ b : Fin K, ((shMat a0 K a i : ℚ) : ℚ_[p]) * ((shMat a0 K b k : ℚ) : ℚ_[p]) *
        Λ (X ^ ((a : ℕ) + (b : ℕ))) := by
  rw [shBinom_eq_sum a0 K i, shBinom_eq_sum a0 K k, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : C (shMat a0 K a i) * X ^ (a : ℕ) * (C (shMat a0 K b k) * X ^ (b : ℕ)) =
      (shMat a0 K a i * shMat a0 K b k) • X ^ ((a : ℕ) + (b : ℕ)) := by
    rw [smul_eq_C_mul, pow_add, C_mul]; ring
  rw [this, map_smul, Rat.smul_def]
  push_cast; ring

/-- **The Bhargava bound** for a `ℚ`-linear moment functional and the shifted binomial basis. -/
theorem norm_hankel_det_le_shBinom (K : ℕ) (Λ : ℚ[X] →ₗ[ℚ] ℚ_[p]) (a0 : ℚ) (c : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ i k : ℕ, i < K → k < K → ‖Λ (shBinom a0 i * shBinom a0 k)‖ ≤ c) :
    ‖(Matrix.of fun i j : Fin K => Λ (X ^ ((i : ℕ) + (j : ℕ)))).det‖ ≤
      c ^ K * ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[p])‖ ^ 2 := by
  set T : Matrix (Fin K) (Fin K) ℚ_[p] := (shMat a0 K).map (fun r : ℚ => (r : ℚ_[p]))
  set H := (Matrix.of fun i j : Fin K => Λ (X ^ ((i : ℕ) + (j : ℕ))))
  set G := (Matrix.of fun i k : Fin K => ∑ a : Fin K, ∑ b : Fin K,
        T a i * T b k * Λ (X ^ ((a : ℕ) + (b : ℕ))))
  have hG : G.det = T.det ^ 2 * H.det :=
    Hankel2.det_moment_basis_change K (fun e => Λ (X ^ e)) T
  have hGnorm : ‖G.det‖ ≤ c ^ K := by
    refine Hankel2.norm_det_le_max_perm G (c ^ K) (pow_nonneg hc K) fun σ => ?_
    calc ∏ i, ‖G (σ i) i‖ ≤ ∏ _i : Fin K, c := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
          simp only [G, T, Matrix.of_apply, Matrix.map_apply]
          rw [← Lam_binom_mul]
          exact hentry _ _ (σ i).isLt i.isLt
      _ = c ^ K := by simp
  have hdetT : T.det = ∏ i : Fin K, (((i : ℕ).factorial : ℚ_[p]))⁻¹ := by
    have h := (Rat.castHom ℚ_[p]).map_det (shMat a0 K)
    simp only [Rat.coe_castHom] at h
    rw [show T = (Rat.castHom ℚ_[p]).mapMatrix (shMat a0 K) from rfl, ← h, shMat_det]
    push_cast; rfl
  have hprod : (∏ i : Fin K, ((i : ℕ).factorial : ℚ_[p])) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hH : H.det = G.det * (∏ i : Fin K, ((i : ℕ).factorial : ℚ_[p])) ^ 2 := by
    rw [hG, hdetT, Finset.prod_inv_distrib]
    field_simp
  rw [hH, norm_mul, norm_pow, norm_prod, ← Finset.prod_pow]
  exact mul_le_mul_of_nonneg_right hGnorm
    (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)

end PadicWin
