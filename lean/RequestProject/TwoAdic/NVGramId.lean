import RequestProject.TwoAdic.NVDet

/-!
# II, Theorem 6.4: the change of basis

* `LXl`: the functional `L_X = b + ∑_j X_j a_j` as a `ℚ`-linear map `ℚ[x] → ℚ[X_1, …, X_r]`;
* `hankel_gram`: for any basis `E` of `ℚ[x]_{<K}` with coefficient matrix `C`,
  `det(C)^2 Δ_K = det[L_X(E_x E_y)]` (the Gram matrix of `(P, Q) ↦ L_X(PQ)` in the basis `E`);
* `padicNorm_det_coeff`: if the jets of the `E_x` at the interpolation conditions are `δ` and the
  coefficients are `ℓ`-integral, the change of basis is unimodular: `|det C|_ℓ = 1` (the matrix of the
  conditions on the monomials is integral and inverse to `C`).
-/

open Polynomial Finset PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ}

theorem Pjet_add' (F G : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (F + G) k a = Pjet F k a + Pjet G k a := by
  simp [Pjet, PF.Pjet]

theorem Pjet_smul' (c : ℚ) (F : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (c • F) k a = c * Pjet F k a := by
  simp [Pjet, PF.Pjet]

theorem Pjet_sum {α : Type*} (s : Finset α) (F : α → ℚ[X]) (k : ℤ) (a : ℕ) :
    Pjet (∑ i ∈ s, F i) k a = ∑ i ∈ s, Pjet (F i) k a := by
  simp [Pjet, PF.Pjet, map_sum, eval_finset_sum]

theorem bL_add (P Q : ℚ[X]) : bL q d n (P + Q) = bL q d n P + bL q d n Q := by
  simp only [bL, Pjet_add', mul_add, sum_add_distrib]

theorem bL_smul (c : ℚ) (P : ℚ[X]) : bL q d n (c • P) = c * bL q d n P := by
  simp only [bL, Pjet_smul', mul_sum]
  exact sum_congr rfl fun k _ => sum_congr rfl fun a _ => by ring

theorem aL_add (j : ℕ) (P Q : ℚ[X]) : aL q d n j (P + Q) = aL q d n j P + aL q d n j Q := by
  simp only [aL, Pjet_add', mul_add, sum_add_distrib]

theorem aL_smul (j : ℕ) (c : ℚ) (P : ℚ[X]) : aL q d n j (c • P) = c * aL q d n j P := by
  simp only [aL, Pjet_smul', mul_sum]
  exact sum_congr rfl fun k _ => sum_congr rfl fun a _ => by ring

/-- `L_X` as a `ℚ`-linear map. -/
noncomputable def LXl (q d n : ℕ) : ℚ[X] →ₗ[ℚ] MvPolynomial (Fin (rr q)) ℚ where
  toFun := LX q d n
  map_add' P Q := by
    simp only [LX, bL_add, aL_add, map_add, add_mul, sum_add_distrib]
    ring
  map_smul' c P := by
    simp only [LX, bL_smul, aL_smul, map_mul, RingHom.id_apply, MvPolynomial.smul_eq_C_mul,
      mul_add, mul_sum, mul_assoc]

theorem LXl_apply (P : ℚ[X]) : LXl q d n P = LX q d n P := rfl

/-- **The Gram identity**: `det(C)^2 Δ_K = det[L_X(E_x E_y)]`. -/
theorem hankel_gram (K : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin K)
    (E : ι → ℚ[X]) (Cm : Matrix (Fin K) (Fin K) ℚ)
    (hsum : ∀ c, E (e.symm c) = ∑ dd : Fin K, Polynomial.C (Cm dd c) * X ^ (dd : ℕ)) :
    MvPolynomial.C Cm.det ^ 2 * hankelPoly q d n K =
      (Matrix.of fun x y => LX q d n (E x * E y)).det := by
  set Hank : Matrix (Fin K) (Fin K) (MvPolynomial (Fin (rr q)) ℚ) :=
    Matrix.of fun i j : Fin K => LX q d n (X ^ ((i : ℕ) + j)) with hHank
  set Cp := Cm.map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin (rr q)) ℚ) with hCp
  have hmul : Cp.transpose * Hank * Cp =
      (Matrix.of fun x y => LX q d n (E x * E y)).submatrix e.symm e.symm := by
    refine Matrix.ext fun c c' => ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      hHank, hCp, Matrix.map_apply]
    rw [hsum c, hsum c', Finset.sum_mul_sum]
    have e2 : ∀ (a b : ℚ) (i j : ℕ),
        Polynomial.C a * X ^ i * (Polynomial.C b * X ^ j) = (a * b) • X ^ (i + j) := by
      intro a b i j; rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul, pow_add]; ring
    simp only [e2, ← LXl_apply (q := q) (d := d) (n := n), map_sum, map_smul, MvPolynomial.smul_eq_C_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  have h1 := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h1
  have hC : Cp.det = MvPolynomial.C Cm.det := by
    rw [hCp, RingHom.map_det]; rfl
  rw [← h1, hC]
  unfold hankelPoly
  ring

variable [Fact ℓ.Prime]

/-- **The change of basis is unimodular.** -/
theorem padicNorm_det_coeff (K : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin K)
    (E : ι → ℚ[X]) (Cm : Matrix (Fin K) (Fin K) ℚ)
    (hsum : ∀ c, E (e.symm c) = ∑ dd : Fin K, Polynomial.C (Cm dd c) * X ^ (dd : ℕ))
    (node : ι → ℤ) (jet : ι → ℕ)
    (hE : ∀ x y, Pjet (E x) (node y) (jet y) = if x = y then 1 else 0)
    (hint : ∀ dd c, VB ℓ (Cm dd c) 0) : padicNorm ℓ Cm.det = 1 := by
  set Jm : Matrix (Fin K) (Fin K) ℚ := fun i dd =>
    Pjet (X ^ (dd : ℕ)) (node (e.symm i)) (jet (e.symm i)) with hJm
  have hJC : Jm * Cm = 1 := by
    ext i c
    simp only [Matrix.mul_apply, hJm, Matrix.one_apply]
    have := hE (e.symm c) (e.symm i)
    rw [hsum c, Pjet_sum] at this
    simp only [← Polynomial.smul_eq_C_mul, Pjet_smul'] at this
    rw [show (∑ x : Fin K, Pjet (X ^ (x : ℕ)) (node (e.symm i)) (jet (e.symm i)) * Cm x c) =
      ∑ x : Fin K, Cm x c * Pjet (X ^ (x : ℕ)) (node (e.symm i)) (jet (e.symm i)) from
      sum_congr rfl fun _ _ => mul_comm _ _, this]
    simp only [e.symm.injective.eq_iff]
    by_cases hic : i = c
    · subst hic; simp
    · rw [if_neg (Ne.symm hic), if_neg hic]
  have hJint : ∀ i dd, VB ℓ (Jm i dd) 0 := by
    intro i dd
    simp only [hJm, Pjet, PF.Pjet, VB]
    rw [show (-((node (e.symm i) : ℤ) : ℚ)) = (((-node (e.symm i) : ℤ)) : ℚ) by push_cast; ring]
    have := Hankel2.W3.Fam3.padicNorm_jet_le_one (p := ℓ) (X ^ (dd : ℕ)) (fun m => by
      rw [coeff_X_pow]; split_ifs <;> simp) (-node (e.symm i)) (jet (e.symm i))
    simpa using this
  have hdet := congrArg Matrix.det hJC
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have h1 : padicNorm ℓ Jm.det ≤ 1 := by simpa [VB] using VB_det Jm hJint
  have h2 : padicNorm ℓ Cm.det ≤ 1 := by simpa [VB] using VB_det Cm (fun i j => hint i j)
  have h3 : padicNorm ℓ Jm.det * padicNorm ℓ Cm.det = 1 := by
    rw [← padicNorm.mul, hdet, padicNorm.one]
  have h4 := padicNorm.nonneg (p := ℓ) Jm.det
  have h5 := padicNorm.nonneg (p := ℓ) Cm.det
  nlinarith

end TwoAdicWin.Dom
