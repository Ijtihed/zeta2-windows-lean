import RequestProject.Frame.Criterion
import RequestProject.Zeta7.Hankel2.ArchL1

/-!
# The `ℓ¹` norm on `ℚ[X_σ]` (any parameters)

`l1Mv F = ∑_m |[X^m]F|` (`PadicWin.l1Mv`) equals the real `ℓ¹` norm `mvl1` of the image of `F` in
`ℝ[X_σ]` (`l1Mv_eq_mvl1`).  Consequently it is subadditive, submultiplicative, and satisfies the
determinant bound `‖det M‖₁ ≤ (card ι)! A^{card ι}` (`l1Mv_det_le`).
-/

open Finset

namespace PadicWin

open MvPolynomial Hankel2.ArchB

variable {σ : Type*}

theorem l1Mv_eq_mvl1 (F : MvPolynomial σ ℚ) :
    l1Mv F = mvl1 (MvPolynomial.map (Rat.castHom ℝ) F) := by
  unfold l1Mv mvl1
  have hs : (MvPolynomial.map (Rat.castHom ℝ) F).support = F.support :=
    MvPolynomial.support_map_of_injective _ (Rat.castHom ℝ).injective
  rw [hs]
  refine sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]; rfl

theorem l1Mv_nonneg (F : MvPolynomial σ ℚ) : 0 ≤ l1Mv F :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem l1Mv_zero : l1Mv (0 : MvPolynomial σ ℚ) = 0 := by simp [l1Mv]

theorem l1Mv_add_le (F G : MvPolynomial σ ℚ) : l1Mv (F + G) ≤ l1Mv F + l1Mv G := by
  simp only [l1Mv_eq_mvl1, map_add]; exact mvl1_add_le _ _

theorem l1Mv_sum_le {α : Type*} (s : Finset α) (F : α → MvPolynomial σ ℚ) :
    l1Mv (∑ a ∈ s, F a) ≤ ∑ a ∈ s, l1Mv (F a) := by
  simp only [l1Mv_eq_mvl1, map_sum]; exact mvl1_sum_le _ _

theorem l1Mv_mul_le (F G : MvPolynomial σ ℚ) : l1Mv (F * G) ≤ l1Mv F * l1Mv G := by
  simp only [l1Mv_eq_mvl1, map_mul]; exact mvl1_mul_le _ _

theorem l1Mv_prod_le {α : Type*} (s : Finset α) (F : α → MvPolynomial σ ℚ) :
    l1Mv (∏ a ∈ s, F a) ≤ ∏ a ∈ s, l1Mv (F a) := by
  simp only [l1Mv_eq_mvl1, map_prod]; exact mvl1_prod_le _ _

theorem l1Mv_C (c : ℚ) : l1Mv (MvPolynomial.C c : MvPolynomial σ ℚ) = |(c : ℝ)| := by
  rw [l1Mv_eq_mvl1, MvPolynomial.map_C, mvl1_C]; rfl

theorem l1Mv_X (i : σ) : l1Mv (MvPolynomial.X i : MvPolynomial σ ℚ) = 1 := by
  rw [l1Mv_eq_mvl1, MvPolynomial.map_X, mvl1_X]

theorem l1Mv_neg (F : MvPolynomial σ ℚ) : l1Mv (-F) = l1Mv F := by
  simp only [l1Mv_eq_mvl1, map_neg]; exact mvl1_neg _

theorem l1Mv_zsmul (u : ℤˣ) (F : MvPolynomial σ ℚ) : l1Mv (u • F) = l1Mv F := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, l1Mv_neg]

theorem l1Mv_C_mul_mul_C_le (a b : ℚ) (P : MvPolynomial σ ℚ) :
    l1Mv (MvPolynomial.C a * P * MvPolynomial.C b) ≤ |(a : ℝ)| * l1Mv P * |(b : ℝ)| := by
  refine (l1Mv_mul_le _ _).trans ?_
  rw [l1Mv_C]
  exact mul_le_mul_of_nonneg_right ((l1Mv_mul_le _ _).trans (by rw [l1Mv_C])) (abs_nonneg _)

/-- **Determinant bound**: if every entry has `‖M_{ij}‖₁ ≤ A` then
`‖det M‖₁ ≤ (card ι)! · A^{card ι}`. -/
theorem l1Mv_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (A : ℝ) (hM : ∀ i j, l1Mv (M i j) ≤ A) :
    l1Mv M.det ≤ (Fintype.card ι).factorial * A ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (l1Mv_sum_le _ _).trans ?_
  have h1 : ∀ τ : Equiv.Perm ι, l1Mv (Equiv.Perm.sign τ • ∏ i, M (τ i) i) ≤
      A ^ Fintype.card ι := by
    intro τ
    rw [l1Mv_zsmul]
    refine (l1Mv_prod_le _ _).trans ?_
    calc ∏ i, l1Mv (M (τ i) i) ≤ ∏ _i : ι, A :=
          prod_le_prod (fun i _ => l1Mv_nonneg _) (fun i _ => hM _ _)
      _ = A ^ Fintype.card ι := by rw [prod_const, card_univ]
  refine (sum_le_sum fun τ _ => h1 τ).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem l1Mv_pos_of_ne {F : MvPolynomial σ ℚ} (hF : F ≠ 0) : 0 < l1Mv F := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hF
  have hms : m ∈ F.support := MvPolynomial.mem_support_iff.2 hm
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun m => |((F.coeff m : ℚ) : ℝ)|)
    (fun _ _ => abs_nonneg _) hms)
  simp only [abs_pos, ne_eq, Rat.cast_eq_zero]; exact hm

end PadicWin
