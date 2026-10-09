import RequestProject.TwoAdic.NVEntries

/-!
# II, Theorem 6.4: the determinant of the leading blocks, and the total weight

* `padicNorm_det_Nm`: `det Nm` is an `ℓ`-adic unit: `Nm` is block diagonal, one block
  `[g_k(a+b)]_{a,b<q}` per affected node, with `g_k(s) = ℓ^{V−s} β_{k,s}` for `s < q` and `0` otherwise,
  so each block is anti-triangular with determinant `±(ℓ^{d+2} β_{k,q−1})^q`, a unit
  (`PadicWin.det_antiHankel`, `betaC_last_norm`);
* `two_sum_wt`: `2 ∑_x ϖ_x = q n (d + 2)`;
* `VB_det`: a determinant of an `ℓ`-integral matrix is `ℓ`-integral.
-/

open Polynomial Finset PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ} [Fact ℓ.Prime]

/-- The block function `g_k(s) = ℓ^{V−s} β_{k,s}` (`s < q`). -/
noncomputable def gB (ℓ q d n : ℕ) (k : ℤ) (s : ℕ) : ℚ :=
  if s < q then (ℓ : ℚ) ^ (q + d + 1 - s) * betaC q d n k s else 0

theorem padicNorm_det_Nm (h : Hyp q d n ℓ) :
    padicNorm ℓ (Matrix.of (Nm ℓ q d n)).det = 1 := by
  let e : HIdx q n ≃ Fin q × ↥(aff n) :=
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  have hblk : Matrix.of (Nm ℓ q d n) = (Matrix.blockDiagonal
      (fun k : ↥(aff n) => Matrix.of fun a b : Fin q => gB ℓ q d n k ((a : ℕ) + b))).submatrix e e := by
    ext x y
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    simp only [e, Equiv.trans_apply, Equiv.sigmaEquivProd_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
    unfold Nm gB
    by_cases hij : i = j
    · subst hij
      simp only [if_true, true_and]
      have hx := a.isLt
      have hy := b.isLt
      have hV := h.V_even
      have hqd := h.adm.2.2.2.1
      split_ifs
      · congr 2; unfold wt; simp only; omega
      · rfl
    · have : ¬ ((i : ℤ) = j) := fun e => hij (Subtype.ext e)
      simp [hij, this]
  rw [hblk, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, padicNorm_prod]
  refine prod_eq_one fun k _ => ?_
  rw [det_antiHankel q (gB ℓ q d n k) (fun s hs => by unfold gB; rw [if_neg (by omega)]),
    padicNorm.mul, padicNorm_pow']
  have hq := h.adm.1
  have hg : gB ℓ q d n k (q - 1) = (ℓ : ℚ) ^ (d + 2) * betaC q d n k (q - 1) := by
    unfold gB; rw [if_pos (by omega)]; congr 2; omega
  rw [hg, betaC_last_norm h k.2, one_pow, mul_one]
  rcases Int.units_eq_one_or (Fin.revPerm : Equiv.Perm (Fin q)).sign with h1 | h1 <;>
    simp [h1]

omit [Fact ℓ.Prime] in
/-- **The total weight**: `2 ∑_x ϖ_x = q n (d + 2)`. -/
theorem two_sum_wt (h : Hyp q d n ℓ) : 2 * ∑ x : HIdx q n, wt q d x = q * n * (d + 2) := by
  rw [Fintype.sum_sigma]
  simp only [wt]
  rw [sum_const, card_univ, Fintype.card_coe, card_aff h, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun a => (q + d + 1) / 2 - a) q]
  have hqd := h.adm.2.2.2.1
  have hq1 := h.adm.1
  have hV : (q + d + 1) / 2 * 2 = q + d + 1 := h.V_even
  set c := (q + d + 1) / 2 with hc
  have hle : ∀ a ∈ range q, a ≤ c := by intro a ha; rw [mem_range] at ha; omega
  clear_value c
  have hsum : ((∑ a ∈ range q, (c - a) : ℕ) : ℤ) = q * c - ∑ a ∈ range q, (a : ℤ) := by
    rw [Nat.cast_sum, sum_congr rfl fun a ha => Nat.cast_sub (hle a ha), sum_sub_distrib, sum_const,
      card_range, nsmul_eq_mul]
  have hid := Finset.sum_range_id_mul_two q
  have hid' : (∑ a ∈ range q, (a : ℤ)) * 2 = (q : ℤ) * ((q : ℤ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hid
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] at this
    rw [this, Nat.cast_sub (by omega)]; simp
  have hV' : (c : ℤ) * 2 = q + d + 1 := by exact_mod_cast hV
  have key : ((2 * (n * ∑ a ∈ range q, (c - a)) : ℕ) : ℤ) = ((q * n * (d + 2) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, hsum]
    push_cast
    linear_combination (n : ℤ) * (q * hV' - hid')
  exact_mod_cast key

theorem VB_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ)
    (hM : ∀ i j, VB ℓ (M i j) 0) : VB ℓ M.det 0 := by
  rw [Matrix.det_apply]
  refine VB.sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have := (VB_intCast (ℓ := ℓ) (σ.sign : ℤ)).mul
    (VB.prod (ℓ := ℓ) univ (fun i => M (σ i) i) (fun _ => 0) fun i _ => hM _ _)
  simpa using this

end TwoAdicWin.Dom
