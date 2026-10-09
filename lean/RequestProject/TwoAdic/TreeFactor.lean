import RequestProject.TwoAdic.InputDefs
import RequestProject.Zeta7.Hankel2.CauchyBinet

/-!
# Tree bound, step 1: the factorisation `Δ_K = det(E · C · Eᵀ)` (P, §7)

General-`q`, several-variable version of `Zeta35.hankelPoly_eq_det`.  Index the columns by
`ι = Fin (2R+1) ×ₗ Fin q` (node `u`, Taylor order `b`).  Then
`L_X(x^{i+j}) = ∑_u ∑_{b,b'} E_{i,(u,b)} c_{u,b+b'} E_{j,(u,b')}` with the confluent Vandermonde
matrix `E_{i,(u,b)} = C(i,b) (−k_u)^{i−b}` (`EmatQ`) and the block-diagonal matrix
`C_{(u,b),(u',b')} = [u = u'] c_{u,b+b'}` (`CblQ`), by the Leibniz rule for the Taylor
coefficients `P_a(k) = [u^a] P(−k + u)`.
-/

open Polynomial Finset Matrix

namespace TwoAdicWin

open Hankel2

/-- The column index set `ι = Fin (2R+1) ×ₗ Fin q`. -/
abbrev IdxQ (q n : ℕ) := Lex (Fin (2 * R n + 1) × Fin q)

/-- `E_{i,(u,b)} = C(i,b) x_u^{i−b}`, `x_u = −k_u`. -/
noncomputable def EmatQ (q n K : ℕ) : Matrix (Fin K) (IdxQ q n) ℚ := fun i c =>
  ((i : ℕ).choose (ofLex c).2 : ℚ) * (-((nodeOf n (ofLex c).1 : ℤ) : ℚ)) ^ ((i : ℕ) - (ofLex c).2)

/-- The block-diagonal matrix `[u = u'] c_{u,b+b'}`. -/
noncomputable def CblQ (q d n : ℕ) :
    Matrix (IdxQ q n) (IdxQ q n) (MvPolynomial (Fin (rr q)) ℚ) := fun c e =>
  if (ofLex c).1 = (ofLex e).1 then cMv q d n (nodeOf n (ofLex c).1) ((ofLex c).2 + (ofLex e).2)
  else 0

theorem cMv_eq_zero {q d n : ℕ} {k : ℤ} {m : ℕ} (hm : q ≤ m) : cMv q d n k m = 0 := by
  simp [cMv, show ¬ m < q by omega]

theorem sum_rangeQ_antidiag {S : Type*} [CommRing S] (q : ℕ) (g : ℕ → S)
    (hg : ∀ m, q ≤ m → g m = 0) (h : ℕ → ℕ → S) :
    ∑ a ∈ range q, g a * ∑ x ∈ antidiagonal a, h x.1 x.2 =
      ∑ b : Fin q, ∑ b' : Fin q, g (b + b') * h b b' := by
  rw [Fin.sum_univ_eq_sum_range (fun b => ∑ b' : Fin q, g (b + b') * h b b') q]
  rw [Finset.sum_congr rfl fun b _ => Fin.sum_univ_eq_sum_range (fun b' => g (b + b') * h b b') q]
  simp_rw [Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_comm' (t' := range q) (s' := fun k => Ico k q)]
  · refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [Finset.sum_Ico_eq_sum_range]
    rw [← Finset.sum_subset (range_subset_range.2 (Nat.sub_le q k))]
    · refine sum_congr rfl fun b' hb' => ?_
      simp only [add_tsub_cancel_left]
    · intro b' hb' hb''
      simp only [mem_range, not_lt] at hb' hb''
      rw [hg _ (by omega), zero_mul]
  · intro a k
    simp only [mem_range, mem_Ico]
    omega

theorem hasseDeriv_X_pow_eval' (m a : ℕ) (x : ℚ) :
    (hasseDeriv a ((X : ℚ[X]) ^ m)).eval x = (m.choose a : ℚ) * x ^ (m - a) := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, eval_monomial, mul_one]

theorem pjet_X_pow' (k : ℤ) (i j a : ℕ) :
    Pjet (X ^ (i + j)) k a = ∑ x ∈ antidiagonal a,
      ((i.choose x.1 : ℚ) * (-(k : ℚ)) ^ (i - x.1)) * ((j.choose x.2 : ℚ) * (-(k : ℚ)) ^ (j - x.2)) := by
  rw [Pjet, PadicWin.PF.Pjet, pow_add, hasseDeriv_mul, eval_finset_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_mul, hasseDeriv_X_pow_eval', hasseDeriv_X_pow_eval']

theorem sum_nodes_eq' (n : ℕ) {M : Type*} [AddCommMonoid M] (F : ℤ → M) :
    ∑ k ∈ nodes n, F k = ∑ u : Fin (2 * R n + 1), F (nodeOf n u) := by
  symm
  refine sum_bij (fun u _ => nodeOf n u) ?_ ?_ ?_ ?_
  · intro u _
    simp only [nodes, mem_Icc, nodeOf]
    have := u.isLt
    omega
  · intro u _ v _ h
    simp only [nodeOf] at h
    exact Fin.ext (by omega)
  · intro k hk
    simp only [nodes, mem_Icc] at hk
    refine ⟨⟨(k + R n).toNat, by omega⟩, mem_univ _, ?_⟩
    simp only [nodeOf]
    omega
  · intro u _; rfl

theorem sum_idxQ {q n : ℕ} {M : Type*} [AddCommMonoid M] (F : IdxQ q n → M) :
    ∑ c : IdxQ q n, F c = ∑ u : Fin (2 * R n + 1), ∑ b : Fin q, F (toLex (u, b)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv toLex _ _ fun _ => rfl).symm

/-- `L_X(P) = ∑_k ∑_{a<q} c_{k,a} P_a(k)`. -/
theorem LX_eq_sum (q d n : ℕ) (P : ℚ[X]) :
    LX q d n P = ∑ u : Fin (2 * R n + 1), ∑ a ∈ range q,
      cMv q d n (nodeOf n u) a * MvPolynomial.C (Pjet P (nodeOf n u) a) := by
  rw [LX, bL]
  simp only [aL, sum_nodes_eq', map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := (univ : Finset (Fin (rr q)))), ← Finset.sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm (s := (univ : Finset (Fin (rr q)))), ← Finset.sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  rw [cMv, if_pos (by simpa using ha)]
  simp only [map_mul, add_mul, Finset.sum_mul]
  congr 1
  all_goals first | ring1 | exact sum_congr rfl fun j _ => by ring

/-- **The factorisation** `Δ_K = det(E C Eᵀ)`. -/
theorem hankelPoly_eq_detQ (q d n K : ℕ) :
    hankelPoly q d n K =
      ((EmatQ q n K).map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin (rr q)) ℚ) * CblQ q d n *
        ((EmatQ q n K).map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin (rr q)) ℚ))ᵀ).det := by
  unfold hankelPoly
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [of_apply, mul_apply, map_apply, transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, sum_idxQ, LX_eq_sum]
  refine sum_congr rfl fun u _ => ?_
  simp_rw [pjet_X_pow', map_sum]
  rw [sum_rangeQ_antidiag q (fun a => cMv q d n (nodeOf n u) a) (fun m hm => cMv_eq_zero hm)
    (fun b b' => MvPolynomial.C (((i : ℕ).choose b : ℚ) * (-((nodeOf n u : ℤ) : ℚ)) ^ ((i : ℕ) - b) *
      (((j : ℕ).choose b' : ℚ) * (-((nodeOf n u : ℤ) : ℚ)) ^ ((j : ℕ) - b'))))]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_idxQ, Finset.sum_eq_single u]
  · refine sum_congr rfl fun b' _ => ?_
    simp only [EmatQ, CblQ, ofLex_toLex, if_true, map_mul, map_pow, map_natCast]
    ring
  · intro v _ hv
    refine sum_eq_zero fun b' _ => ?_
    simp [CblQ, Ne.symm hv]
  · simp

/-- **Double Cauchy–Binet expansion**:
`Δ_K = ∑_{f, g} det E[:, f] · det C[f, g] · det E[:, g]` over strictly monotone `f, g`. -/
theorem hankelPoly_eq_sumQ (q d n K : ℕ) :
    hankelPoly q d n K = ∑ f ∈ smSet K (IdxQ q n), ∑ g ∈ smSet K (IdxQ q n),
      MvPolynomial.C ((EmatQ q n K).submatrix id f).det * ((CblQ q d n).submatrix f g).det *
        MvPolynomial.C ((EmatQ q n K).submatrix id g).det := by
  set Cm : ℚ →+* MvPolynomial (Fin (rr q)) ℚ := MvPolynomial.C
  rw [hankelPoly_eq_detQ, Matrix.mul_assoc, det_mul_eq_sum_strictMono]
  refine sum_congr rfl fun f _ => ?_
  have h1 : (CblQ q d n * ((EmatQ q n K).map Cm)ᵀ).submatrix f id =
      (CblQ q d n).submatrix f id * ((EmatQ q n K).map Cm)ᵀ := by
    ext i j; simp [mul_apply]
  rw [h1, det_mul_eq_sum_strictMono, Finset.mul_sum]
  refine sum_congr rfl fun g _ => ?_
  have h2 : ((EmatQ q n K).map Cm).submatrix id f = ((EmatQ q n K).submatrix id f).map Cm := rfl
  have h3 : ((EmatQ q n K).map Cm)ᵀ.submatrix g id = (((EmatQ q n K).submatrix id g).map Cm)ᵀ :=
    rfl
  have h4 : ((CblQ q d n).submatrix f id).submatrix id g = (CblQ q d n).submatrix f g := rfl
  have h5 : ∀ M : Matrix (Fin K) (Fin K) ℚ, (M.map Cm).det = Cm M.det :=
    fun M => (RingHom.map_det Cm M).symm
  rw [h2, h3, det_transpose, h4, h5, h5]
  ring

end TwoAdicWin
