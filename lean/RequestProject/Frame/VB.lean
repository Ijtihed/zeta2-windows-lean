import Mathlib

/-!
# Valuation bookkeeping for the strict-dominance argument (II, Thm 6.4)

`VB ℓ x e` means `v_ℓ(x) ≥ e`, i.e. `|x|_ℓ ≤ ℓ^{−e}` (with `x = 0` allowed).

* the ultrametric rules (`VB.add`, `VB.mul`, `VB.sum`, `VB.prod`, …);
* `domSub ℓ σ`: the subring of `ℚ[X_σ]` of polynomials whose constant coefficient is `ℓ`-integral and
  whose other coefficients are divisible by `ℓ` (`v_ℓ([X^m] P) ≥ [m ≠ 0]`);
* **`det_mem_domSub`**: a determinant of a matrix with entries in `domSub` lies in `domSub`, and its
  constant coefficient is the determinant of the constant coefficients (`coeff_zero_det`).  This is
  the "congruence identically in `X`" of II, Thm 6.4: if the scaled Gram matrix is congruent
  modulo `ℓ` to a matrix without `X`, the determinant has the same constant coefficient modulo `ℓ`
  and all its other coefficients are divisible by `ℓ`;
* `det_congr_mod`: integral matrices congruent modulo `ℓ` have determinants congruent modulo `ℓ`;
* `det_antiHankel`: an anti-triangular Hankel block `[g(a+b)]_{a,b<q}` (`g(s) = 0` for `s ≥ q`) has
  determinant `±g(q−1)^q`.
-/

open Finset

namespace PadicWin

/-- `v_ℓ(x) ≥ e`. -/
def VB (ℓ : ℕ) (x : ℚ) (e : ℤ) : Prop := padicNorm ℓ x ≤ (ℓ : ℚ) ^ (-e)

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem one_lt_ell : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt

theorem ell_pos : (0 : ℚ) < ℓ := by linarith [one_lt_ell (ℓ := ℓ)]

theorem VB.mono {x : ℚ} {e e' : ℤ} (h : VB ℓ x e) (he : e' ≤ e) : VB ℓ x e' :=
  h.trans (zpow_le_zpow_right₀ (one_lt_ell (ℓ := ℓ)).le (by omega))

theorem VB_zero (e : ℤ) : VB ℓ 0 e := by
  simp only [VB, padicNorm.zero]; exact (zpow_pos ell_pos _).le

theorem VB.mul {x y : ℚ} {e f : ℤ} (hx : VB ℓ x e) (hy : VB ℓ y f) : VB ℓ (x * y) (e + f) := by
  unfold VB at *
  rw [padicNorm.mul, neg_add, zpow_add₀ (ell_pos (ℓ := ℓ)).ne']
  exact mul_le_mul hx hy (padicNorm.nonneg _) (zpow_pos ell_pos _).le

omit hℓ in
theorem VB.neg {x : ℚ} {e : ℤ} (h : VB ℓ x e) : VB ℓ (-x) e := by
  unfold VB at *; rwa [padicNorm.neg]

omit hℓ in
theorem VB_neg_iff {x : ℚ} {e : ℤ} : VB ℓ (-x) e ↔ VB ℓ x e := by
  unfold VB; rw [padicNorm.neg]

theorem VB.add {x y : ℚ} {e : ℤ} (hx : VB ℓ x e) (hy : VB ℓ y e) : VB ℓ (x + y) e :=
  padicNorm.nonarchimedean.trans (max_le hx hy)

theorem VB.sub {x y : ℚ} {e : ℤ} (hx : VB ℓ x e) (hy : VB ℓ y e) : VB ℓ (x - y) e := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem VB.sum {α : Type*} (s : Finset α) (f : α → ℚ) {e : ℤ} (h : ∀ i ∈ s, VB ℓ (f i) e) :
    VB ℓ (∑ i ∈ s, f i) e :=
  padicNorm.sum_le' h (zpow_pos ell_pos _).le

omit hℓ in
theorem VB_one : VB ℓ 1 0 := by simp [VB]

theorem VB_natCast (m : ℕ) : VB ℓ (m : ℚ) 0 := by
  unfold VB; simp only [neg_zero, zpow_zero]; exact padicNorm.of_nat m

theorem VB_intCast (m : ℤ) : VB ℓ (m : ℚ) 0 := by
  unfold VB; simp only [neg_zero, zpow_zero]; exact padicNorm.of_int m

theorem VB.prod {α : Type*} (s : Finset α) (f : α → ℚ) (e : α → ℤ) (h : ∀ i ∈ s, VB ℓ (f i) (e i)) :
    VB ℓ (∏ i ∈ s, f i) (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (VB_one (ℓ := ℓ))
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem VB.pow {x : ℚ} {e : ℤ} (h : VB ℓ x e) (m : ℕ) : VB ℓ (x ^ m) (m * e) := by
  induction m with
  | zero => simpa using (VB_one (ℓ := ℓ))
  | succ m ih =>
    rw [pow_succ]
    have := ih.mul h
    rwa [show ((m + 1 : ℕ) : ℤ) * e = m * e + e by push_cast; ring]

theorem VB_ell : VB ℓ (ℓ : ℚ) 1 := by
  unfold VB
  rw [padicNorm.padicNorm_p_of_prime]; simp

theorem VB_ell_pow (m : ℕ) : VB ℓ ((ℓ : ℚ) ^ m) m := by
  simpa using (VB_ell (ℓ := ℓ)).pow m

theorem VB_of_padicValRat {x : ℚ} {e : ℤ} (h : e ≤ padicValRat ℓ x) : VB ℓ x e := by
  by_cases hx : x = 0
  · subst hx; exact VB_zero e
  · unfold VB
    rw [padicNorm.eq_zpow_of_nonzero hx]
    exact zpow_le_zpow_right₀ (one_lt_ell (ℓ := ℓ)).le (by omega)

theorem padicValRat_of_VB {x : ℚ} {e : ℤ} (hx : x ≠ 0) (h : VB ℓ x e) : e ≤ padicValRat ℓ x := by
  unfold VB at h
  rw [padicNorm.eq_zpow_of_nonzero hx] at h
  have := (zpow_le_zpow_iff_right₀ (one_lt_ell (ℓ := ℓ))).1 h
  omega

/-! ### The subring `domSub` -/

open Classical in
variable (ℓ) in
/-- Polynomials with `ℓ`-integral constant coefficient and all other coefficients divisible by
`ℓ`. -/
def domSub (σ : Type*) : Subring (MvPolynomial σ ℚ) where
  carrier := {P | ∀ m, VB ℓ (P.coeff m) (if m = 0 then 0 else 1)}
  mul_mem' {P Q} hP hQ m := by
    classical
    rw [MvPolynomial.coeff_mul]
    refine VB.sum _ _ fun x hx => ?_
    have h := (hP x.1).mul (hQ x.2)
    refine h.mono ?_
    rw [mem_antidiagonal] at hx
    split_ifs with h1 h2 h3 h3 <;> try omega
    all_goals (subst_vars; simp_all)
  one_mem' m := by
    rw [MvPolynomial.coeff_one]
    by_cases h1 : m = 0
    · subst h1; simp only [if_true]; exact VB_one
    · rw [if_neg (Ne.symm h1)]; exact VB_zero _
  add_mem' {P Q} hP hQ m := by
    rw [MvPolynomial.coeff_add]; exact (hP m).add (hQ m)
  zero_mem' m := by rw [MvPolynomial.coeff_zero]; exact VB_zero _
  neg_mem' {P} hP m := by rw [MvPolynomial.coeff_neg]; exact (hP m).neg

open Classical in
theorem mem_domSub {σ : Type*} {P : MvPolynomial σ ℚ} :
    P ∈ domSub ℓ σ ↔ ∀ m, VB ℓ (P.coeff m) (if m = 0 then 0 else 1) := Iff.rfl

theorem C_mem_domSub {σ : Type*} {a : ℚ} (ha : VB ℓ a 0) :
    (MvPolynomial.C a : MvPolynomial σ ℚ) ∈ domSub ℓ σ := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  by_cases h1 : m = 0
  · subst h1; simp only [if_true]; exact ha
  · rw [if_neg (Ne.symm h1)]; exact VB_zero _

theorem mem_domSub_of_VB_one {σ : Type*} {P : MvPolynomial σ ℚ} (h : ∀ m, VB ℓ (P.coeff m) 1) :
    P ∈ domSub ℓ σ := fun m => (h m).mono (by classical split_ifs <;> omega)

theorem det_mem_subring {R : Type*} [CommRing R] (T : Subring R) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (hM : ∀ i j, M i j ∈ T) : M.det ∈ T := by
  rw [Matrix.det_apply]
  refine T.sum_mem fun σ _ => ?_
  refine Subring.zsmul_mem _ (T.prod_mem fun i _ => hM _ _) _

/-- **The determinant stays in `domSub`.** -/
theorem det_mem_domSub {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℚ)) (hM : ∀ i j, M i j ∈ domSub ℓ σ) :
    M.det ∈ domSub ℓ σ := det_mem_subring _ M hM

/-- The constant coefficient of a determinant is the determinant of the constant coefficients. -/
theorem coeff_zero_det {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℚ)) :
    M.det.coeff 0 = (M.map fun P => P.coeff 0).det := by
  rw [← MvPolynomial.constantCoeff_eq, RingHom.map_det]
  congr 1

/-- **Congruent integral matrices have congruent determinants.** -/
theorem det_congr_mod {ι : Type*} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℚ)
    (hN : ∀ i j, VB ℓ (N i j) 0) (hMN : ∀ i j, VB ℓ (M i j - N i j) 1) :
    VB ℓ (M.det - N.det) 1 := by
  classical
  -- `T ↦ det(N + T (M − N))` in one variable
  set P : Matrix ι ι (MvPolynomial (Fin 1) ℚ) := fun i j =>
    MvPolynomial.C (N i j) + MvPolynomial.C (M i j - N i j) * MvPolynomial.X 0 with hP
  have hmem : ∀ i j, P i j ∈ domSub ℓ (Fin 1) := by
    intro i j
    refine (domSub ℓ _).add_mem (C_mem_domSub (hN i j)) ?_
    refine mem_domSub_of_VB_one fun m => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    split_ifs
    · simpa using hMN i j
    · simpa using (VB_zero (ℓ := ℓ) 1)
  have hdet := det_mem_domSub P hmem
  have hev : MvPolynomial.eval (fun _ => (1 : ℚ)) P.det = M.det := by
    rw [RingHom.map_det]; congr 1; ext i j; simp [hP]
  have h0 : P.det.coeff 0 = N.det := by
    rw [coeff_zero_det]; congr 1; ext i j
    simp [hP, MvPolynomial.coeff_mul_X']
  -- `det P(1) − det P(0) = ∑_{m ≠ 0} coeff_m`
  have hsum : MvPolynomial.eval (fun _ => (1 : ℚ)) P.det =
      ∑ m ∈ P.det.support, P.det.coeff m := by
    conv_lhs => rw [MvPolynomial.as_sum P.det]
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    simp [MvPolynomial.eval_monomial]
  rw [← hev, ← h0, hsum]
  by_cases h0m : (0 : Fin 1 →₀ ℕ) ∈ P.det.support
  · rw [← add_sum_erase _ _ h0m, add_sub_cancel_left]
    refine VB.sum _ _ fun m hm => ?_
    have := hdet m
    rwa [if_neg (ne_of_mem_erase hm)] at this
  · have : P.det.coeff 0 = 0 := by simpa using h0m
    rw [this, sub_zero]
    refine VB.sum _ _ fun m hm => ?_
    have h1 := hdet m
    have hm0 : m ≠ 0 := fun h => h0m (h ▸ hm)
    rwa [if_neg hm0] at h1

/-- **Anti-triangular Hankel blocks**: if `g s = 0` for `s ≥ q`, then
`det[g(a+b)]_{a,b<q} = ±g(q−1)^q`. -/
theorem det_antiHankel {R : Type*} [CommRing R] (q : ℕ) (g : ℕ → R)
    (hg : ∀ s, q ≤ s → g s = 0) :
    (Matrix.of fun a b : Fin q => g ((a : ℕ) + b)).det =
      (((Fin.revPerm : Equiv.Perm (Fin q)).sign : ℤ) : R) * g (q - 1) ^ q := by
  have h := Matrix.det_permute' (σ := (Fin.revPerm : Equiv.Perm (Fin q)))
    (M := Matrix.of fun a b : Fin q => g ((a : ℕ) + b))
  have htri : ((Matrix.of fun a b : Fin q => g ((a : ℕ) + b)).submatrix id Fin.revPerm).det =
      g (q - 1) ^ q := by
    rw [Matrix.det_of_upperTriangular]
    · simp only [Matrix.submatrix_apply, id, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev]
      rw [Finset.prod_congr rfl fun i _ => by
        rw [show (i : ℕ) + (q - (i + 1)) = q - 1 by have := i.isLt; omega]]
      simp
    · intro i j hij
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev]
      apply hg
      have : (j : ℕ) < i := hij
      have := i.isLt
      omega
  rw [htri] at h
  have hs : (((Fin.revPerm : Equiv.Perm (Fin q)).sign : ℤ) : R) *
      (((Fin.revPerm : Equiv.Perm (Fin q)).sign : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Fin.revPerm : Equiv.Perm (Fin q)).sign with h1 | h1 <;>
      simp [h1]
  rw [h, ← mul_assoc, hs, one_mul]

end PadicWin
