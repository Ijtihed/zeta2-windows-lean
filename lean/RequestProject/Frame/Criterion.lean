import RequestProject.Zeta35.Criterion

/-!
# The multivariable product-formula criterion (P, Lemma 3.1), any prime `p`

For a polynomial `Δ ∈ ℚ[X_0, …, X_{r-1}]` of total degree `≤ K` and a rational point
`x = (a_0/b, …, a_{r-1}/b)` (common denominator `b = ∏_j den(x_j)`, `a_j = b·x_j ∈ ℤ`) with
`Δ(x) ≠ 0` in `ℚ_p`:

  `1 ≤ (∏_{ℓ ∈ S} ℓ^{E_ℓ}) · ‖Δ‖₁ · max(b, |a_j|)^K · ‖Δ(x)‖_p`,

where `S` is a finite set of primes `ℓ ≠ p` and `E_ℓ ≤ max(−v_ℓ(Δ), 0)`, `v_ℓ(Δ)` being the minimum
of `v_ℓ` over the nonzero coefficients (`gaussValMv`), and `‖Δ‖₁` is the sum of the absolute
values of the coefficients (`l1Mv`).  This is the criterion in multiplicative form: taking `log₂`
gives `v_p(Δ(ζ)) log₂ p ≤ log₂‖Δ‖₁ + ∑_{ℓ≠p} (−v_ℓ Δ)⁺ log₂ ℓ + K log₂ max(|a_j|, b)` (the term
`r log₂(K+1)` of W is not needed with the `ℓ¹` norm).  The `p`-part of the content cancels.
-/

open Finset

namespace PadicWin

open MvPolynomial

/-- `‖F‖₁`, the sum of the absolute values of the coefficients. -/
noncomputable def l1Mv {σ : Type*} (F : MvPolynomial σ ℚ) : ℝ :=
  ∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|

/-- The Gauss valuation `v_ℓ(F) = min_m v_ℓ([X^m]F)` over the nonzero coefficients (`⊤` for `F = 0`). -/
noncomputable def gaussValMv {σ : Type*} (ℓ : ℕ) (F : MvPolynomial σ ℚ) : WithTop ℤ :=
  F.support.inf fun m => ((padicValRat ℓ (F.coeff m) : ℤ) : WithTop ℤ)

/-- The common denominator `b = ∏_j den(x_j)`. -/
def commonDen {r : ℕ} (x : Fin r → ℚ) : ℕ := ∏ j, (x j).den

/-- The numerators `a_j = b · x_j = num(x_j) ∏_{i ≠ j} den(x_i)`. -/
def commonNum {r : ℕ} (x : Fin r → ℚ) (j : Fin r) : ℤ :=
  (x j).num * ∏ i ∈ univ.erase j, ((x i).den : ℤ)

/-- The height `max(b, |a_0|, …, |a_{r-1}|)`. -/
def heightMv {r : ℕ} (x : Fin r → ℚ) : ℕ :=
  max (commonDen x) (univ.sup fun j => (commonNum x j).natAbs)

theorem commonDen_pos {r : ℕ} (x : Fin r → ℚ) : 0 < commonDen x :=
  Finset.prod_pos fun j _ => (x j).den_pos

theorem commonNum_cast {r : ℕ} (x : Fin r → ℚ) (j : Fin r) :
    ((commonNum x j : ℤ) : ℚ) = x j * commonDen x := by
  rw [commonNum, commonDen, ← Finset.mul_prod_erase univ (fun i => (x i).den) (mem_univ j)]
  push_cast
  rw [← Rat.mul_den_eq_num (x j)]; ring

theorem one_le_heightMv {r : ℕ} (x : Fin r → ℚ) : 1 ≤ heightMv x :=
  le_max_of_le_left (commonDen_pos x)

theorem natAbs_commonNum_le {r : ℕ} (x : Fin r → ℚ) (j : Fin r) :
    (commonNum x j).natAbs ≤ heightMv x :=
  le_max_of_le_right (Finset.le_sup (f := fun j => (commonNum x j).natAbs) (mem_univ j))

/-- Evaluation commutes with the embedding `ℚ → ℚ_p`. -/
theorem aeval_ratCast_eq {p : ℕ} [Fact p.Prime] {r : ℕ} (x : Fin r → ℚ)
    (Δ : MvPolynomial (Fin r) ℚ) :
    aeval (fun j => ((x j : ℚ) : ℚ_[p])) Δ = ((eval x Δ : ℚ) : ℚ_[p]) := by
  induction Δ using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

/-- `b^K ∏_j x_j^{m_j} = b^{K − |m|} ∏_j a_j^{m_j}` for `|m| ≤ K`. -/
theorem den_pow_mul_monomial {r : ℕ} (x : Fin r → ℚ) (m : Fin r →₀ ℕ) {K : ℕ}
    (hm : ∑ j, m j ≤ K) :
    ((commonDen x : ℚ)) ^ K * ∏ j, x j ^ m j =
      ((commonDen x : ℚ)) ^ (K - ∑ j, m j) * ∏ j, ((commonNum x j : ℤ) : ℚ) ^ m j := by
  have hK : K = (K - ∑ j, m j) + ∑ j, m j := by omega
  conv_lhs => rw [hK, pow_add, ← Finset.prod_pow_eq_pow_sum, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [commonNum_cast, ← mul_pow, mul_comm]

theorem sum_le_totalDegree {r : ℕ} {Δ : MvPolynomial (Fin r) ℚ} {m : Fin r →₀ ℕ}
    (hm : m ∈ Δ.support) : ∑ j, m j ≤ Δ.totalDegree := by
  have h := MvPolynomial.le_totalDegree hm
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h

theorem prod_pow_eq_eval_monomial {r : ℕ} (x : Fin r → ℚ) (m : Fin r →₀ ℕ) :
    ∏ i ∈ m.support, x i ^ m i = ∏ i, x i ^ m i := by
  refine Finset.prod_subset (subset_univ _) fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

/-- The `ℓ`-adic order of an `lcm` (any index type). -/
theorem lcm_factorization_le_gen {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (q m : ℕ)
    (h : ∀ i ∈ s, (f i).factorization q ≤ m) : (s.lcm f).factorization q ≤ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.lcm_insert]
    have h0 : s.lcm f ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; push_neg
      exact fun i hi => hf i (mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := hf a (mem_insert_self a s)
    change (Nat.lcm (f a) (s.lcm f)).factorization q ≤ m
    rw [Nat.factorization_lcm ha0 h0, Finsupp.sup_apply]
    exact sup_le (h a (mem_insert_self a s))
      (ih (fun i hi => hf i (mem_insert_of_mem hi)) (fun i hi => h i (mem_insert_of_mem hi)))

/-- **The multivariable criterion** (P, Lemma 3.1), for any prime `p`. -/
theorem mv_criterion (p : ℕ) [hp : Fact p.Prime] {r : ℕ} (Δ : MvPolynomial (Fin r) ℚ) {K : ℕ}
    (hK : Δ.totalDegree ≤ K) (x : Fin r → ℚ)
    (hne : aeval (fun j => ((x j : ℚ) : ℚ_[p])) Δ ≠ 0) :
    ∃ (S : Finset ℕ) (E : ℕ → ℕ),
      (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ p ∧ ∀ g : ℤ, gaussValMv ℓ Δ = g → (E ℓ : ℤ) ≤ max (-g) 0) ∧
      1 ≤ (∏ ℓ ∈ S, (ℓ : ℝ) ^ E ℓ) * l1Mv Δ * (heightMv x : ℝ) ^ K *
        ‖aeval (fun j => ((x j : ℚ) : ℚ_[p])) Δ‖ := by
  rw [aeval_ratCast_eq] at hne ⊢
  have hev : eval x Δ ≠ 0 := by exact_mod_cast hne
  set b : ℕ := commonDen x with hb_def
  have hb : 0 < b := commonDen_pos x
  set H : ℕ := heightMv x with hH_def
  have hH : 1 ≤ H := one_le_heightMv x
  -- the common denominator of the coefficients
  set D : ℕ := Δ.support.lcm (fun m => (Δ.coeff m).den) with hD_def
  have hD0 : D ≠ 0 := by
    rw [hD_def, Ne, Finset.lcm_eq_zero_iff]; push_neg; exact fun m _ => (Δ.coeff m).den_nz
  have hdvd : ∀ m ∈ Δ.support, (Δ.coeff m).den ∣ D := fun m hm => Finset.dvd_lcm hm
  -- integer coefficients `D · c_m`
  have hint : ∀ m ∈ Δ.support, ∃ z : ℤ, (z : ℚ) = D * Δ.coeff m := by
    intro m hm
    obtain ⟨k, hk⟩ := hdvd m hm
    refine ⟨(Δ.coeff m).num * k, ?_⟩
    push_cast
    rw [hk]; push_cast
    have := Rat.mul_den_eq_num (Δ.coeff m)
    linear_combination (-(k : ℚ)) * this
  choose! z hz using hint
  -- the nonzero integer `N = D b^K Δ(x)`
  set N : ℤ := ∑ m ∈ Δ.support, z m * (b : ℤ) ^ (K - ∑ j, m j) * ∏ j, commonNum x j ^ m j
    with hN_def
  have hNq : (N : ℚ) = D * (b : ℚ) ^ K * eval x Δ := by
    rw [hN_def, eval_eq, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hz m hm, prod_pow_eq_eval_monomial,
      mul_assoc (D : ℚ) ((b : ℚ) ^ K), mul_left_comm ((b : ℚ) ^ K), ← mul_assoc,
      den_pow_mul_monomial x m ((sum_le_totalDegree hm).trans hK)]
    ring
  have hN0 : N ≠ 0 := by
    intro h
    have : (N : ℚ) = 0 := by exact_mod_cast h
    rw [hNq] at this
    exact hev (by
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd (by exact_mod_cast h2) hD0
        · exact absurd h2 (pow_ne_zero _ (by exact_mod_cast hb.ne'))
      · exact h1)
  -- archimedean bound `|N| ≤ D ‖Δ‖₁ H^K`
  have hNabs : |(N : ℝ)| ≤ D * l1Mv Δ * (H : ℝ) ^ K := by
    rw [hN_def, l1Mv, Finset.mul_sum, Finset.sum_mul]
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hzm : ((z m : ℤ) : ℝ) = (D : ℝ) * ((Δ.coeff m : ℚ) : ℝ) := by
      have := congrArg (fun y : ℚ => (y : ℝ)) (hz m hm); push_cast at this; exact this
    have hsum : ∑ j, m j ≤ K := (sum_le_totalDegree hm).trans hK
    have hprod : |∏ j, ((commonNum x j : ℤ) : ℝ) ^ m j| ≤ (H : ℝ) ^ ∑ j, m j := by
      rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun j _ => abs_nonneg _) fun j _ => ?_
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      have h1 := natAbs_commonNum_le x j
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast h1
    have hbpow : |((b : ℤ) : ℝ) ^ (K - ∑ j, m j)| ≤ (H : ℝ) ^ (K - ∑ j, m j) := by
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (le_max_left _ _ : b ≤ max b _)
    rw [hzm, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (D : ℕ))]
    have hHK : (H : ℝ) ^ (K - ∑ j, m j) * (H : ℝ) ^ ∑ j, m j = (H : ℝ) ^ K := by
      rw [← pow_add]; congr 1; omega
    calc (D : ℝ) * |((Δ.coeff m : ℚ) : ℝ)| * |((b : ℤ) : ℝ) ^ (K - ∑ j, m j)| *
          |∏ j, ((commonNum x j : ℤ) : ℝ) ^ m j|
        ≤ (D : ℝ) * |((Δ.coeff m : ℚ) : ℝ)| * (H : ℝ) ^ (K - ∑ j, m j) * (H : ℝ) ^ ∑ j, m j := by
          gcongr
      _ = (D : ℝ) * |((Δ.coeff m : ℚ) : ℝ)| * (H : ℝ) ^ K := by rw [mul_assoc _ _ ((H : ℝ) ^ _), hHK]
  -- `p`-adic size of `N`
  have hNp : ‖((N : ℚ) : ℚ_[p])‖ ≤ ‖((D : ℚ) : ℚ_[p])‖ * ‖((eval x Δ : ℚ) : ℚ_[p])‖ := by
    rw [hNq]; push_cast
    rw [norm_mul, norm_mul, norm_pow]
    have hb1 : ‖(b : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (b : ℤ)
    have hb2 : ‖(b : ℚ_[p])‖ ^ K ≤ 1 := pow_le_one₀ (norm_nonneg _) hb1
    have := mul_le_mul_of_nonneg_left hb2 (norm_nonneg ((D : ℚ_[p])))
    nlinarith [norm_nonneg ((eval x Δ : ℚ) : ℚ_[p]), norm_nonneg ((D : ℚ_[p]))]
  -- `|N| ‖N‖_p ≥ 1`
  have hNone : 1 ≤ |(N : ℝ)| * ‖((N : ℚ) : ℚ_[p])‖ := by
    have hNa : 0 < N.natAbs := Int.natAbs_pos.mpr hN0
    have h1 := Hankel2.inv_le_norm_natCast (p := p) hNa
    have h2 : ‖((N : ℚ) : ℚ_[p])‖ = ‖((N.natAbs : ℕ) : ℚ_[p])‖ := by
      have : ((N.natAbs : ℕ) : ℚ_[p]) = ((|N| : ℤ) : ℚ_[p]) := by
        rw [← Int.natCast_natAbs, Int.cast_natCast]
      rw [this]
      rcases abs_choice N with h | h <;> rw [h] <;> simp
    have h3 : |(N : ℝ)| = (N.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, h3]
    have h4 : (0 : ℝ) < N.natAbs := by exact_mod_cast hNa
    calc (1 : ℝ) = (N.natAbs : ℝ) * (N.natAbs : ℝ)⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h4.le
  -- the ledger
  set d := ordCompl[p] D with hd_def
  have hd0 : d ≠ 0 := (Nat.ordCompl_pos p hD0).ne'
  refine ⟨d.primeFactors, d.factorization, ?_, ?_⟩
  · intro ℓ hℓ
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hℓp' : ℓ ≠ p := by
      rintro rfl
      exact Nat.not_dvd_ordCompl hp.out hD0 (Nat.dvd_of_mem_primeFactors hℓ)
    refine ⟨hℓp, hℓp', fun g hg => ?_⟩
    haveI := Fact.mk hℓp
    have hE : d.factorization ℓ = D.factorization ℓ := by
      rw [hd_def, Nat.factorization_ordCompl, Finsupp.erase_ne hℓp']
    rw [hE]
    have key : ∀ m ∈ Δ.support, ((Δ.coeff m).den.factorization ℓ : ℤ) ≤ max (-g) 0 := by
      intro m hm
      apply Hankel2.den_factorization_le _ ℓ g
      have : gaussValMv ℓ Δ ≤ ((padicValRat ℓ (Δ.coeff m) : ℤ) : WithTop ℤ) :=
        Finset.inf_le hm
      rw [hg] at this; exact_mod_cast this
    have hl : D.factorization ℓ ≤ (max (-g) 0).toNat :=
      lcm_factorization_le_gen Δ.support (fun m => (Δ.coeff m).den)
        (fun m _ => (Δ.coeff m).den_nz) ℓ (max (-g) 0).toNat
        (fun m hm => by have := key m hm; simp only; omega)
    omega
  · have hprod : (∏ ℓ ∈ d.primeFactors, (ℓ : ℝ) ^ d.factorization ℓ) = d := by
      rw [← Nat.support_factorization]
      exact_mod_cast Nat.factorization_prod_pow_eq_self hd0
    rw [hprod, ← Zeta35.mul_norm_p_eq_ordCompl p D hD0]
    have hl1 : 0 ≤ l1Mv Δ := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hDn : ‖((D : ℚ) : ℚ_[p])‖ = ‖(D : ℚ_[p])‖ := by push_cast; rfl
    calc (1 : ℝ) ≤ |(N : ℝ)| * ‖((N : ℚ) : ℚ_[p])‖ := hNone
      _ ≤ (D * l1Mv Δ * (H : ℝ) ^ K) * (‖((D : ℚ) : ℚ_[p])‖ * ‖((eval x Δ : ℚ) : ℚ_[p])‖) :=
          mul_le_mul hNabs hNp (norm_nonneg _) (by positivity)
      _ = _ := by rw [hDn]; ring

end PadicWin
