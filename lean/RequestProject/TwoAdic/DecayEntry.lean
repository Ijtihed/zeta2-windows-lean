import RequestProject.TwoAdic.DecayAnalytic
import RequestProject.TwoAdic.Defs

/-!
# II, Theorem 3.1, the entry bound

At the integration point `s = u + 1/2` the weight factorises (II, proof of Theorem 3.1):
`W(u + 1/2) = 2^{q(3n+1)} (n!)^q C(u + n/2, n)^q G(u)`, `G(u) = ∏_k (1 + 2k + 2u)^{-q}`
(`PW_eq_factor`).  Hence for `B ∈ ℚ[x]` integer-valued on `1/2 + ℕ` with `deg B + qn ≤ D`,
`‖L(B)‖₂ ≤ ‖2^{q(3n+1)} (n!)^q‖₂ · D^d · (D+1)` (`norm_L_le_of_intValued`).
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

/-- `∏_{j<n} (u + j + 1 − n/2) = n! C(u + n/2, n)`. -/
noncomputable def zpoly (n : ℕ) : ℚ_[2][X] :=
  ∏ j ∈ range n, (X + C ((j : ℚ_[2]) + 1 - (n : ℚ_[2]) / 2))

/-- `G(u) = ∏_k (1 + 2k + 2u)^{-q}`. -/
noncomputable def Gw (q n : ℕ) (u : ℚ_[2]) : ℚ_[2] :=
  ∏ k ∈ nodes n, (((1 + 2 * k : ℤ) : ℚ_[2]) + 2 * u)⁻¹ ^ q

/-- `c₀ = 2^{q(3n+1)} (n!)^q`. -/
noncomputable def c0 (q n : ℕ) : ℚ_[2] := 2 ^ (q * (3 * n + 1)) * ((n.factorial : ℚ_[2])) ^ q

/-- The polynomial `Q(u) = B(u + 1/2) (C(u + n/2, n))^q` (without `c₀`). -/
noncomputable def Qpoly (q n : ℕ) (B : ℚ[X]) : ℚ_[2][X] :=
  (B.map (algebraMap ℚ ℚ_[2])).comp (X + C (1 / 2)) * (C ((n.factorial : ℚ_[2])⁻¹) * zpoly n) ^ q

theorem adm_Gw (q n : ℕ) : Adm (Gw q n) := by
  unfold Gw
  exact Adm.prod _ fun k _ => (Adm.phi (1 + 2 * k) ⟨k, by ring⟩).pow q

theorem natDegree_zpoly_le (n : ℕ) : (zpoly n).natDegree ≤ n := by
  unfold zpoly
  refine (natDegree_prod_le _ _).trans ?_
  have h : ∀ j ∈ range n,
      (X + C ((j : ℚ_[2]) + 1 - (n : ℚ_[2]) / 2)).natDegree ≤ (fun _ => 1) j :=
    fun j _ => (natDegree_X_add_C _).le
  refine (Finset.sum_le_sum h).trans ?_
  simp

theorem natDegree_Qpoly_le (q n : ℕ) (B : ℚ[X]) :
    (Qpoly q n B).natDegree ≤ B.natDegree + q * n := by
  unfold Qpoly
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · rw [natDegree_comp, natDegree_map, natDegree_X_add_C, mul_one]
  · exact natDegree_pow_le.trans
      (Nat.mul_le_mul_left q ((natDegree_C_mul_le _ _).trans (natDegree_zpoly_le n)))

/-- **The factorisation of II, Theorem 3.1**: `B(s) W(s) = c₀ Q(s − 1/2) G(s − 1/2)` for all `s`. -/
theorem PW_eq_factor (q : ℕ) {n : ℕ} (hn : Even n) (B : ℚ[X]) (s : ℚ_[2]) :
    aeval s B * W q n s = (C (c0 q n) * Qpoly q n B).eval (s - 1 / 2) * Gw q n (s - 1 / 2) := by
  have hfac : (n.factorial : ℚ_[2]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hB : (B.map (algebraMap ℚ ℚ_[2])).eval s = aeval s B := by
    rw [aeval_def, eval_map]
  have hz : (zpoly n).eval (s - 1 / 2) = ∏ j ∈ range n, (s - ((zeroPt n j : ℚ) : ℚ_[2])) := by
    unfold zpoly
    rw [eval_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [eval_add, eval_X, eval_C, zeroPt]
    push_cast; ring
  have hden : (∏ k ∈ nodes n, (s + (k : ℚ_[2])) ^ q)⁻¹ =
      (2 : ℚ_[2]) ^ (q * (3 * n + 1)) * Gw q n (s - 1 / 2) := by
    rw [← Finset.prod_inv_distrib, Gw]
    have h1 : ∀ k ∈ nodes n, ((s + (k : ℚ_[2])) ^ q)⁻¹ =
        (2 : ℚ_[2]) ^ q * (((1 + 2 * k : ℤ) : ℚ_[2]) + 2 * (s - 1 / 2))⁻¹ ^ q := by
      intro k _
      have e : ((1 + 2 * k : ℤ) : ℚ_[2]) + 2 * (s - 1 / 2) = 2 * (s + k) := by push_cast; ring
      rw [e, mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow,
        one_mul, inv_pow]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const,
      card_nodes_of_even hn, ← pow_mul]
  rw [W, div_eq_mul_inv, hden, eval_mul, eval_C, Qpoly, eval_mul, eval_comp, eval_add, eval_X,
    eval_C, sub_add_cancel, hB, eval_pow, eval_mul, eval_C, hz, c0]
  rw [mul_pow, ← Finset.prod_pow, inv_pow]
  field_simp

/-- `n! ∣ ∏_{j<n} (u + j + 1 − n/2)` at natural `u` (for even `n`). -/
theorem zpoly_eval_nat {n : ℕ} (hn : Even n) (u : ℕ) :
    ∃ m : ℤ, (C ((n.factorial : ℚ_[2])⁻¹) * zpoly n).eval (u : ℚ_[2]) = m := by
  obtain ⟨h, rfl⟩ := hn
  have hfac : ((h + h).factorial : ℚ_[2]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [eval_mul, eval_C, zpoly, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  by_cases hu : h ≤ u + 1
  · -- all factors are natural numbers `u + 1 − h + j`
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_ascFactorial (u + 1 - h) (h + h)
    refine ⟨c, ?_⟩
    have hprod : ∏ j ∈ range (h + h), ((u : ℚ_[2]) + ((j : ℚ_[2]) + 1 - ((h + h : ℕ) : ℚ_[2]) / 2)) =
        (((u + 1 - h).ascFactorial (h + h) : ℕ) : ℚ_[2]) := by
      rw [Nat.ascFactorial_eq_prod_range]
      push_cast
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Nat.cast_sub hu]; push_cast; ring
    rw [hprod, hc]
    push_cast
    field_simp
  · -- one factor vanishes
    refine ⟨0, ?_⟩
    have hmem : h - 1 - u ∈ range (h + h) := by rw [Finset.mem_range]; omega
    rw [Finset.prod_eq_zero hmem, mul_zero, Int.cast_zero]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

theorem eval_map_half_nat (B : ℚ[X]) (u : ℕ) :
    ((B.map (algebraMap ℚ ℚ_[2])).comp (X + C (1 / 2))).eval (u : ℚ_[2]) =
      ((B.eval ((u : ℚ) + 1 / 2) : ℚ) : ℚ_[2]) := by
  rw [eval_comp, eval_add, eval_X, eval_C, eval_map]
  have : (u : ℚ_[2]) + 1 / 2 = algebraMap ℚ ℚ_[2] ((u : ℚ) + 1 / 2) := by
    simp
  rw [this, eval₂_at_apply]
  rfl

/-- **The entry bound of II, Theorem 3.1**: for `B` integer-valued on `1/2 + ℕ` and
`deg B + qn ≤ D`, `‖L(B)‖₂ ≤ ‖c₀‖₂ D^d (D+1)`. -/
theorem norm_L_le_of_intValued (q d : ℕ) {n : ℕ} (hn : Even n) (B : ℚ[X])
    (hB : ∀ u : ℕ, ∃ m : ℤ, B.eval ((u : ℚ) + 1 / 2) = m) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : B.natDegree + q * n ≤ D) :
    ‖L q d n B‖ ≤ ‖c0 q n‖ * (D : ℝ) ^ d * ((D : ℝ) + 1) := by
  set Q' := Qpoly q n B
  have hQ'deg : Q'.natDegree ≤ D := (natDegree_Qpoly_le q n B).trans hD
  have hQ'int : ∀ x : ℕ, ∃ m : ℤ, Q'.eval (x : ℚ_[2]) = m := by
    intro x
    obtain ⟨m1, hm1⟩ := hB x
    obtain ⟨m2, hm2⟩ := zpoly_eval_nat hn x
    refine ⟨m1 * m2 ^ q, ?_⟩
    simp only [Q', Qpoly, eval_mul, eval_pow]
    rw [eval_map_half_nat, hm1, ← eval_mul, hm2]
    push_cast; ring
  have hQ'p : Prof (polyW 1 D) fun y => Q'.eval y := prof_of_intValued hQ'deg hQ'int
  set Q := C (c0 q n) * Q'
  have hQdeg : Q.natDegree ≤ D := (natDegree_C_mul_le _ _).trans hQ'deg
  have hQp : Prof (polyW ‖c0 q n‖ D) fun y => Q.eval y := by
    intro x j
    have h := hQ'p.const_mul (c0 q n) x j
    have e : (fun y => Q.eval y) = fun y => c0 q n * Q'.eval y := by
      funext y; simp only [Q, eval_mul, eval_C]
    rw [e]
    refine h.trans (le_of_eq ?_)
    by_cases hj : j ≤ D <;> simp [polyW, hj]
  obtain ⟨I, hI, hIn⟩ := exists_hasVolkenborn_iteratedDeriv Q (D := D) hD1 hQdeg (norm_nonneg _)
    hQp (adm_Gw q n) (1 / 2) d
  have hfun : (fun t => iteratedDeriv d (fun s => aeval s B * W q n s) (t + 1 / 2)) =
      fun t => iteratedDeriv d (fun s => Q.eval (s - 1 / 2) * Gw q n (s - 1 / 2)) (t + 1 / 2) := by
    funext t; congr 1; funext s; exact PW_eq_factor q hn B s
  unfold L
  rw [hfun, hI.volkInt_eq]
  exact hIn

end TwoAdicWin
