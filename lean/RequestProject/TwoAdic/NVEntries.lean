import RequestProject.TwoAdic.NVBasis

/-!
# II, Theorem 6.4: the weighted Gram entries

For the dual basis `E` of `NVBasis` and the weights `ϖ_x = V/2 − j₀` (`wt`, `V = q + d + 1`), the
scaled Gram entries `ℓ^{ϖ_x + ϖ_y} L_X(E_x E_y)`, `L_X = b + ∑_j X_j a_j`, satisfy:

* `aL_entry`: the coefficient of every `X_j`, `ℓ^{ϖ_x+ϖ_y} a_j(E_x E_y)`, is divisible by `ℓ`;
* `bL_entry`: the constant part `ℓ^{ϖ_x+ϖ_y} b(E_x E_y)` is congruent modulo `ℓ` to `Nm x y`, the
  contribution of the affected nodes, which is block diagonal (one block per affected node `k`),
  each block `[ℓ^{V−a−b} β_{k,a+b}]_{a,b<q}` being anti-triangular (`β_{k,s}` only for `s < q`);
* `Nm_int`: `Nm` is `ℓ`-integral, and `padicNorm_det_Nm`: `det Nm` is an `ℓ`-adic unit (the
  anti-diagonal entries `ℓ^{d+2} β_{k,q−1}` are units, `betaC_last_norm`).

The partners contribute `ω ≥ d + 2` (`term_big`, with `jet_partner`), the nodes `|k| ≤ n/2`
contribute `ω ≥ d + 3 − q ≥ 2` (`term_small`).
-/

open Polynomial Finset PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ}

/-- The weight `ϖ_x = V/2 − j₀`. -/
def wt (q d : ℕ) {n : ℕ} (x : HIdx q n) : ℕ := (q + d + 1) / 2 - (x.2 : ℕ)

theorem Pjet_mul' (F G : ℚ[X]) (k : ℤ) (a : ℕ) :
    Pjet (F * G) k a = ∑ ab ∈ antidiagonal a, Pjet F k ab.1 * Pjet G k ab.2 :=
  Hankel2.W3.jet_mul F G _ a

theorem Hyp.V_even (h : Hyp q d n ℓ) : (q + d + 1) / 2 * 2 = q + d + 1 := by
  obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩, _, _⟩ := h.adm
  omega

theorem scaled_bL (N : ℕ) (F G : ℚ[X]) :
    (ℓ : ℚ) ^ N * bL q d n (F * G) = ∑ k ∈ nodes n, ∑ a ∈ range q, ∑ ab ∈ antidiagonal a,
      (ℓ : ℚ) ^ N * betaC q d n k a * Pjet F k ab.1 * Pjet G k ab.2 := by
  unfold bL
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Pjet_mul', mul_sum, mul_sum]
  exact sum_congr rfl fun ab _ => by ring

theorem scaled_aL (N j : ℕ) (F G : ℚ[X]) :
    (ℓ : ℚ) ^ N * aL q d n j (F * G) = ∑ k ∈ nodes n, ∑ a ∈ range q, ∑ ab ∈ antidiagonal a,
      (ℓ : ℚ) ^ N * alphaC q d n j k a * Pjet F k ab.1 * Pjet G k ab.2 := by
  unfold aL
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Pjet_mul', mul_sum, mul_sum]
  exact sum_congr rfl fun ab _ => by ring

variable [Fact ℓ.Prime]

section Terms

variable (h : Hyp q d n ℓ) (E : HIdx q n → ℚ[X])
  (hE1 : ∀ x (i : ↥(aff n)) j (hj : j < q), Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
  (hE2 : ∀ x m, padicNorm ℓ ((E x).coeff m) ≤ 1)
include h hE1 hE2

/-- Terms at the affected nodes and the partners: `ω ≥ d + 2 ≥ 1`. -/
theorem term_big (x y : HIdx q n) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs)
    {a : ℕ} (ha : a < q) {ab : ℕ × ℕ} (hab : ab ∈ antidiagonal a) {c : ℚ}
    (hc : VB ℓ c (-((q : ℤ) - 1 - a))) :
    VB ℓ ((ℓ : ℚ) ^ (wt q d x + wt q d y) * c * Pjet (E x) k ab.1 * Pjet (E y) k ab.2) 1 := by
  rw [mem_antidiagonal] at hab
  have h1 := jet_partner h E hE1 hE2 x hk hk1 (b := ab.1) (by omega)
  have h2 := jet_partner h E hE1 hE2 y hk hk1 (b := ab.2) (by omega)
  have := (((VB_ell_pow (ℓ := ℓ) (wt q d x + wt q d y)).mul hc).mul h1).mul h2
  refine this.mono ?_
  have hx := x.2.isLt
  have hy := y.2.isLt
  have hqd := h.adm.2.2.2.1
  unfold wt
  omega

omit hE1 in
/-- Terms at the nodes `|k| ≤ n/2`: `ω ≥ d + 3 − q ≥ 2`. -/
theorem term_small (x y : HIdx q n) (k : ℤ) (ab : ℕ × ℕ) {c : ℚ} (hc : VB ℓ c 0) :
    VB ℓ ((ℓ : ℚ) ^ (wt q d x + wt q d y) * c * Pjet (E x) k ab.1 * Pjet (E y) k ab.2) 1 := by
  have := (((VB_ell_pow (ℓ := ℓ) (wt q d x + wt q d y)).mul hc).mul
    (jet_int E hE2 x k ab.1)).mul (jet_int E hE2 y k ab.2)
  refine this.mono ?_
  have hx := x.2.isLt
  have hqd := h.adm.2.2.2.1
  unfold wt
  omega

/-- **The `X_j`-coefficients are divisible by `ℓ`.** -/
theorem aL_entry (x y : HIdx q n) (j : ℕ) :
    VB ℓ ((ℓ : ℚ) ^ (wt q d x + wt q d y) * aL q d n j (E x * E y)) 1 := by
  rw [scaled_aL]
  refine VB.sum _ _ fun k hk => VB.sum _ _ fun a ha => VB.sum _ _ fun ab hab => ?_
  by_cases hk1 : n / 2 + 1 ≤ k.natAbs
  · exact term_big h E hE1 hE2 x y hk hk1 (mem_range.1 ha) hab (alphaC_VB_partner h hk hk1 j a)
  · exact term_small h E hE2 x y k ab (alphaC_VB_small h hk (by omega) j a)

end Terms

/-- The leading (affected-node) part of the scaled constant Gram matrix. -/
noncomputable def Nm (ℓ q d n : ℕ) (x y : HIdx q n) : ℚ :=
  if (x.1 : ℤ) = y.1 ∧ (x.2 : ℕ) + y.2 < q then
    (ℓ : ℚ) ^ (wt q d x + wt q d y) * betaC q d n x.1 ((x.2 : ℕ) + y.2) else 0

theorem jet_aff_eq (E : HIdx q n → ℚ[X])
    (hE1 : ∀ x (i : ↥(aff n)) j (hj : j < q), Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
    (x : HIdx q n) {k : ℤ} (hk : k ∈ aff n) {b : ℕ} (hb : b < q) :
    Pjet (E x) k b = if (x.1 : ℤ) = k ∧ (x.2 : ℕ) = b then 1 else 0 := by
  rw [show k = ((⟨k, hk⟩ : ↥(aff n)) : ℤ) from rfl, hE1 x ⟨k, hk⟩ b hb]
  obtain ⟨⟨k', hk'⟩, ⟨b', hb'⟩⟩ := x
  congr 1
  apply propext
  simp only [Sigma.mk.injEq, Subtype.mk.injEq, heq_eq_eq, Fin.mk.injEq]

omit [Fact ℓ.Prime] in
theorem aff_part (E : HIdx q n → ℚ[X])
    (hE1 : ∀ x (i : ↥(aff n)) j (hj : j < q), Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
    (x y : HIdx q n) :
    ∑ k ∈ aff n, ∑ a ∈ range q, ∑ ab ∈ antidiagonal a,
      (ℓ : ℚ) ^ (wt q d x + wt q d y) * betaC q d n k a * Pjet (E x) k ab.1 * Pjet (E y) k ab.2 =
    Nm ℓ q d n x y := by
  have hterm : ∀ k ∈ aff n, ∀ a ∈ range q, ∀ ab ∈ antidiagonal a,
      (ℓ : ℚ) ^ (wt q d x + wt q d y) * betaC q d n k a * Pjet (E x) k ab.1 * Pjet (E y) k ab.2 =
      if ab = ((x.2 : ℕ), (y.2 : ℕ)) then
        (if (x.1 : ℤ) = k ∧ (y.1 : ℤ) = k then (ℓ : ℚ) ^ (wt q d x + wt q d y) * betaC q d n k a
          else 0) else 0 := by
    intro k hk a ha ab hab
    rw [mem_antidiagonal] at hab
    rw [mem_range] at ha
    rw [jet_aff_eq E hE1 x hk (b := ab.1) (by omega), jet_aff_eq E hE1 y hk (b := ab.2) (by omega)]
    obtain ⟨b1, b2⟩ := ab
    simp only [Prod.mk.injEq]
    by_cases hA : (x.1 : ℤ) = k ∧ (x.2 : ℕ) = b1 <;> by_cases hB : (y.1 : ℤ) = k ∧ (y.2 : ℕ) = b2
    · rw [if_pos hA, if_pos hB, if_pos (show b1 = (x.2 : ℕ) ∧ b2 = (y.2 : ℕ) from ⟨hA.2.symm, hB.2.symm⟩),
        if_pos (show (x.1 : ℤ) = k ∧ (y.1 : ℤ) = k from ⟨hA.1, hB.1⟩), mul_one, mul_one]
    · rw [if_neg hB, mul_zero]; symm
      rw [ite_eq_right_iff]; intro h1; rw [ite_eq_right_iff]; intro h2
      exact absurd ⟨h2.2, h1.2.symm⟩ hB
    · rw [if_neg hA, mul_zero, zero_mul]; symm
      rw [ite_eq_right_iff]; intro h1; rw [ite_eq_right_iff]; intro h2
      exact absurd ⟨h2.1, h1.1.symm⟩ hA
    · rw [if_neg hA, mul_zero, zero_mul]; symm
      rw [ite_eq_right_iff]; intro h1; rw [ite_eq_right_iff]; intro h2
      exact absurd ⟨h2.1, h1.1.symm⟩ hA
  rw [sum_congr rfl fun k hk => sum_congr rfl fun a ha => sum_congr rfl fun ab hab =>
    hterm k hk a ha ab hab]
  simp only [sum_ite_eq', mem_antidiagonal, sum_ite_eq, mem_range]
  rw [sum_eq_single (x.1 : ℤ)]
  · unfold Nm
    by_cases h1 : (x.1 : ℤ) = y.1
    · by_cases h2 : (x.2 : ℕ) + y.2 < q
      · rw [if_pos h2, if_pos ⟨rfl, h1.symm⟩, if_pos ⟨h1, h2⟩]
      · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
    · have hn : ¬ ((x.1 : ℤ) = y.1 ∧ (x.2 : ℕ) + y.2 < q) := fun hc => h1 hc.1
      have hn2 : ¬ ((x.1 : ℤ) = x.1 ∧ (y.1 : ℤ) = x.1) := fun hc => h1 hc.2.symm
      rw [if_neg hn, if_neg hn2, ite_self]
  · intro k _ hk
    split_ifs with h1 h2
    · exact absurd h2.1.symm hk
    · rfl
    · rfl
  · intro hx; exact absurd x.1.2 hx

variable (h : Hyp q d n ℓ) (E : HIdx q n → ℚ[X])
  (hE1 : ∀ x (i : ↥(aff n)) j (hj : j < q), Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
  (hE2 : ∀ x m, padicNorm ℓ ((E x).coeff m) ≤ 1)
include h hE1 hE2

/-- **The constant part is congruent to the affected-node blocks modulo `ℓ`.** -/
theorem bL_entry (x y : HIdx q n) :
    VB ℓ ((ℓ : ℚ) ^ (wt q d x + wt q d y) * bL q d n (E x * E y) - Nm ℓ q d n x y) 1 := by
  rw [scaled_bL, ← sum_filter_add_sum_filter_not (nodes n) (fun k => n + 1 ≤ k.natAbs)]
  rw [show (nodes n).filter (fun k => n + 1 ≤ k.natAbs) = aff n from rfl, aff_part E hE1,
    add_sub_cancel_left]
  refine VB.sum _ _ fun k hk => VB.sum _ _ fun a ha => VB.sum _ _ fun ab hab => ?_
  rw [mem_filter] at hk
  by_cases hk1 : n / 2 + 1 ≤ k.natAbs
  · exact term_big h E hE1 hE2 x y hk.1 hk1 (mem_range.1 ha) hab
      (betaC_VB_partner h hk.1 hk1 (by omega) a)
  · exact term_small h E hE2 x y k ab (betaC_VB_small h hk.1 (by omega) a)

omit hE1 hE2 in
theorem Nm_int (x y : HIdx q n) : VB ℓ (Nm ℓ q d n x y) 0 := by
  unfold Nm
  split_ifs with hc
  · have h1 := betaC_VB_aff h x.1.2 (a := (x.2 : ℕ) + y.2) hc.2
    have := (VB_ell_pow (ℓ := ℓ) (wt q d x + wt q d y)).mul h1
    refine this.mono ?_
    have := h.V_even
    have hx := x.2.isLt
    have hy := y.2.isLt
    have hqd := h.adm.2.2.2.1
    unfold wt
    omega
  · exact VB_zero _

end TwoAdicWin.Dom
