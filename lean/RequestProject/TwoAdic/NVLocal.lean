import RequestProject.TwoAdic.NVHk

/-!
# II, Lemma 6.2 (local constants at `ℓ = 2n + 1`)

With `V = q + d + 1` and `a < q`:

* `betaC_VB_aff`: at an affected node, `v_ℓ(β_{k,a}) ≥ −(V − a)` (every term of
  `β_{k,a} = ∑_i (−1)^d (i)_d H_k[q−i−a] T_k(i+d)` has `v(H_k[q−i−a]) ≥ −(q−i−a)` and
  `v(T_k(i+d)) = −(i+d+1)`);
* `betaC_last_norm`: at an affected node, `ℓ^{d+2} β_{k,q−1} = ℓ^{d+2} (−1)^d d! H_k[0] T_k(d+1)` is
  an `ℓ`-adic unit (the unit anti-diagonal of II, Theorem 6.4);
* `betaC_VB_partner`, `alphaC_VB_partner`: at the partners (and, for `α`, also at affected nodes)
  `v ≥ −(q − 1 − a)`;
* `betaC_VB_small`, `alphaC_VB_small`: at the nodes `|k| ≤ n/2`, all local constants are integral.
-/

open Finset Polynomial PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ} [hp : Fact ℓ.Prime]

theorem VB_rising (i d : ℕ) : VB ℓ (rising i d) 0 := by
  unfold rising
  have := VB.prod (ℓ := ℓ) (range d) (fun l => (i : ℚ) + l) (fun _ => 0)
    (fun l _ => by simpa using VB_natCast (ℓ := ℓ) (i + l))
  simpa using this

theorem VB_neg_one_pow (d : ℕ) : VB ℓ ((-1 : ℚ) ^ d) 0 := by
  simpa using ((VB_one (ℓ := ℓ)).neg).pow d

theorem betaC_VB_gen (k : ℤ) (a : ℕ) (eH eT : ℕ → ℤ)
    (hH : ∀ i ∈ Icc 1 (q - a), VB ℓ (Hk q n k (q - i - a)) (eH i))
    (hT : ∀ i ∈ Icc 1 (q - a), VB ℓ (Tk k (i + d)) (eT i)) (e : ℤ)
    (he : ∀ i ∈ Icc 1 (q - a), e ≤ eH i + eT i) : VB ℓ (betaC q d n k a) e := by
  unfold betaC
  refine VB.sum _ _ fun i hi => ?_
  have := (((VB_neg_one_pow (ℓ := ℓ) d).mul (VB_rising i d)).mul (hH i hi)).mul (hT i hi)
  exact this.mono (by have := he i hi; omega)

theorem Hyp.Tk_aff (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ aff n) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : M ≤ q + d) : VB ℓ (Tk k M) (-((M + 1 : ℕ) : ℤ)) := by
  rw [mem_aff_iff, mem_nodes_iff, h.R_eq] at hk
  have hn := h.n_eq
  have hl := h.hℓ
  have hb := h.big
  refine VB_of_padicValRat (le_of_eq ?_)
  rw [padicValRat_Tk_pole h.hℓ k M hM1 (by omega) hk.2 (by omega)]

theorem Hyp.Tk_int (h : Hyp q d n ℓ) {k : ℤ} (hk : k.natAbs ≤ n) (M : ℕ) : VB ℓ (Tk k M) 0 :=
  VB_of_padicValRat (padicValRat_Tk_nonneg h.hℓ k M hk)

/-- **II, Lemma 6.2 (i)**: `v_ℓ(β_{k,a}) ≥ −(V − a)` at an affected node. -/
theorem betaC_VB_aff (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ aff n) {a : ℕ} (ha : a < q) :
    VB ℓ (betaC q d n k a) (-(((q + d + 1 : ℕ) : ℤ) - a)) := by
  have hk' := mem_aff_iff.1 hk
  refine betaC_VB_gen k a (fun i => -((q - i - a : ℕ) : ℤ)) (fun i => -((i + d + 1 : ℕ) : ℤ))
    (fun i _ => Hk_VB_partner h hk'.1 (by omega) _) (fun i hi => ?_) _ (fun i hi => ?_)
  · rw [mem_Icc] at hi
    exact h.Tk_aff hk (by omega) (by omega)
  · rw [mem_Icc] at hi
    dsimp only
    omega

/-- **The partner nodes**: `v_ℓ(β_{k,a}) ≥ −(q − 1 − a)`. -/
theorem betaC_VB_partner (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n)
    (hk1 : n / 2 + 1 ≤ k.natAbs) (hk2 : k.natAbs ≤ n) (a : ℕ) :
    VB ℓ (betaC q d n k a) (-((q : ℤ) - 1 - a)) := by
  refine betaC_VB_gen k a (fun i => -((q - i - a : ℕ) : ℤ)) (fun _ => 0)
    (fun i _ => Hk_VB_partner h hk hk1 _) (fun i _ => h.Tk_int hk2 _) _ (fun i hi => ?_)
  rw [mem_Icc] at hi
  dsimp only
  omega

/-- **The nodes `|k| ≤ n/2`**: `β_{k,a}` is `ℓ`-integral. -/
theorem betaC_VB_small (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : k.natAbs ≤ n / 2)
    (a : ℕ) : VB ℓ (betaC q d n k a) 0 :=
  betaC_VB_gen k a (fun _ => 0) (fun _ => 0) (fun i _ => Hk_VB_small h hk hk1 _)
    (fun i _ => h.Tk_int (by omega) _) 0 (fun i _ => by simp)

theorem alphaC_VB_gen (k : ℤ) (j a : ℕ) (eH : ℤ)
    (hH : VB ℓ (Hk q n k (q - (2 * j + 3) - a)) eH) : VB ℓ (alphaC q d n j k a) eH := by
  unfold alphaC
  split_ifs
  · have h1 := ((VB_neg_one_pow (ℓ := ℓ) d).mul (VB_rising (2 * j + 3) d)).mul hH
    have h2 := (VB_natCast (ℓ := ℓ) (2 * j + 3 + d)).mul ((VB_natCast (ℓ := ℓ) 2).pow (2 * j + 3 + d + 1))
    have := h1.mul h2
    simp only [zero_add, mul_zero, add_zero] at this
    simpa using this
  · exact VB_zero _

/-- `v_ℓ(α^{(j)}_{k,a}) ≥ −(q − 1 − a)` at the affected nodes and the partners. -/
theorem alphaC_VB_partner (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n)
    (hk1 : n / 2 + 1 ≤ k.natAbs) (j a : ℕ) :
    VB ℓ (alphaC q d n j k a) (-((q : ℤ) - 1 - a)) := by
  by_cases hq : 2 * j + 3 + a ≤ q
  · exact alphaC_VB_gen k j a _ ((Hk_VB_partner h hk hk1 _).mono (by omega))
  · unfold alphaC; rw [if_neg hq]; exact VB_zero _

/-- `α^{(j)}_{k,a}` is `ℓ`-integral at the nodes `|k| ≤ n/2`. -/
theorem alphaC_VB_small (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : k.natAbs ≤ n / 2)
    (j a : ℕ) : VB ℓ (alphaC q d n j k a) 0 :=
  alphaC_VB_gen k j a _ (Hk_VB_small h hk hk1 _)

theorem padicNorm_pow' (x : ℚ) (m : ℕ) : padicNorm ℓ (x ^ m) = padicNorm ℓ x ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

theorem padicNorm_rising_one (h : Hyp q d n ℓ) : padicNorm ℓ (rising 1 d) = 1 := by
  unfold rising
  rw [padicNorm_prod]
  refine prod_eq_one fun l hl => ?_
  rw [mem_range] at hl
  have : ((1 : ℚ) + l) = ((1 + l : ℕ) : ℚ) := by push_cast; ring
  rw [Nat.cast_one, this, padicNorm.nat_eq_one_iff]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  have := h.big
  omega

/-- **The unit anti-diagonal (II, Lemma 6.2 (i) at `s = q − 1`)**: at an affected node,
`ℓ^{d+2} β_{k,q−1}` is an `ℓ`-adic unit. -/
theorem betaC_last_norm (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ aff n) :
    padicNorm ℓ ((ℓ : ℚ) ^ (d + 2) * betaC q d n k (q - 1)) = 1 := by
  have hq := h.adm.1
  have hk' := mem_aff_iff.1 hk
  unfold betaC
  rw [show q - (q - 1) = 1 by omega, Icc_self, sum_singleton, show q - 1 - (q - 1) = 0 by omega]
  have hT : padicValRat ℓ (Tk k (1 + d)) = -((1 + d + 1 : ℕ) : ℤ) := by
    rw [mem_nodes_iff, h.R_eq] at hk'
    have hn := h.n_eq
    have hl := h.hℓ
    have hb := h.big
    rw [padicValRat_Tk_pole h.hℓ k (1 + d) (by omega) (by omega) hk'.2 (by omega)]
  have hT0 : Tk k (1 + d) ≠ 0 := by
    intro h0; rw [h0, padicValRat.zero] at hT; omega
  have hTn : padicNorm ℓ (Tk k (1 + d)) = (ℓ : ℚ) ^ ((d + 2 : ℕ) : ℤ) := by
    rw [padicNorm.eq_zpow_of_nonzero hT0, hT]
    congr 1; push_cast; ring
  have hsign : padicNorm ℓ ((-1 : ℚ) ^ d) = 1 := by
    rcases neg_one_pow_eq_or ℚ d with e | e <;> rw [e] <;> simp
  rw [padicNorm.mul, padicNorm.mul, padicNorm.mul, padicNorm.mul, hsign, padicNorm_rising_one h,
    Hk_zero_norm h hk'.1 (by omega), hTn, padicNorm_pow', padicNorm.padicNorm_p_of_prime,
    zpow_natCast]
  have : (ℓ : ℚ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  rw [one_mul, one_mul, one_mul, ← mul_pow, inv_mul_cancel₀ this, one_pow]
