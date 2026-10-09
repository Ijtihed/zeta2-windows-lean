import RequestProject.TwoAdic.Defs

/-!
# II, Lemma 6.1 (node structure at `ℓ = 2n + 1`): the harmonic corrections `T_k`

For the auxiliary prime `ℓ = 2n + 1` and `1 ≤ M < ℓ`:

* `padicValRat_Tk_nonneg`: for `|k| ≤ n`, `T_k(M)` is `ℓ`-integral;
* `padicValRat_Tk_pole`: for `n + 1 ≤ |k| ≤ 3n + 1` (in particular for the affected nodes
  `n + 1 ≤ |k| ≤ 3n/2`), `v_ℓ(T_k(M)) = −(M + 1)`: the sum defining `T_k` contains exactly one term
  `ℓ^{−M−1}` with a pole at `ℓ`.

This is the part of II, Lemma 6.1 about `T_k`; it is a first step towards field (iv)
(`nonvanishing`, II Theorem 6.4), which is proved in `NVMain.lean`.
-/

open Finset

namespace TwoAdicWin

/-- A finite sum of positive rationals with nonnegative `ℓ`-adic valuations has nonnegative
valuation. -/
theorem padicValRat_sum_nonneg_of_pos {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} (S : Finset ι)
    (F : ι → ℚ) (hpos : ∀ i ∈ S, 0 < F i) (hv : ∀ i ∈ S, 0 ≤ padicValRat ℓ (F i)) :
    0 ≤ padicValRat ℓ (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [sum_insert ha]
    have ih' := ih (fun i hi => hpos i (mem_insert_of_mem hi)) (fun i hi => hv i (mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ S, F i := sum_nonneg fun i hi => (hpos i (mem_insert_of_mem hi)).le
    have ha' := hpos a (mem_insert_self a S)
    have hne : F a + ∑ i ∈ S, F i ≠ 0 := by positivity
    exact le_trans (le_min (hv a (mem_insert_self a S)) ih') (padicValRat.min_le_padicValRat_add hne)

theorem padicValRat_inv_pow_odd_nonneg {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (m e : ℕ) (hm : ¬ ℓ ∣ m) :
    0 ≤ padicValRat ℓ (((m : ℚ) ^ e)⁻¹) := by
  rw [padicValRat.inv, padicValRat.pow (by exact_mod_cast (show m ≠ 0 by rintro rfl; simp at hm)),
    padicValRat.of_nat]
  have : padicValNat ℓ m = 0 := padicValNat.eq_zero_of_not_dvd hm
  simp [this]

/-- The harmonic sum over `j < k` of `(2j+1)^{−e}` is `ℓ`-integral when `k ≤ n`, `ℓ = 2n+1`. -/
theorem padicValRat_harm_nonneg {n ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ = 2 * n + 1) (k e : ℕ)
    (hk : k ≤ n) :
    0 ≤ padicValRat ℓ (∑ j ∈ range k, (((2 * j + 1 : ℕ) : ℚ) ^ e)⁻¹) := by
  apply padicValRat_sum_nonneg_of_pos
  · intro j _; positivity
  · intro j hj
    apply padicValRat_inv_pow_odd_nonneg
    rintro ⟨c, hc⟩
    rw [mem_range] at hj
    rcases c with _ | _ | c <;> [omega; omega; nlinarith]

/-- The harmonic sum over `j < k` of `(2j+1)^{−e}` has valuation exactly `−e` when
`n + 1 ≤ k ≤ 3n + 1`, `ℓ = 2n + 1`, `e ≥ 1`: only `j = n` contributes a pole. -/
theorem padicValRat_harm_pole {n ℓ : ℕ} [hp : Fact ℓ.Prime] (hℓ : ℓ = 2 * n + 1) (k e : ℕ)
    (he : 1 ≤ e) (hk1 : n + 1 ≤ k) (hk2 : k ≤ 3 * n + 1) :
    padicValRat ℓ (∑ j ∈ range k, (((2 * j + 1 : ℕ) : ℚ) ^ e)⁻¹) = -(e : ℤ) := by
  have hnk : n ∈ range k := mem_range.2 (by omega)
  rw [← add_sum_erase _ _ hnk]
  have hterm : padicValRat ℓ ((((2 * n + 1 : ℕ) : ℚ) ^ e)⁻¹) = -(e : ℤ) := by
    rw [← hℓ, padicValRat.inv, padicValRat.pow (by exact_mod_cast hp.out.ne_zero),
      padicValRat.self hp.out.one_lt]
    simp
  have hrest_v : ∀ j ∈ (range k).erase n,
      padicValRat ℓ ((((2 * n + 1 : ℕ) : ℚ) ^ e)⁻¹) <
        padicValRat ℓ ((((2 * j + 1 : ℕ) : ℚ) ^ e)⁻¹) := by
    intro j hj
    rw [hterm]
    have := padicValRat_inv_pow_odd_nonneg (ℓ := ℓ) (2 * j + 1) e (by
      rintro ⟨c, hc⟩
      rw [mem_erase, mem_range] at hj
      rcases c with _ | _ | _ | c
      · omega
      · omega
      · omega
      · nlinarith)
    omega
  rcases ((range k).erase n).eq_empty_or_nonempty with h | h
  · rw [h, sum_empty, add_zero, hterm]
  · rw [padicValRat.add_eq_of_lt (by positivity) (by positivity)
      (sum_pos (fun j _ => by positivity) h).ne' _, hterm]
    have := padicValRat.lt_sum_of_lt (p := ℓ) (j := n)
      (F := fun j : ℕ => (((2 * j + 1 : ℕ) : ℚ) ^ e)⁻¹) h hrest_v (fun i => by positivity)
    exact this

/-- The negative-side sum `∑_{1 ≤ i ≤ m} (2i−1)^{−e}` is the same harmonic sum. -/
theorem sum_Icc_odd_eq_range (m e : ℕ) :
    ∑ i ∈ Icc 1 m, (((2 * i - 1 : ℕ) : ℚ) ^ e)⁻¹ = ∑ j ∈ range m, (((2 * j + 1 : ℕ) : ℚ) ^ e)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ]
    rfl

theorem padicValRat_const_factor {ℓ M : ℕ} [hp : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hM1 : 1 ≤ M)
    (hM : M < ℓ) (s : ℚ) (hs : s ≠ 0) (σ : ℚ) (hσ : σ = 1 ∨ σ = -1) :
    padicValRat ℓ ((M : ℚ) * σ * 2 ^ (M + 1) * s) = padicValRat ℓ s := by
  have hMv : padicValRat ℓ (M : ℚ) = 0 := by
    have hnd : ¬ ℓ ∣ M := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd hnd]
  have h2v : padicValRat ℓ (2 : ℚ) = 0 := by
    have : padicValRat ℓ ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      simp only [Nat.cast_eq_zero]
      rw [padicValNat.eq_zero_of_not_dvd]
      intro h
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
    exact_mod_cast this
  have hσv : padicValRat ℓ σ = 0 := by
    rcases hσ with rfl | rfl
    · simp
    · rw [padicValRat.neg]; simp
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [padicValRat.mul (by positivity) hs, padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul hM0 hσ0, padicValRat.pow (by norm_num), hMv, h2v, hσv]
  simp

/-- **II, Lemma 6.1 (integral nodes)**: for `ℓ = 2n + 1` prime and `|k| ≤ n`, `T_k(M)` is
`ℓ`-integral (for every `M`). -/
theorem padicValRat_Tk_nonneg {n ℓ : ℕ} [hp : Fact ℓ.Prime] (hℓ : ℓ = 2 * n + 1) (k : ℤ) (M : ℕ)
    (hk : k.natAbs ≤ n) : 0 ≤ padicValRat ℓ (Tk k M) := by
  have h2 : ℓ ≠ 2 := by omega
  have h2v : 0 ≤ padicValRat ℓ (2 : ℚ) := by
    have : padicValRat ℓ ((2 : ℕ) : ℚ) = (padicValNat ℓ 2 : ℤ) := padicValRat.of_nat
    exact_mod_cast this ▸ Int.natCast_nonneg _
  have hMv : 0 ≤ padicValRat ℓ (M : ℚ) := by rw [padicValRat.of_nat]; exact Int.natCast_nonneg _
  have key : ∀ (x y z : ℚ), 0 ≤ padicValRat ℓ x → 0 ≤ padicValRat ℓ y → 0 ≤ padicValRat ℓ z →
      0 ≤ padicValRat ℓ (x * y * z) := by
    intro x y z hx hy hz
    by_cases hx0 : x = 0; · simp [hx0]
    by_cases hy0 : y = 0; · simp [hy0]
    by_cases hz0 : z = 0; · simp [hz0]
    rw [padicValRat.mul (mul_ne_zero hx0 hy0) hz0, padicValRat.mul hx0 hy0]; omega
  have hpow : 0 ≤ padicValRat ℓ ((2 : ℚ) ^ (M + 1)) := by
    rw [padicValRat.pow (by norm_num)]; positivity
  unfold Tk
  split_ifs
  · have := padicValRat_harm_nonneg hℓ k.natAbs (M + 1) hk
    have h := key (-(M : ℚ)) (2 ^ (M + 1)) _ (by rw [padicValRat.neg]; exact hMv) hpow this
    exact h
  · rw [sum_Icc_odd_eq_range]
    have := padicValRat_harm_nonneg hℓ k.natAbs (M + 1) hk
    have hσ : 0 ≤ padicValRat ℓ ((M : ℚ) * (-1) ^ (M + 1)) := by
      by_cases hM0 : (M : ℚ) = 0
      · simp [hM0]
      rw [padicValRat.mul hM0 (pow_ne_zero _ (by norm_num)), padicValRat.pow (by norm_num),
        padicValRat.neg, padicValRat.one]
      simp
    exact key _ _ _ hσ hpow this

/-- **II, Lemma 6.1 (affected nodes)**: for `ℓ = 2n + 1` prime, `1 ≤ M < ℓ` and
`n + 1 ≤ |k| ≤ 3n + 1`, `v_ℓ(T_k(M)) = −(M + 1)`. -/
theorem padicValRat_Tk_pole {n ℓ : ℕ} [hp : Fact ℓ.Prime] (hℓ : ℓ = 2 * n + 1) (k : ℤ) (M : ℕ)
    (hM1 : 1 ≤ M) (hM : M < ℓ) (hk1 : n + 1 ≤ k.natAbs) (hk2 : k.natAbs ≤ 3 * n + 1) :
    padicValRat ℓ (Tk k M) = -((M + 1 : ℕ) : ℤ) := by
  have h2 : ℓ ≠ 2 := by omega
  have hharm := padicValRat_harm_pole hℓ k.natAbs (M + 1) (by omega) hk1 hk2
  have hs : ∑ j ∈ range k.natAbs, (((2 * j + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹ ≠ 0 := by
    intro h0; rw [h0, padicValRat.zero] at hharm; omega
  unfold Tk
  split_ifs
  · have := padicValRat_const_factor h2 hM1 hM _ hs (-1) (Or.inr rfl)
    rw [show -(M : ℚ) * 2 ^ (M + 1) = (M : ℚ) * (-1) * 2 ^ (M + 1) by ring, this, hharm]
  · rw [sum_Icc_odd_eq_range]
    have hσ : ((-1 : ℚ) ^ (M + 1)) = 1 ∨ ((-1 : ℚ) ^ (M + 1)) = -1 := by
      rcases neg_one_pow_eq_or ℚ (M + 1) with h | h <;> simp [h]
    rw [padicValRat_const_factor h2 hM1 hM _ hs _ hσ, hharm]

end TwoAdicWin
