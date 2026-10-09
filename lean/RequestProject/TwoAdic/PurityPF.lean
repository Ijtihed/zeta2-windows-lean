import RequestProject.TwoAdic.Defs
import RequestProject.Frame.Derivs
import RequestProject.Zeta7.Hankel2.PurityInt

/-!
# Purity, step 1: partial fractions of `P W` and the local constants (II, Lemma 2.2)

* `PW_eq_Gsum`: on the non-poles, `P(s) W(s) = ∑_k ∑_{i=1}^{q} r_{k,i} (s+k)^{−i}` with
  `r_{k,i} = r_{k,i}(P · N)` the partial-fraction coefficients of `P N / ∏_k (t+k)^q`;
* `resCoef_mul_numPoly`: `r_{k,i}(P N) = ∑_{a+b = q−i} P_a(k) H_k[b]` with
  `H_k[b] = [u^b] u^q W(−k+u)` (`Hk`);
* `Tk_eq_neg_HS`: the corrections `T_k(M)` of II agree with `−M HS(k, M+1)` of the ζ₂(7) library
  (`Hankel2.HS`), for every `k ∈ ℤ`.
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

/-- The partial-fraction coefficients `r_{k,i}(P N)`. -/
noncomputable def rco (q n : ℕ) (P : ℚ[X]) (k : ℤ) (i : ℕ) : ℚ :=
  PadicWin.PF.resCoef (nodes n) q (P * numPoly q n) k i

theorem aeval_numPoly (q n : ℕ) (s : ℚ_[2]) :
    aeval s (numPoly q n) = ∏ j ∈ range n, (s - ((zeroPt n j : ℚ) : ℚ_[2])) ^ q := by
  simp [numPoly, map_prod]

theorem natDegree_numPoly_le (q n : ℕ) : (numPoly q n).natDegree ≤ q * n := by
  unfold numPoly
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ range n, ((X - C (zeroPt n j)) ^ q).natDegree ≤ ∑ _j ∈ range n, q := by
        refine Finset.sum_le_sum fun j _ => natDegree_pow_le.trans ?_
        rw [natDegree_X_sub_C, mul_one]
    _ = q * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

theorem aeval_Dki (S : Finset ℤ) (q : ℕ) (k : ℤ) (i : ℕ) (s : ℚ_[2]) :
    aeval s (PadicWin.PF.Dki S q k i) =
      (s + k) ^ (q - i) * ∏ k' ∈ S.erase k, (s + k') ^ q := by
  simp [PadicWin.PF.Dki, map_prod]

/-- **Partial fractions of `P W`** on the non-poles (for `deg(P N) ≤ q|𝒦| − 1`). -/
theorem PW_eq_Gsum (q n : ℕ) (P : ℚ[X])
    (hP : (P * numPoly q n).natDegree + 1 ≤ q * (nodes n).card) {s : ℚ_[2]}
    (hs : s ∈ PadicWin.nonPolesS 2 (nodes n)) :
    aeval s P * W q n s = PadicWin.Gsum (nodes n) (rco q n P) q 0 s := by
  rw [PadicWin.Gsum_zero]
  have hpf := congrArg (aeval s) (PadicWin.PF.eq_sum (nodes n) q (P * numPoly q n) hP)
  rw [map_mul, aeval_numPoly, map_sum] at hpf
  have hden : ∏ k ∈ nodes n, (s + (k : ℚ_[2])) ^ q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hs k hk)
  rw [W, ← mul_div_assoc, hpf, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.mp hi
  rw [map_mul, aeval_C, aeval_Dki, ← Finset.mul_prod_erase _ _ hk]
  have hk0 : s + (k : ℚ_[2]) ≠ 0 := hs k hk
  have herase : ∏ k' ∈ (nodes n).erase k, (s + (k' : ℚ_[2])) ^ q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' hk' => pow_ne_zero _ (hs k' (Finset.mem_of_mem_erase hk'))
  have hq : (s + (k : ℚ_[2])) ^ q = (s + k) ^ (q - i) * (s + k) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hq]
  simp only [eq_ratCast, rco]
  have hki : (s + (k : ℚ_[2])) ^ i ≠ 0 := pow_ne_zero _ hk0
  have hkqi : (s + (k : ℚ_[2])) ^ (q - i) ≠ 0 := pow_ne_zero _ hk0
  field_simp

/-- **The local constants**: `r_{k,i}(P N) = ∑_{a + b = q − i} P_a(k) H_k[b]`. -/
theorem resCoef_mul_numPoly (q n : ℕ) (P : ℚ[X]) (k : ℤ) {i : ℕ} (hiq : i ≤ q) :
    rco q n P k i = ∑ a ∈ range (q + 1 - i), Pjet P k a * Hk q n k (q - i - a) := by
  rw [rco, PadicWin.PF.resCoef_eq_coeff _ _ _ _ hiq, taylor_mul, RingHom.map_mul, mul_assoc,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h5 : q + 1 - i = q - i + 1 := by omega
  rw [h5]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, taylor_coeff, Pjet,
    PadicWin.PF.Pjet, Hk]

/-- **`T_k(M) = −M HS(k, M+1)`** for every `k ∈ ℤ`. -/
theorem Tk_eq_neg_HS (k : ℤ) (M : ℕ) : Tk k M = -(M : ℚ) * HS k (M + 1) := by
  unfold Tk HS W3.Fam3.hsSum
  rcases lt_trichotomy k 0 with hk | hk | hk
  · -- `k < 0`
    rw [if_neg (by omega), if_neg (by omega), Finset.filter_true]
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, k = -(N : ℤ) := ⟨(-k).toNat, by omega⟩
    have hN : (-(N : ℤ)).natAbs = N := by simp
    rw [hN]
    have hre : ∑ l ∈ Finset.Icc (-(N : ℤ) + 1) 0, (2 / (2 * (l : ℚ) - 1)) ^ (M + 1) =
        ∑ i ∈ Finset.Icc 1 N, (-1) ^ (M + 1) * 2 ^ (M + 1) * (((2 * i - 1 : ℕ) : ℚ) ^ (M + 1))⁻¹ := by
      symm
      refine Finset.sum_nbij' (fun i => 1 - (i : ℤ)) (fun l => (1 - l).toNat) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
      · intro l hl; simp only [Finset.mem_Icc] at hl ⊢; omega
      · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
      · intro l hl; simp only [Finset.mem_Icc] at hl; dsimp only; omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        have h2i : ((2 * i - 1 : ℕ) : ℚ) = 2 * (i : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [h2i]
        have hne : (2 * (i : ℚ) - 1) ≠ 0 := by
          have : (1 : ℚ) ≤ i := by exact_mod_cast hi.1
          linarith
        have e : (2 * (((1 - (i : ℤ) : ℤ)) : ℚ) - 1) = -(2 * (i : ℚ) - 1) := by push_cast; ring
        rw [e, div_neg, neg_pow (2 / (2 * (i : ℚ) - 1)), div_pow, div_eq_mul_inv]
        ring
    rw [hre, neg_mul_neg]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · subst hk; simp
  · -- `k > 0`
    rw [if_pos hk.le, if_pos hk, Finset.filter_true]
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, k = (N : ℤ) := ⟨k.toNat, by omega⟩
    have hN : ((N : ℤ)).natAbs = N := by simp
    rw [hN]
    have hre : ∑ l ∈ Finset.Icc (1 : ℤ) N, (2 / (2 * (l : ℚ) - 1)) ^ (M + 1) =
        ∑ j ∈ range N, 2 ^ (M + 1) * (((2 * j + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹ := by
      symm
      refine Finset.sum_nbij' (fun j => (j : ℤ) + 1) (fun l => (l - 1).toNat) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
      · intro l hl; simp only [Finset.mem_Icc] at hl; simp only [Finset.mem_range]; omega
      · intro j hj; simp
      · intro l hl; simp only [Finset.mem_Icc] at hl; dsimp only; omega
      · intro j _
        push_cast
        have hne : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
        rw [show (2 * ((j : ℚ) + 1) - 1) = 2 * (j : ℚ) + 1 by ring, div_pow, div_eq_mul_inv]
    rw [hre, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end TwoAdicWin
