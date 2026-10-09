import RequestProject.Zeta7.Hankel2.TpPlus

/-!
# Towards Theorem 8.1: the prime ranges (paper §8.4, steps (i)–(iii))

Explicit (non-asymptotic) forms of the per-range bounds used in the assembly of Theorem 8.1:

* `sum_TPplus_large_eq`: primes `p > 4n` contribute nothing (`max(T_p,0) = 0`);
* `sum_TPplus_le_A1`: for any set of odd primes, by Lemma 8.3 (A1),
  `∑ max(T_p,0) ln p ≤ ∑ (K(6n+4−K)/(p−1) + 12 K L_p + 113 n) ln p`;
* `sum_TPplus_le_prop85`: for odd primes with `p² > 6n`, by Proposition 8.5,
  `∑ max(T_p,0) ln p ≤ ∑ (K(6n+4−K)/p + 5K + 25p) ln p`.

The remaining steps of the paper's assembly (the Mertens/PNT asymptotics of these prime sums, the
circle model for `εn < p ≤ 4.5n`, and the certificate of Appendix B) are carried out in
`PrimeSums.lean`, `CircleModel.lean`–`CircleCount.lean` and `Thm81Reduction.lean`.
-/

open Finset

namespace Hankel2.Fam3

variable {n K : ℕ}

/-- Proposition 8.5 for `max(T_p, 0)` (`p² > 6n`, `K ≤ 6n+4`). -/
theorem prop85_plus {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2)
    (hK6 : K ≤ 6 * n + 4) :
    (TPplus p n K : ℝ) ≤ (K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p := by
  have hb : 0 ≤ (K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p := by
    have : (K : ℝ) ≤ 6 * n + 4 := by exact_mod_cast hK6
    have : 0 ≤ (K : ℝ) * (6 * n + 4 - K) / p := by
      apply div_nonneg _ (by positivity); nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    positivity
  unfold TPplus
  induction h : TP p n K with
  | bot => simpa using hb
  | coe t =>
    have := prop85 hp2 h6 K t h
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simpa using hb
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]; simpa using this

/-- Primes `p > 4n` do not contribute to `∑ max(T_p, 0) ln p`. -/
theorem sum_TPplus_large_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ S, (TPplus p n K : ℝ) * Real.log p =
      ∑ p ∈ S.filter (fun p => p ≤ 4 * n), (TPplus p n K : ℝ) * Real.log p := by
  rw [sum_filter]
  refine sum_congr rfl fun p hp => ?_
  split_ifs with h
  · rfl
  · haveI : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [TPplus_eq_zero_of_large (hS p hp).2 (by omega) K]; simp

/-- **Range (i)** (paper §8.4): by Lemma 8.3 (A1), for every finite set of odd primes,
`∑ max(T_p,0) ln p ≤ ∑ (K(6n+4−K)/(p−1) + 12 K L_p + 113 n) ln p`. -/
theorem sum_TPplus_le_A1 (hK6 : K ≤ 6 * n + 4) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ S, (TPplus p n K : ℝ) * Real.log p ≤
      ∑ p ∈ S, ((K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n) * Real.log p := by
  refine sum_le_sum fun p hp => ?_
  haveI : Fact p.Prime := ⟨(hS p hp).1⟩
  exact mul_le_mul_of_nonneg_right (lemmaA1_plus (hS p hp).2 n K hK6)
    (Real.log_nonneg (by exact_mod_cast (hS p hp).1.one_lt.le))

/-- **Range (ii)** (paper §8.4): by Proposition 8.5, for every finite set of odd primes with
`p² > 6n`, `∑ max(T_p,0) ln p ≤ ∑ (K(6n+4−K)/p + 5K + 25p) ln p`. -/
theorem sum_TPplus_le_prop85 (hK6 : K ≤ 6 * n + 4) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ 6 * n < p ^ 2) :
    ∑ p ∈ S, (TPplus p n K : ℝ) * Real.log p ≤
      ∑ p ∈ S, ((K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p) * Real.log p := by
  refine sum_le_sum fun p hp => ?_
  haveI : Fact p.Prime := ⟨(hS p hp).1⟩
  exact mul_le_mul_of_nonneg_right (prop85_plus (hS p hp).2.1 (hS p hp).2.2 hK6)
    (Real.log_nonneg (by exact_mod_cast (hS p hp).1.one_lt.le))

/-- **Range (iii), per prime** (paper eq. (dual)): for an odd prime with `p² > 6n`, every `λ` and
every family `ψ_c ≥ V_c(S) − λ S`, `max(T_p, 0) ≤ max(λ K + ∑_c ψ_c, 0)`. -/
theorem TPplus_le_dual {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (lam : ℝ)
    (ψ : ℕ → ℝ) (hψ : ∀ c < p, ∀ S : ℕ, ∀ v : ℤ, Vc p n c S = v → (v : ℝ) - lam * S ≤ ψ c) :
    (TPplus p n K : ℝ) ≤ max (lam * K + ∑ c ∈ range p, ψ c) 0 := by
  unfold TPplus
  induction h : TP p n K with
  | bot => simp
  | coe t =>
    have := TP_le_dual hp2 h6 K lam ψ hψ t h
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simp
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]
      simp only [WithBot.unbotD_coe]
      exact le_max_of_le_left this

end Hankel2.Fam3
