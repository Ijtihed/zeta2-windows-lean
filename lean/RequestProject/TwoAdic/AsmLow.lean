import RequestProject.TwoAdic.AsmSmall
import RequestProject.Zeta7.Hankel2.PrimeSums

/-!
# The primes `ℓ ≤ n/20`: small and middle primes together

* `low_prime_bound`: for every odd prime `ℓ`,
  `T⁺_ℓ ≤ q² n (n+1)/(ℓ − 1) + (d + 2) q n + q² ℓ/4 + [ℓ² ≤ 4n] W(n)`, with
  `W(n) = ((2q + d + 1) q n + (3n + 1) q²/4) ⌊log₂ 4n⌋` (`small_bound` for `ℓ² ≤ 4n`, `middle_bound`
  otherwise);
* **`low_sum`**: for a set `S` of odd primes,
  `∑_{ℓ ∈ S, ℓ ≤ n/20} T⁺_ℓ ln ℓ ≤ q² n (n+1) M(n/20) + (d+2) q n θ(n/20) + (q²/4)(n/20) θ(n/20)
    + W(n) · 2 ln 4 · √n`, with Mertens' sum `M = mertensOddSum`.
-/

open Finset Chebyshev

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin

variable {q d n ℓ : ℕ}

/-- The error term of the small primes. -/
noncomputable def Wsm (q d n : ℕ) : ℝ :=
  ((2 * q + d + 1) * q * n + (3 * n + 1) * (q : ℝ) ^ 2 / 4) * Nat.log 2 (4 * n)

theorem low_prime_bound [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) :
    (TPplus q d n ℓ (q * n) : ℝ) ≤
      (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) + (d + 2) * q * n + (q : ℝ) ^ 2 * ℓ / 4 +
        (if ℓ ^ 2 ≤ 4 * n then Wsm q d n else 0) := by
  have hℓ2 : 2 ≤ ℓ := hp.out.two_le
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  have h0 : (0 : ℝ) ≤ (d + 2) * q * n + (q : ℝ) ^ 2 * ℓ / 4 := by positivity
  split_ifs with hsm
  · have h := small_bound (q := q) (d := d) hn hn1 h2
    have hL1 : Lell n ℓ ≤ Nat.log 2 (4 * n) :=
      (Nat.log_anti_left (by norm_num) hℓ2).trans (Nat.log_mono_right (by omega))
    have hL2 : Nat.log ℓ (3 * n + 1) ≤ Nat.log 2 (4 * n) :=
      (Nat.log_anti_left (by norm_num) hℓ2).trans (Nat.log_mono_right (by omega))
    have hL1' : (Lell n ℓ : ℝ) ≤ Nat.log 2 (4 * n) := by exact_mod_cast hL1
    have hL2' : (Nat.log ℓ (3 * n + 1) : ℝ) ≤ Nat.log 2 (4 * n) := by exact_mod_cast hL2
    have hW : (2 * q + d + 1) * q * n * (Lell n ℓ : ℝ) +
        Nat.log ℓ (3 * n + 1) * (3 * n + 1) * (q : ℝ) ^ 2 / 4 ≤ Wsm q d n := by
      unfold Wsm
      have a1 : (0 : ℝ) ≤ (2 * q + d + 1) * q * n := by positivity
      have a2 : (0 : ℝ) ≤ (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL1' a1, mul_le_mul_of_nonneg_left hL2' a2]
    linarith
  · push_neg at hsm
    have h := middle_bound (q := q) (d := d) hn hn1 h2 hsm
    have hl : (q : ℝ) ^ 2 * n * (n + 1) / ℓ ≤ (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    linarith

theorem natLog_two_le (m : ℕ) (hm : m ≠ 0) : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 hm
  have h' : ((2 : ℝ)) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

/-- **The primes `ℓ ≤ n/20`.** -/
theorem low_sum (hn : Even n) (hn1 : 1 ≤ n) (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) :
    ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ n / 20), (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
      (q : ℝ) ^ 2 * n * (n + 1) * mertensOddSum (n / 20) + (d + 2) * q * n * θ (n / 20) +
        (q : ℝ) ^ 2 / 4 * (n / 20) * θ (n / 20) + Wsm q d n * (2 * Real.log 4 * Real.sqrt n) := by
  set A := S.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ n / 20)
  have hA : ∀ ℓ ∈ A, ℓ.Prime ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ n / 20 := fun ℓ hℓ => by
    simp only [A, mem_filter] at hℓ; exact ⟨(hS ℓ hℓ.1).1, (hS ℓ hℓ.1).2, hℓ.2⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  -- termwise
  have hterm : ∀ ℓ ∈ A, (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
      (q : ℝ) ^ 2 * n * (n + 1) * (Real.log ℓ / ((ℓ : ℝ) - 1)) + (d + 2) * q * n * Real.log ℓ +
        (q : ℝ) ^ 2 / 4 * (n / 20) * Real.log ℓ +
          Wsm q d n * (if ℓ ^ 2 ≤ 4 * n then Real.log ℓ else 0) := by
    intro ℓ hℓ
    obtain ⟨hp, h2, hle⟩ := hA ℓ hℓ
    haveI : Fact ℓ.Prime := ⟨hp⟩
    have h := low_prime_bound (q := q) (d := d) hn hn1 h2
    have hlog : 0 ≤ Real.log ℓ := Real.log_natCast_nonneg ℓ
    have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hp.one_lt
    have e := mul_le_mul_of_nonneg_right h hlog
    have hq4 : (q : ℝ) ^ 2 * ℓ / 4 * Real.log ℓ ≤ (q : ℝ) ^ 2 / 4 * (n / 20) * Real.log ℓ := by
      have : (q : ℝ) ^ 2 * ℓ / 4 = (q : ℝ) ^ 2 / 4 * ℓ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hlog
    have e2 : (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) * Real.log ℓ =
        (q : ℝ) ^ 2 * n * (n + 1) * (Real.log ℓ / ((ℓ : ℝ) - 1)) := by ring
    split_ifs at e ⊢ with hsm
    · nlinarith
    · nlinarith
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_add_distrib, ← mul_sum]
  -- Mertens
  have hM : ∑ ℓ ∈ A, Real.log ℓ / ((ℓ : ℝ) - 1) ≤ mertensOddSum (n / 20) := by
    unfold mertensOddSum
    refine sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) (fun ℓ hℓ _ => ?_)
    · obtain ⟨hp, h2, hle⟩ := hA ℓ hℓ
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨?_, Nat.le_floor hle⟩, hp⟩
      have := hp.two_le
      omega
    · simp only [mem_filter, mem_Icc] at hℓ
      have : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.1.1
      exact div_nonneg (Real.log_natCast_nonneg ℓ) (by linarith)
  -- θ
  have hθ1 : ∑ ℓ ∈ A, Real.log ℓ ≤ θ (n / 20) := by
    have := Hankel2.sum_log_le_theta_sub A (x := 0) (y := n / 20) (by positivity)
      (fun p hp => ⟨(hA p hp).1, by exact_mod_cast (hA p hp).1.pos, (hA p hp).2.2⟩)
    simpa [theta] using this
  have hθ2 : ∑ ℓ ∈ A, (if ℓ ^ 2 ≤ 4 * n then Real.log ℓ else 0) ≤ 2 * Real.log 4 * Real.sqrt n := by
    rw [← sum_filter]
    have hsq : ∀ p ∈ A.filter (fun ℓ => ℓ ^ 2 ≤ 4 * n), (p : ℝ) ≤ 2 * Real.sqrt n := by
      intro p hp
      simp only [mem_filter] at hp
      have h1 : ((p : ℝ)) ^ 2 ≤ 4 * n := by exact_mod_cast hp.2
      have : (p : ℝ) ≤ Real.sqrt (4 * n) := Real.le_sqrt_of_sq_le h1
      rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    have := Hankel2.sum_log_le_theta_sub (A.filter (fun ℓ => ℓ ^ 2 ≤ 4 * n)) (x := 0)
      (y := 2 * Real.sqrt n) (by positivity)
      (fun p hp => ⟨(hA p (mem_filter.1 hp).1).1,
        by exact_mod_cast (hA p (mem_filter.1 hp).1).1.pos, hsq p hp⟩)
    have h0 : θ 0 = 0 := by simp [theta]
    rw [h0, sub_zero] at this
    refine this.trans ?_
    have := theta_le_log4_mul_x (x := 2 * Real.sqrt n) (by positivity)
    linarith
  have hq1 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * n * (n + 1) := by positivity
  have hq2 : (0 : ℝ) ≤ (d + 2) * q * n := by positivity
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 2 / 4 * (n / 20) := by positivity
  have hW : 0 ≤ Wsm q d n := by unfold Wsm; positivity
  nlinarith [mul_le_mul_of_nonneg_left hM hq1, mul_le_mul_of_nonneg_left hθ1 hq2,
    mul_le_mul_of_nonneg_left hθ1 hq3, mul_le_mul_of_nonneg_left hθ2 hW]

end TwoAdicWin.Asm
