import Mathlib

/-!
# The discrete logarithmic energy of two intervals (the closed form of `F`)

For `n = 2h ≥ 2` consider the integer set `𝒪 = [h+1, 3h] ∪ [−3h, −(h+1)]` (the outer thirds of the
nodes `|k| ≤ 3n/2`; two blocks of `n` consecutive integers).

* `lf j = ln j!`; Stirling-type bounds `lf_lower`, `lf_upper`;
* `F2 N = ∑_{j ≤ N} ln j!` and `abs_F2_sub_le`: `|F2 N − (N²/2 ln N − 3N²/4)| ≤ 5N(1 + ln N)`;
* `self_sum_eq`: `∑_{a,b<n} ln|a − b| = 2 F2(n−1)`;
* `cross_sum_eq`: `∑_{a,b<n} ln(n + 2 + a + b) = F2(3n) − 2F2(2n) + F2(n)`;
* **`outer_energy_ge`**: `∑_{k,m ∈ 𝒪} ln|k − m| ≥ 4n² ln n + (9 ln 3 − 8 ln 2 − 6) n² − 300 n (1 + ln n)`.

This is the discrete form of `⟨1_𝒪, 𝓛1_𝒪⟩ = 9 ln 3 − 8 ln 2 − 6`.
-/

open Finset

namespace PadicWin.LogEnergy

/-- `ln j!`. -/
noncomputable def lf (j : ℕ) : ℝ := Real.log (j.factorial)

theorem lf_succ (j : ℕ) : lf (j + 1) = lf j + Real.log (j + 1) := by
  unfold lf
  rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  push_cast; ring

theorem lf_lower (j : ℕ) : (j : ℝ) * Real.log j - j ≤ lf j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [lf]
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have h := Real.pow_div_factorial_le_exp (j : ℝ) hj'.le j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h2 : Real.log ((j : ℝ) ^ j / j.factorial) ≤ j := by
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_exp] at this
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow] at h2
  unfold lf
  linarith

theorem lf_upper (j : ℕ) : lf j ≤ (j : ℝ) * Real.log j - j + Real.log j + 2 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [lf]
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hS := Stirling.stirlingSeq'_antitone (Nat.zero_le (j - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hj] at hS
  rw [Stirling.stirlingSeq_one] at hS
  unfold Stirling.stirlingSeq at hS
  have hpos : 0 < √(2 * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j := by positivity
  rw [div_le_iff₀ hpos] at hS
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h1 := Real.log_le_log hf hS
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_div hj'.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp] at h1
  have hsq2 : Real.log (√(2 * (j : ℝ))) = (Real.log 2 + Real.log j) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hj'.ne']
  have hsq3 : Real.log (√(2 : ℝ)) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hsq : 0 ≤ Real.log (√2) := Real.log_nonneg (by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
  rw [hsq2, hsq3] at h1
  have hL : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  unfold lf
  linarith

/-- `F2 N = ∑_{j ≤ N} ln j!`. -/
noncomputable def F2 (N : ℕ) : ℝ := ∑ j ∈ range (N + 1), lf j

theorem F2_succ (N : ℕ) : F2 (N + 1) = F2 N + lf (N + 1) := by
  unfold F2; rw [sum_range_succ]

/-- `G(x) = x²/2 ln x − x²/4`, a primitive of `x ln x`. -/
noncomputable def Gp (x : ℝ) : ℝ := x ^ 2 / 2 * Real.log x - x ^ 2 / 4

theorem integral_mul_log {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (1 : ℝ)..N, x * Real.log x = Gp N - Gp 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
    (Real.continuous_mul_log.intervalIntegrable _ _)
  rw [Set.uIcc_of_le hN'] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have h := (((hasDerivAt_pow 2 x).div_const 2).mul (Real.hasDerivAt_log hx0)).sub
    ((hasDerivAt_pow 2 x).div_const 4)
  convert h using 1
  field_simp
  ring

theorem monotoneOn_mul_log : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  exact mul_le_mul hxy (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx) (by linarith)

theorem sum_mul_log_ge {N : ℕ} (hN : 1 ≤ N) :
    Gp N - Gp 1 ≤ ∑ j ∈ range (N + 1), (j : ℝ) * Real.log j := by
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc 1 (1 + ((N - 1 : ℕ) : ℝ))) :=
    monotoneOn_mul_log.mono fun x hx => hx.1
  have h := hmono.integral_le_sum
  have e : (1 : ℝ) + ((N - 1 : ℕ) : ℝ) = N := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [e, integral_mul_log hN] at h
  refine h.trans ?_
  have e2 : N + 1 = (N - 1) + 2 := by omega
  rw [e2, Finset.sum_range_succ' (fun j : ℕ => (j : ℝ) * Real.log j) (N - 1 + 1),
    Finset.sum_range_succ' (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ)) (N - 1)]
  simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero, zero_add, Nat.cast_one,
    Real.log_one]
  refine le_of_eq (sum_congr rfl fun i _ => ?_)
  push_cast; ring_nf

theorem sum_mul_log_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ range (N + 1), (j : ℝ) * Real.log j ≤ Gp N - Gp 1 + N * Real.log N := by
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc 1 (1 + ((N - 1 : ℕ) : ℝ))) :=
    monotoneOn_mul_log.mono fun x hx => hx.1
  have h := hmono.sum_le_integral
  have e : (1 : ℝ) + ((N - 1 : ℕ) : ℝ) = N := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [e, integral_mul_log hN] at h
  have e2 : N + 1 = (N - 1) + 1 + 1 := by omega
  rw [e2, sum_range_succ, sum_range_succ']
  simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero]
  have e3 : (((N - 1 + 1 : ℕ)) : ℝ) = N := by rw [Nat.sub_add_cancel hN]
  rw [e3]
  have e4 : ∑ i ∈ range (N - 1), ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ) =
      ∑ i ∈ range (N - 1), (1 + ((i : ℕ) : ℝ)) * Real.log (1 + ((i : ℕ) : ℝ)) := by
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [e4]
  linarith

theorem sum_id_real (N : ℕ) : ∑ j ∈ range (N + 1), (j : ℝ) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_log_le (N : ℕ) : ∑ j ∈ range (N + 1), (Real.log j + 2) ≤ (N + 1) * (Real.log N + 2) := by
  have : ∀ j ∈ range (N + 1), Real.log j + 2 ≤ Real.log N + 2 := by
    intro j hj
    rw [mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [Nat.cast_zero, Real.log_zero]
      have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      linarith
    · have : Real.log j ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast hj0) (by exact_mod_cast (by omega : j ≤ N))
      linarith
  refine (sum_le_sum this).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- **`|F2 N − (N²/2 ln N − 3N²/4)| ≤ 5N(1 + ln N)`** for `N ≥ 1`. -/
theorem F2_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ 2 / 2 * Real.log N - 3 * (N : ℝ) ^ 2 / 4 - 5 * N * (1 + Real.log N) ≤ F2 N := by
  have h1 := sum_mul_log_ge hN
  have h2 : ∑ j ∈ range (N + 1), ((j : ℝ) * Real.log j - j) ≤ F2 N :=
    sum_le_sum fun j _ => lf_lower j
  rw [sum_sub_distrib, sum_id_real] at h2
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Gp at h1
  simp only [one_pow, Real.log_one, mul_zero, zero_sub] at h1
  nlinarith

theorem F2_le {N : ℕ} (hN : 1 ≤ N) :
    F2 N ≤ (N : ℝ) ^ 2 / 2 * Real.log N - 3 * (N : ℝ) ^ 2 / 4 + 5 * N * (1 + Real.log N) := by
  have h1 := sum_mul_log_le hN
  have h2 : F2 N ≤ ∑ j ∈ range (N + 1), (((j : ℝ) * Real.log j - j) + (Real.log j + 2)) :=
    sum_le_sum fun j _ => by linarith [lf_upper j]
  rw [sum_add_distrib, sum_sub_distrib, sum_id_real] at h2
  have h3 := sum_log_le N
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Gp at h1
  simp only [one_pow, Real.log_one, mul_zero, zero_sub] at h1
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) hL]

/-! ### The self and cross sums -/

theorem sum_log_shift (c m : ℕ) :
    ∑ b ∈ range m, Real.log ((c : ℝ) + 1 + b) = lf (c + m) - lf c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, ← add_assoc c m 1, lf_succ]
    push_cast; ring_nf

theorem sum_lf_shift (M n : ℕ) : ∑ a ∈ range n, lf (M + 1 + a) = F2 (M + n) - F2 M := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, ← add_assoc M n 1, F2_succ]
    ring_nf

/-- `∑_{a,b<n} ln|a − b| = 2 F2(n − 1)` (the diagonal terms vanish: `ln 0 = 0`). -/
theorem self_sum_eq (n : ℕ) :
    ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), Real.log |(a : ℝ) - b| = 2 * F2 n := by
  induction n with
  | zero => simp [F2, lf]
  | succ n ih =>
    have e : ∀ a : ℕ, ∑ b ∈ range (n + 1 + 1), Real.log |((a : ℕ) : ℝ) - b| =
        ∑ b ∈ range (n + 1), Real.log |((a : ℕ) : ℝ) - b| +
          Real.log |((a : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| :=
      fun a => sum_range_succ _ _
    rw [sum_range_succ, sum_congr rfl (fun a _ => e a), sum_add_distrib, ih, e (n + 1), F2_succ]
    have key : ∑ a ∈ range (n + 1), Real.log |((a : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| = lf (n + 1) := by
      have : ∀ a ∈ range (n + 1), Real.log |((a : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| =
          Real.log (((0 : ℕ) : ℝ) + 1 + ((n - a : ℕ) : ℝ)) := by
        intro a ha
        rw [mem_range] at ha
        have han : (a : ℝ) ≤ n := by exact_mod_cast (by omega : a ≤ n)
        rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
        rw [Nat.cast_sub (by omega : a ≤ n)]; push_cast; ring_nf
      rw [sum_congr rfl this]
      have hr := sum_range_reflect (fun b => Real.log (((0 : ℕ) : ℝ) + 1 + (b : ℝ))) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      rw [hr, sum_log_shift 0 (n + 1)]
      simp [lf]
    have key2 : ∑ b ∈ range (n + 1), Real.log |((n + 1 : ℕ) : ℝ) - (b : ℝ)| = lf (n + 1) := by
      rw [← key]; refine sum_congr rfl fun b _ => by rw [abs_sub_comm]
    rw [key, key2]
    simp only [sub_self, abs_zero, Real.log_zero]
    ring

/-- `∑_{a,b<n} ln(n + 2 + a + b) = F2(3n) − 2 F2(2n) + F2(n)`. -/
theorem cross_sum_eq (n : ℕ) :
    ∑ a ∈ range n, ∑ b ∈ range n, Real.log ((n : ℝ) + 2 + a + b) =
      F2 (3 * n) - 2 * F2 (2 * n) + F2 n := by
  have h1 : ∀ a ∈ range n, ∑ b ∈ range n, Real.log ((n : ℝ) + 2 + a + b) =
      lf (n + 1 + a + n) - lf (n + 1 + a) := by
    intro a _
    rw [← sum_log_shift]
    refine sum_congr rfl fun b _ => ?_
    push_cast; ring_nf
  rw [sum_congr rfl h1, sum_sub_distrib]
  have h2 : ∑ a ∈ range n, lf (n + 1 + a + n) = F2 (3 * n) - F2 (2 * n) := by
    rw [show 3 * n = 2 * n + n by ring, ← sum_lf_shift]
    refine sum_congr rfl fun a _ => ?_
    congr 1; ring
  have h3 : ∑ a ∈ range n, lf (n + 1 + a) = F2 (2 * n) - F2 n := by
    rw [show 2 * n = n + n by ring, ← sum_lf_shift]
  rw [h2, h3]; ring

/-! ### The outer set -/

/-- The outer thirds `𝒪 = [h+1, 3h] ∪ [−3h, −(h+1)]` of `[−3h, 3h]`. -/
def Oset (h : ℕ) : Finset ℤ := Icc ((h : ℤ) + 1) (3 * h) ∪ Icc (-(3 * (h : ℤ))) (-((h : ℤ) + 1))

theorem Oset_disj (h : ℕ) :
    Disjoint (Icc ((h : ℤ) + 1) (3 * h)) (Icc (-(3 * (h : ℤ))) (-((h : ℤ) + 1))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [mem_Icc] at ha hb
  omega

theorem sum_Icc_pos {M : Type*} [AddCommMonoid M] (h : ℕ) (F : ℤ → M) :
    ∑ k ∈ Icc ((h : ℤ) + 1) (3 * h), F k = ∑ a ∈ range (2 * h), F ((h : ℤ) + 1 + a) := by
  refine sum_nbij' (fun k => (k - h - 1).toNat) (fun a => (h : ℤ) + 1 + a) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
  · intro a ha; simp only [mem_Icc, mem_range] at ha ⊢; omega
  · intro k hk; simp only [mem_Icc] at hk; dsimp only; omega
  · intro a _; dsimp only; omega
  · intro k hk; simp only [mem_Icc] at hk; dsimp only; congr 1; omega

theorem sum_Icc_neg {M : Type*} [AddCommMonoid M] (h : ℕ) (F : ℤ → M) :
    ∑ k ∈ Icc (-(3 * (h : ℤ))) (-((h : ℤ) + 1)), F k =
      ∑ a ∈ range (2 * h), F (-((h : ℤ) + 1 + a)) := by
  refine (sum_nbij' (fun k => (-k - h - 1).toNat) (fun a => -((h : ℤ) + 1 + a)) ?_ ?_ ?_ ?_ ?_)
  · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
  · intro a ha; simp only [mem_Icc, mem_range] at ha ⊢; omega
  · intro k hk; simp only [mem_Icc] at hk; dsimp only; omega
  · intro a _; dsimp only; omega
  · intro k hk; simp only [mem_Icc] at hk; dsimp only; congr 1; omega

theorem self_part (h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ range (2 * h), ∑ b ∈ range (2 * h),
      Real.log |((((h : ℤ) + 1 + a) - ((h : ℤ) + 1 + b) : ℤ) : ℝ)| = 2 * F2 (2 * h - 1) := by
  rw [← self_sum_eq, Nat.sub_add_cancel (by omega)]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  push_cast; ring_nf

theorem log_le_Bk (d : ℝ) : Real.log |d| ≤ Real.log (1 + d ^ 2) / 2 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have h : Real.log |d| = Real.log (d ^ 2) / 2 := by
    rw [Real.log_pow, ← Real.log_abs d]; push_cast; ring
  rw [h]
  have := Real.log_le_log (by positivity) (by linarith : d ^ 2 ≤ 1 + d ^ 2)
  linarith

/-- **The discrete energy of the outer set**, `n = 2h`:
`∑_{k,m ∈ 𝒪} ln|k − m| ≥ 4n² ln n + (9 ln 3 − 8 ln 2 − 6) n² − 300 n (1 + ln n)`. -/
theorem outer_energy_ge (h : ℕ) (hh : 1 ≤ h) :
    4 * ((2 * h : ℕ) : ℝ) ^ 2 * Real.log (2 * h : ℕ) +
        (9 * Real.log 3 - 8 * Real.log 2 - 6) * ((2 * h : ℕ) : ℝ) ^ 2 -
        300 * ((2 * h : ℕ) : ℝ) * (1 + Real.log (2 * h : ℕ)) ≤
      ∑ k ∈ Oset h, ∑ m ∈ Oset h, Real.log |((k - m : ℤ) : ℝ)| := by
  set n := 2 * h with hn
  have hn1 : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  unfold Oset
  rw [sum_union (Oset_disj h)]
  simp_rw [sum_union (Oset_disj h)]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_Icc_pos, sum_Icc_neg]
  simp_rw [sum_Icc_pos h, sum_Icc_neg h]
  -- self parts
  have hs1 := self_part h hh
  have hs2 : ∑ a ∈ range n, ∑ b ∈ range n,
      Real.log |(((-((h : ℤ) + 1 + a)) - (-((h : ℤ) + 1 + b)) : ℤ) : ℝ)| = 2 * F2 (n - 1) := by
    rw [← self_part h hh]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [← abs_neg]; push_cast; ring_nf
  have hc : ∀ (a b : ℕ), Real.log |((((h : ℤ) + 1 + a) - (-((h : ℤ) + 1 + b)) : ℤ) : ℝ)| =
      Real.log ((n : ℝ) + 2 + a + b) := by
    intro a b
    rw [abs_of_nonneg (by push_cast; linarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h),
      (Nat.cast_nonneg a : (0:ℝ) ≤ a), (Nat.cast_nonneg b : (0:ℝ) ≤ b)])]
    simp only [hn]; push_cast; ring_nf
  have hc' : ∀ (a b : ℕ), Real.log |(((-((h : ℤ) + 1 + a)) - ((h : ℤ) + 1 + b) : ℤ) : ℝ)| =
      Real.log ((n : ℝ) + 2 + a + b) := by
    intro a b
    rw [← hc a b, ← abs_neg]; push_cast; ring_nf
  simp_rw [hc, hc']
  rw [hs1, hs2, cross_sum_eq]
  -- asymptotics
  have hF2n1 : F2 n - lf n = F2 (n - 1) := by
    have := F2_succ (n - 1)
    rw [Nat.sub_add_cancel hn1] at this
    linarith
  have hlf := lf_upper n
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have a1 := F2_ge hn1
  have a3 := F2_ge (N := 3 * n) (by omega)
  have a2 := F2_le (N := 2 * n) (by omega)
  have l3 : Real.log ((3 * n : ℕ) : ℝ) = Real.log 3 + Real.log n := by
    push_cast; rw [Real.log_mul (by norm_num) (by positivity)]
  have l2 : Real.log ((2 * n : ℕ) : ℝ) = Real.log 2 + Real.log n := by
    push_cast; rw [Real.log_mul (by norm_num) (by positivity)]
  rw [l3] at a3
  rw [l2] at a2
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hl2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hl3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast at a1 a2 a3 ⊢
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) hL]

end PadicWin.LogEnergy
