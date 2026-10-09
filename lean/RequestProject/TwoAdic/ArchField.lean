import RequestProject.TwoAdic.ArchEnergy
import RequestProject.TwoAdic.MainR3
import RequestProject.Zeta7.Hankel2.LemmaB61

/-!
# The archimedean field `arch` (II Theorem 4.1; P, Theorem 6.1)

* `errR_le`: the reduction error is `𝓔(n, qn) ≤ C_{q,d} n (1 + ln n)` for even `n ≥ 1`;
* `arch_exp`: `‖Δ_{qn}‖₁ ≤ exp(−q²n² ln n + (F + ε) n²)` for all large even `n`;
* **`arch_field`**: the field `arch` of `TwoAdicInputsR3` verbatim (with `Δ_{qn} ≠ 0`, so that
  `ln` is the true logarithm of a positive number).
-/

open Finset PadicWin Hankel2

namespace TwoAdicWin.Arch

/-- The constant of the reduction error. -/
noncomputable def Cerr (q d : ℕ) : ℝ :=
  q * (Real.log (q * Cqd q d) + q * Real.log (6 * q) + 13 * q) + 5 * (q : ℝ) ^ 2 +
    4 * (Real.log (q.factorial) + 2 * q)

theorem errR_le {q d n : ℕ} (hq : 2 ≤ q) (hn : Even n) (hn1 : 1 ≤ n) :
    errR q d n (q * n) ≤ Cerr q d * n * (1 + Real.log n) := by
  have h2R : 2 * R n = 3 * n := R_of_even hn
  have h2R' : (2 * (R n : ℝ)) = 3 * n := by exact_mod_cast h2R
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hX : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hC : (1 : ℝ) ≤ Cqd q d := by
    have : 1 ≤ Cqd q d := Nat.one_le_iff_ne_zero.2 (by unfold Cqd; positivity)
    exact_mod_cast this
  have hLam1 := one_le_LamT (n := n) (by omega : 1 ≤ q)
  have hLam : LamT q n ≤ 6 * q * n := by
    unfold LamT
    have : ((2 * R n + 1 : ℕ) : ℝ) = 3 * n + 1 := by rw [Nat.cast_add, Nat.cast_mul]; push_cast; linarith
    rw [this]; nlinarith
  have hlogLam : Real.log (LamT q n) ≤ Real.log (6 * q) + Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) hLam
  have hlogLam0 : 0 ≤ Real.log (LamT q n) := Real.log_nonneg hLam1
  have hQ : Real.log (Qc q d n) = Real.log (q * Cqd q d) + q * Real.log (LamT q n) := by
    unfold Qc
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hA : 0 ≤ Real.log (q * Cqd q d) := Real.log_nonneg (by nlinarith)
  have hl3 : Real.log (3 * (n : ℝ)) ≤ 2 + Real.log n := ArchB.log_three_mul_le (by omega)
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfac : 0 ≤ Real.log (q.factorial) := Real.log_natCast_nonneg _
  unfold errR Cerr
  rw [hQ, h2R']
  push_cast
  set X := Real.log n
  set A := Real.log (q * Cqd q d)
  set B := Real.log (6 * q)
  have hB : 0 ≤ B := Real.log_nonneg (by linarith)
  -- first term
  have t1 : (q : ℝ) * n * (A + q * Real.log (LamT q n) + 4 * q * (1 + Real.log (3 * (n : ℝ))) +
      q * Real.log 2) ≤ (q * (A + q * B + 13 * q) + 5 * (q : ℝ) ^ 2) * n * (1 + X) := by
    have i1 : A + q * Real.log (LamT q n) + 4 * q * (1 + Real.log (3 * (n : ℝ))) + q * Real.log 2
        ≤ (A + q * B + 13 * q) + 5 * q * X := by
      have : (q : ℝ) * Real.log (LamT q n) ≤ q * (B + X) :=
        mul_le_mul_of_nonneg_left hlogLam (by linarith)
      have : 4 * (q : ℝ) * (1 + Real.log (3 * (n : ℝ))) ≤ 4 * q * (3 + X) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have : (q : ℝ) * Real.log 2 ≤ q * 1 := mul_le_mul_of_nonneg_left hl2 (by linarith)
      nlinarith
    have hqn : (0 : ℝ) ≤ q * n := by positivity
    calc (q : ℝ) * n * (A + q * Real.log (LamT q n) + 4 * q * (1 + Real.log (3 * (n : ℝ))) +
          q * Real.log 2) ≤ q * n * ((A + q * B + 13 * q) + 5 * q * X) :=
          mul_le_mul_of_nonneg_left i1 hqn
      _ ≤ (q * (A + q * B + 13 * q) + 5 * (q : ℝ) ^ 2) * n * (1 + X) := by
          have h0 : 0 ≤ (q : ℝ) * (A + q * B + 13 * q) := by positivity
          have h1 : 0 ≤ (q : ℝ) * (A + q * B + 13 * q) * n * X := by positivity
          have h2 : 0 ≤ 5 * (q : ℝ) ^ 2 * n := by positivity
          nlinarith
  have t2 : (3 * (n : ℝ) + 1) * (Real.log (q.factorial) + 2 * q * Real.log 2) ≤
      4 * (Real.log (q.factorial) + 2 * q) * n * (1 + X) := by
    have : Real.log (q.factorial) + 2 * q * Real.log 2 ≤ Real.log (q.factorial) + 2 * q := by
      nlinarith
    have h0 : 0 ≤ Real.log (q.factorial) + 2 * q * Real.log 2 := by positivity
    have h1 : 0 ≤ 4 * (Real.log (q.factorial) + 2 * q) * n * X := by positivity
    nlinarith
  linarith

/-- **The archimedean bound, exponential form.** -/
theorem arch_exp (q d : ℕ) (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    l1Mv (hankelPoly q d n (q * n)) ≤
      Real.exp (-((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2) := by
  have hC0 : 0 ≤ 100 * (q : ℝ) ^ 2 + Cerr q d := by
    have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hC : (1 : ℝ) ≤ Cqd q d := by
      have : 1 ≤ Cqd q d := Nat.one_le_iff_ne_zero.2 (by unfold Cqd; positivity)
      exact_mod_cast this
    have : 0 ≤ Real.log (q * Cqd q d) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ Real.log (6 * q) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (q.factorial) := Real.log_natCast_nonneg _
    unfold Cerr; positivity
  obtain ⟨N, hN⟩ := ArchB.nlogn_le_eps_sq _ hC0 hε
  refine ⟨N + 1, fun n hNn hn => ?_⟩
  obtain ⟨h, rfl⟩ := hn
  have hh : 1 ≤ h := by omega
  have e : h + h = 2 * h := by ring
  rw [e] at hNn ⊢
  have hred := arch_reduction (d := d) (K := q * (2 * h)) hq ⟨h, by ring⟩ _
    (fun s hs => EB_le q h hh hs)
  refine hred.trans (Real.exp_le_exp.2 ?_)
  have h1 := errR_le (d := d) hq ⟨h, by ring⟩ (by omega : 1 ≤ 2 * h)
  have h2 := hN (2 * h) (by omega) (by omega)
  push_cast at h1 h2 ⊢
  nlinarith

/-- **The field `arch` (II Theorem 4.1; P, Theorem 6.1)**, verbatim. -/
theorem arch_field : ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Even n → hankelPoly q d n (q * n) ≠ 0 →
      Real.log (PadicWin.l1Mv (hankelPoly q d n (q * n))) ≤
        -((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n) + (Fconst q + ε) * (n : ℝ) ^ 2 := by
  intro q d hadm ε hε
  have hq : 2 ≤ q := by have := hadm.1; omega
  obtain ⟨N, hN⟩ := arch_exp q d hq hε
  refine ⟨N, fun n hNn hn hne => ?_⟩
  rw [Real.log_le_iff_le_exp (l1Mv_pos_of_ne hne)]
  exact hN n hNn hn

end TwoAdicWin.Arch
