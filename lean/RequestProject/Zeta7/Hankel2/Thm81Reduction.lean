import RequestProject.Zeta7.Hankel2.CircleCount
import RequestProject.Zeta7.Hankel2.PrimeSums

/-!
# Theorem 8.1 reduced to the prime number theorem and a finite certificate (paper §8.5)

`StepMajorant κ₁ κ₂` encodes the data of Appendix B: a finite partition
`1/20 = a₀ < a₁ < ⋯ < a_M = 9/2` refining `𝓑 ∩ (1/20, 9/2)`, and on each cell `[a_{i−1}, a_i]`
rationals `λ_i`, `h_i ≥ 0` with `h_i ≥ g(λ_i, u, κ)` at the four corners
`u ∈ {a_{i−1}, a_i}`, `κ ∈ {κ₁, κ₂}` (`g = gfun`, eq. (gdef)).

**`thm81_of_stepMajorant`**: `θ(x) ∼ x`, the Mertens asymptotics and a `StepMajorant κ₁ κ₂`
(with `κ₂ ≤ 6`) imply Theorem 8.1 on `κ ∈ [κ₁, κ₂]` with
`c(κ) = (1/ln 2) [A(κ)(−γ − ln 2 − ln 20) + ∑ h_i (a_i − a_{i−1}) + 5κ/20 + 12.5/400]`,
`A(κ) = κ(6 − κ)`.

Assembly (paper §8.5): primes `p > 4n` contribute nothing; for `p ≤ n/20` the main terms of
Lemma 8.3 (A1, used for `p² ≤ 6n`) and Proposition 8.5 (used for `p² > 6n`) are both
`≤ K(6n+4−K) ln p/(p−1)`, whose sum is `K(6n+4−K) · mertensSum(n/20)`; the A1 error terms
`(12 K L_p + 113 n) ln p` over the `O(√n)` primes with `p² ≤ 6n` are `O(n^{3/2} log n)`; the
Proposition 8.5 error terms give `5K θ(n/20) + 25 ∑_{p ≤ n/20} p ln p ≤ (5κ/20 + 12.5/400 + o(1)) n²`;
for `n/20 < p ≤ 4n` eq. (gdef) and the step majorant give `max(T_p,0) ≤ n h_i + O(1)` on the
`i`-th cell, and `θ(a_i n) − θ(a_{i−1} n) = (a_i − a_{i−1}) n + o(n)`.
(The paper splits the small primes at `Y = n^{0.9}`; here the split is at `p² = 6n`, the exact
condition of Proposition 8.5 — the resulting statement is the same.)
-/

open Filter Topology Finset Chebyshev

namespace Hankel2.Fam3

open Circle

/-- **Appendix B data** for `κ ∈ [κ₁, κ₂]`: a step majorant of `g(λ, u, κ)` on `[1/20, 9/2]`. -/
structure StepMajorant (κ₁ κ₂ : ℝ) where
  /-- number of cells -/
  M : ℕ
  /-- the partition points `a₀ < ⋯ < a_M` -/
  a : Fin (M + 1) → ℚ
  a_strictMono : StrictMono a
  a_zero : a 0 = 1 / 20
  a_last : a (Fin.last M) = 9 / 2
  /-- the partition refines `𝓑 ∩ (1/20, 9/2)` -/
  refines : ∀ b ∈ Bset, (1 / 20 : ℝ) < b → b < 9 / 2 → ∃ j, (a j : ℝ) = b
  /-- the multipliers `λ_i` -/
  lam : Fin M → ℚ
  /-- the heights `h_i` -/
  h : Fin M → ℚ
  /-- `h_i ≥ g(λ_i, u, κ)` at the four corners of the cell -/
  dom : ∀ i : Fin M, ∀ u : ℝ, (u = a i.castSucc ∨ u = a i.succ) →
    ∀ κ : ℝ, (κ = κ₁ ∨ κ = κ₂) → gfun (lam i) u κ ≤ h i
  h_nonneg : ∀ i, 0 ≤ h i

/-- The constant `c(κ)` of Theorem 8.1 attached to a step majorant (in bits). -/
noncomputable def cfunB {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) (κ : ℝ) : ℝ :=
  (1 / Real.log 2) * (κ * (6 - κ) * (-Real.eulerMascheroniConstant - Real.log 2 - Real.log 20)
    + ∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc)
    + 5 * κ / 20 + 12.5 / 400)

/-- The statement of Theorem 8.1 (the field `thm_8_1` of `Zeta27Inputs`) for `κ = K/n ∈ [κ₁, κ₂]`
and a given constant function `cfun`. -/
def Thm81On (κ₁ κ₂ : ℝ) (cfun : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → n % 2 = 1 →
    κ₁ ≤ (K : ℝ) / n → (K : ℝ) / n ≤ κ₂ → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2) →
      ∑ p ∈ S, (TPplus p n K : ℝ) * Real.logb 2 p ≤
        ((K : ℝ) / n) * (6 - (K : ℝ) / n) * (n : ℝ) ^ 2 * Real.logb 2 n
          + cfun ((K : ℝ) / n) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2

section StepMajorantAPI

variable {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂)

theorem StepMajorant.a_mem (j : Fin (C.M + 1)) : (1 / 20 : ℝ) ≤ C.a j ∧ (C.a j : ℝ) ≤ 9 / 2 := by
  have h1 := C.a_strictMono.monotone (Fin.zero_le j)
  have h2 := C.a_strictMono.monotone (Fin.le_last j)
  rw [C.a_zero] at h1
  rw [C.a_last] at h2
  have h1' := (Rat.cast_le (K := ℝ)).2 h1
  have h2' := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h1' h2'
  exact ⟨h1', h2'⟩

theorem StepMajorant.noB (i : Fin C.M) : ∀ v ∈ Set.Ioo (C.a i.castSucc : ℝ) (C.a i.succ), v ∉ Bset := by
  intro v hv hB
  obtain ⟨j, hj⟩ := C.refines v hB (by linarith [(C.a_mem i.castSucc).1, hv.1])
    (by linarith [(C.a_mem i.succ).2, hv.2])
  rw [← hj] at hv
  have h1 : C.a i.castSucc < C.a j := by exact_mod_cast hv.1
  have h2 : C.a j < C.a i.succ := by exact_mod_cast hv.2
  rw [C.a_strictMono.lt_iff_lt, Fin.lt_def] at h1 h2
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  omega

theorem StepMajorant.exists_cell {x : ℝ} (h1 : 1 / 20 < x) (h2 : x ≤ 9 / 2) :
    ∃ i : Fin C.M, (C.a i.castSucc : ℝ) < x ∧ x ≤ C.a i.succ := by
  classical
  set s := univ.filter (fun j : Fin (C.M + 1) => (C.a j : ℝ) < x)
  have h0 : (0 : Fin (C.M + 1)) ∈ s := by
    simp only [s, mem_filter, mem_univ, true_and, C.a_zero]; push_cast; linarith
  set j := s.max' ⟨0, h0⟩
  have hj : j ∈ s := max'_mem _ _
  have hjx : (C.a j : ℝ) < x := (mem_filter.1 hj).2
  have hjM : j.val < C.M := by
    by_contra hc
    have : j = Fin.last C.M := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [this, C.a_last] at hjx; push_cast at hjx; linarith
  refine ⟨⟨j.val, hjM⟩, ?_, ?_⟩
  · have : (⟨j.val, hjM⟩ : Fin C.M).castSucc = j := Fin.ext rfl
    rw [this]; exact hjx
  · by_contra hc
    push_neg at hc
    have hmem : (⟨j.val, hjM⟩ : Fin C.M).succ ∈ s := by simp only [s, mem_filter, mem_univ, true_and]; exact hc
    have := le_max' s _ hmem
    rw [Fin.le_def] at this
    simp only [Fin.val_succ] at this
    omega

theorem StepMajorant.gfun_le (i : Fin C.M) {u κ : ℝ}
    (hu : u ∈ Set.Icc (C.a i.castSucc : ℝ) (C.a i.succ)) (hκ : κ ∈ Set.Icc κ₁ κ₂) :
    gfun (C.lam i) u κ ≤ C.h i := by
  have ha : (0 : ℝ) < C.a i.castSucc := by linarith [(C.a_mem i.castSucc).1]
  have hab : (C.a i.castSucc : ℝ) < C.a i.succ := by
    exact_mod_cast C.a_strictMono (Fin.castSucc_lt_succ (i := i))
  have hG := Gpot_le_max (fun t => psiT t 0 (C.lam i : ℝ)) ha hab (C.noB i) hu
  have hd := C.dom i
  unfold gfun at hd ⊢
  have hl : (C.lam i : ℝ) * κ ≤ C.lam i * κ₁ ∨ (C.lam i : ℝ) * κ ≤ C.lam i * κ₂ := by
    rcases le_total 0 (C.lam i : ℝ) with h0 | h0
    · right; exact mul_le_mul_of_nonneg_left hκ.2 h0
    · left; nlinarith [hκ.1]
  rcases hl with hl | hl <;>
    rcases le_total (Gpot (fun t => psiT t 0 (C.lam i : ℝ)) (C.a i.castSucc : ℝ))
      (Gpot (fun t => psiT t 0 (C.lam i : ℝ)) (C.a i.succ : ℝ)) with hm | hm
  all_goals first | rw [max_eq_right hm] at hG | rw [max_eq_left hm] at hG
  all_goals first
    | linarith [hd _ (Or.inl rfl) _ (Or.inl rfl)]
    | linarith [hd _ (Or.inl rfl) _ (Or.inr rfl)]
    | linarith [hd _ (Or.inr rfl) _ (Or.inl rfl)]
    | linarith [hd _ (Or.inr rfl) _ (Or.inr rfl)]

end StepMajorantAPI

theorem TPplus_nonneg (p n K : ℕ) : (0 : ℝ) ≤ TPplus p n K := by
  unfold TPplus
  induction h : TP p n K with
  | bot => simp
  | coe t =>
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simp
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]; simpa using ht

/-- Eq. (gdef) for `max(T_p, 0)`. -/
theorem TPplus_le_gdef {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n % 2 = 1) (h6 : 6 * n < p ^ 2)
    (K : ℕ) (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (hεp : ε * n ≤ p) :
    (TPplus p n K : ℝ) ≤ max (n * gfun lam ((p : ℝ) / n) ((K : ℝ) / n) + 13 * Ceps ε lam) 0 := by
  unfold TPplus
  induction h : TP p n K with
  | bot => simp
  | coe t =>
    have := TP_le_gdef hp hp2 hn h6 K lam hε hεp t h
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simp
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]
      simp only [WithBot.unbotD_coe]
      exact le_max_of_le_left this

/-- The odd primes `p ≤ 4n`. -/
def oddPr (n : ℕ) : Finset ℕ := (Icc 3 (4 * n)).filter Nat.Prime

/-- Only odd primes `≤ 4n` contribute to `∑_{p ∈ S} max(T_p, 0) ln p`. -/
theorem sum_S_le_oddPr {n K : ℕ} (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ S, (TPplus p n K : ℝ) * Real.log p ≤ ∑ p ∈ oddPr n, (TPplus p n K : ℝ) * Real.log p := by
  rw [sum_TPplus_large_eq S hS]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpr, hp2⟩ := hS p hp.1
    simp only [oddPr, mem_filter, mem_Icc]
    exact ⟨⟨by have := hpr.two_le; omega, hp.2⟩, hpr⟩
  · intro p _ _
    exact mul_nonneg (TPplus_nonneg p n K) (Real.log_natCast_nonneg p)

/-- **Primes `p ≤ n/20`** (Lemma 8.3 for `p² ≤ 6n`, Proposition 8.5 for `p² > 6n`):
the main terms sum to at most `K(6n+4−K) · mertensSum(n/20)`. -/
theorem sum_small_le {n K : ℕ} (hK : K ≤ 6 * n) :
    ∑ p ∈ (oddPr n).filter (fun p => 20 * p ≤ n), (TPplus p n K : ℝ) * Real.log p ≤
      (K : ℝ) * (6 * n + 4 - K) * mertensSum ((n : ℝ) / 20)
      + ∑ p ∈ (oddPr n).filter (fun p => p ^ 2 ≤ 6 * n),
          (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p
      + ∑ p ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (5 * (K : ℝ) + 25 * p) * Real.log p := by
  classical
  set T1 := (oddPr n).filter (fun p => 20 * p ≤ n)
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
  have hKc : 0 ≤ (K : ℝ) * (6 * n + 4 - K) := by
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hper : ∀ p ∈ T1, (TPplus p n K : ℝ) * Real.log p ≤
      (K : ℝ) * (6 * n + 4 - K) * (Real.log p / ((p : ℝ) - 1))
      + (if p ^ 2 ≤ 6 * n then (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p else 0)
      + (5 * (K : ℝ) + 25 * p) * Real.log p := by
    intro p hp
    simp only [T1, oddPr, mem_filter, mem_Icc] at hp
    obtain ⟨⟨⟨hp3, hp4⟩, hpr⟩, h20⟩ := hp
    haveI : Fact p.Prime := ⟨hpr⟩
    have hp2 : p ≠ 2 := by omega
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hE2 : 0 ≤ (5 * (K : ℝ) + 25 * p) * Real.log p := by positivity
    split_ifs with hsq
    · have h := mul_le_mul_of_nonneg_right (lemmaA1_plus hp2 n K (by omega)) hlog
      have e : ((K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n) * Real.log p =
          (K : ℝ) * (6 * n + 4 - K) * (Real.log p / ((p : ℝ) - 1))
            + (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p := by ring
      linarith
    · have h := prop85_plus (n := n) (K := K) hp2 (by push_neg at hsq; omega) (by omega)
      have hdiv : (K : ℝ) * (6 * n + 4 - K) / p ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) :=
        div_le_div_of_nonneg_left hKc (by linarith) (by linarith)
      have h' := mul_le_mul_of_nonneg_right
        (h.trans (by linarith [hdiv] : _ ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 5 * K + 25 * p)) hlog
      have e : ((K : ℝ) * (6 * n + 4 - K) / (p - 1) + 5 * K + 25 * p) * Real.log p =
          (K : ℝ) * (6 * n + 4 - K) * (Real.log p / ((p : ℝ) - 1))
            + (5 * (K : ℝ) + 25 * p) * Real.log p := by ring
      linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_filter]
  have ha : ∑ p ∈ T1, Real.log p / ((p : ℝ) - 1) ≤ mertensSum ((n : ℝ) / 20) := by
    unfold mertensSum
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [T1, oddPr, mem_filter, mem_Icc] at hp ⊢
      refine ⟨⟨hp.1.1.1, Nat.le_floor ?_⟩, hp.1.2⟩
      have : ((20 * p : ℕ) : ℝ) ≤ n := by exact_mod_cast hp.2
      push_cast at this; linarith
    · intro p hp _
      simp only [mem_filter, mem_Icc] at hp
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp.1.1
      exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
  have hb : ∑ p ∈ T1.filter (fun p => p ^ 2 ≤ 6 * n), (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p ≤
      ∑ p ∈ (oddPr n).filter (fun p => p ^ 2 ≤ 6 * n), (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [T1, mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    · intro p _ _
      have := Real.log_natCast_nonneg p
      positivity
  have hc : ∑ p ∈ T1, (5 * (K : ℝ) + 25 * p) * Real.log p ≤
      ∑ p ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (5 * (K : ℝ) + 25 * p) * Real.log p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [T1, oddPr, mem_filter, mem_Icc, mem_range] at hp ⊢
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hp.1.2⟩
      have : ((20 * p : ℕ) : ℝ) ≤ n := by exact_mod_cast hp.2
      push_cast at this; linarith
    · intro p _ _
      have := Real.log_natCast_nonneg p
      positivity
  have := mul_le_mul_of_nonneg_left ha hKc
  linarith

/-- `∑_i C_{1/20}(λ_i)`, a uniform bound for the constants of eq. (gdef) on all cells. -/
noncomputable def StepMajorant.Csum {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) : ℝ :=
  ∑ i : Fin C.M, Ceps (1 / 20) (C.lam i)

theorem StepMajorant.Csum_nonneg {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) : 0 ≤ C.Csum :=
  sum_nonneg fun i _ => Ceps_nonneg (by norm_num) _

/-- **Primes `n/20 < p ≤ 4n`** (eq. (gdef) and the step majorant): on the `i`-th cell
`max(T_p, 0) ≤ n h_i + 13 C`, hence the contribution of the cell is at most
`(n h_i + 13 C)(θ(a_i n) − θ(a_{i−1} n))`. -/
theorem sum_large_le {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) {n K : ℕ} (hn : n % 2 = 1)
    (hn2400 : 2400 ≤ n) (hκ1 : κ₁ ≤ (K : ℝ) / n) (hκ2 : (K : ℝ) / n ≤ κ₂) :
    ∑ p ∈ (oddPr n).filter (fun p => ¬ 20 * p ≤ n), (TPplus p n K : ℝ) * Real.log p ≤
      ∑ i : Fin C.M, ((n : ℝ) * C.h i + 13 * C.Csum) *
        (θ ((C.a i.succ : ℝ) * n) - θ ((C.a i.castSucc : ℝ) * n)) := by
  classical
  set T3 := (oddPr n).filter (fun p => ¬ 20 * p ≤ n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let cell : Fin C.M → ℕ → Prop := fun i p =>
    (C.a i.castSucc : ℝ) < (p : ℝ) / n ∧ (p : ℝ) / n ≤ C.a i.succ
  have hcoef : ∀ i, 0 ≤ (n : ℝ) * C.h i + 13 * C.Csum := fun i => by
    have := C.h_nonneg i
    have : (0 : ℝ) ≤ C.h i := by exact_mod_cast this
    have := C.Csum_nonneg
    positivity
  have hper : ∀ p ∈ T3, (TPplus p n K : ℝ) * Real.log p ≤
      ∑ i : Fin C.M, if cell i p then ((n : ℝ) * C.h i + 13 * C.Csum) * Real.log p else 0 := by
    intro p hp
    simp only [T3, oddPr, mem_filter, mem_Icc] at hp
    obtain ⟨⟨⟨hp3, hp4⟩, hpr⟩, h20⟩ := hp
    have hp2 : p ≠ 2 := by omega
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have h20r : (n : ℝ) < 20 * p := by exact_mod_cast (show n < 20 * p by omega)
    have h4r : (p : ℝ) ≤ 4 * n := by exact_mod_cast hp4
    obtain ⟨i, hi1, hi2⟩ := C.exists_cell (x := (p : ℝ) / n)
      (by rw [lt_div_iff₀ hn0]; linarith) (by rw [div_le_iff₀ hn0]; linarith)
    have h6 : 6 * n < p ^ 2 := by
      have : 120 * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
      rw [sq]; omega
    have hg := TPplus_le_gdef hpr hp2 hn h6 K (C.lam i) (ε := 1 / 20) (by norm_num)
      (by linarith)
    have hgf := C.gfun_le i ⟨hi1.le, hi2⟩ ⟨hκ1, hκ2⟩
    have hCe : Ceps (1 / 20) (C.lam i) ≤ C.Csum :=
      single_le_sum (f := fun i => Ceps (1 / 20) (C.lam i))
        (fun j _ => Ceps_nonneg (by norm_num) _) (mem_univ i)
    have hT : (TPplus p n K : ℝ) ≤ (n : ℝ) * C.h i + 13 * C.Csum := by
      refine hg.trans (max_le ?_ (hcoef i))
      have := mul_le_mul_of_nonneg_left hgf hn0.le
      linarith
    calc (TPplus p n K : ℝ) * Real.log p ≤ ((n : ℝ) * C.h i + 13 * C.Csum) * Real.log p :=
          mul_le_mul_of_nonneg_right hT hlog
      _ = if cell i p then ((n : ℝ) * C.h i + 13 * C.Csum) * Real.log p else 0 := by
          rw [if_pos ⟨hi1, hi2⟩]
      _ ≤ _ := single_le_sum (f := fun i => if cell i p then
            ((n : ℝ) * C.h i + 13 * C.Csum) * Real.log p else 0)
          (fun j _ => by
            simp only
            split_ifs
            · exact mul_nonneg (hcoef j) hlog
            · exact le_refl _) (mem_univ i)
  refine (sum_le_sum hper).trans ?_
  rw [sum_comm]
  refine sum_le_sum fun i _ => ?_
  rw [← sum_filter, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hcoef i)
  have hmono : (C.a i.castSucc : ℝ) ≤ C.a i.succ := by
    exact_mod_cast (C.a_strictMono (Fin.castSucc_lt_succ (i := i))).le
  apply sum_log_le_theta_sub _ (mul_le_mul_of_nonneg_right hmono hn0.le)
  intro p hp
  simp only [T3, oddPr, mem_filter, mem_Icc, cell] at hp
  obtain ⟨⟨⟨_, hpr⟩, _⟩, h1, h2⟩ := hp
  exact ⟨hpr, (lt_div_iff₀ hn0).1 h1, (div_le_iff₀ hn0).1 h2⟩


/-- `L_p ln p ≤ ln(4n) + ln p`. -/
theorem Lp_mul_log_le {p n : ℕ} (hp : 1 < p) (hn : 1 ≤ n) :
    (Lp p n : ℝ) * Real.log p ≤ Real.log (4 * n) + Real.log p := by
  have h : p ^ (Lp p n - 1) < 4 * n := by
    simpa [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self hp (show 1 < 4 * n by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h' : (p : ℝ) ^ (Lp p n - 1) ≤ 4 * n := by exact_mod_cast h.le
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hl
  have hc : (Lp p n : ℝ) ≤ ((Lp p n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show Lp p n ≤ (Lp p n - 1) + 1 by omega)
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  nlinarith

/-- The Lemma 8.3 error terms over the primes with `p² ≤ 6n`: `O(n^{3/2} log n)`. -/
theorem sum_sqrtRange_le {n K : ℕ} (hn : 1 ≤ n) (hK : K ≤ 6 * n) :
    ∑ p ∈ (oddPr n).filter (fun p => p ^ 2 ≤ 6 * n), (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p ≤
      1028 * n * Real.sqrt n * Real.log (4 * n) := by
  set R := (oddPr n).filter (fun p => p ^ 2 ≤ 6 * n)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl4 : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
  have hterm : ∀ p ∈ R, (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p ≤
      257 * n * Real.log (4 * n) := by
    intro p hp
    simp only [R, oddPr, mem_filter, mem_Icc] at hp
    obtain ⟨⟨⟨hp3, hp4⟩, _⟩, _⟩ := hp
    have hlp : Real.log p ≤ Real.log (4 * n) :=
      Real.log_le_log (by exact_mod_cast (show 0 < p by omega)) (by exact_mod_cast hp4)
    have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hL := Lp_mul_log_le (p := p) (show 1 < p by omega) hn
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have e : (12 * (K : ℝ) * Lp p n + 113 * n) * Real.log p =
        12 * (K : ℝ) * ((Lp p n : ℝ) * Real.log p) + 113 * n * Real.log p := by ring
    rw [e]
    have h1 : 12 * (K : ℝ) * ((Lp p n : ℝ) * Real.log p) ≤ 12 * (K : ℝ) * (2 * Real.log (4 * n)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 113 * (n : ℝ) * Real.log p ≤ 113 * n * Real.log (4 * n) :=
      mul_le_mul_of_nonneg_left hlp (by positivity)
    have h3 : 24 * (K : ℝ) * Real.log (4 * n) ≤ 144 * n * Real.log (4 * n) := by nlinarith
    linarith
  have hcard : (R.card : ℝ) ≤ 4 * Real.sqrt n := by
    have hsub : R ⊆ range (Nat.sqrt (6 * n) + 1) := by
      intro p hp
      simp only [R, mem_filter, mem_range] at hp ⊢
      exact Nat.lt_succ_of_le (Nat.le_sqrt'.2 hp.2)
    have h1 : (R.card : ℝ) ≤ Nat.sqrt (6 * n) + 1 := by
      have := card_le_card hsub
      rw [card_range] at this
      exact_mod_cast this
    have h2 : (Nat.sqrt (6 * n) : ℝ) ≤ Real.sqrt (6 * n) := by
      have := Real.nat_sqrt_le_real_sqrt (a := 6 * n)
      push_cast at this; exact this
    have h3 : Real.sqrt (6 * n) ≤ 3 * Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 6 ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    have h4 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hnr
    linarith
  calc _ ≤ ∑ p ∈ R, 257 * (n : ℝ) * Real.log (4 * n) := sum_le_sum hterm
    _ = R.card * (257 * (n : ℝ) * Real.log (4 * n)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (4 * Real.sqrt n) * (257 * (n : ℝ) * Real.log (4 * n)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1028 * n * Real.sqrt n * Real.log (4 * n) := by ring


/-- The main term: `K(6n+4−K) · mertensSum(n/20) ≤ A n² ln n + A c₀ n² + 9δ n² + 24 n ln n`. -/
theorem main_term_le {n K : ℕ} {κ L c0 δ mS : ℝ} (hn0 : 0 < (n : ℝ)) (hKk : (K : ℝ) = κ * n)
    (hκ0 : 0 ≤ κ) (hκ6 : κ ≤ 6) (hmert : mS ≤ L + c0 + δ) (hc0 : c0 + δ ≤ 0) (hL0 : 0 ≤ L)
    (hδ : 0 ≤ δ) :
    (K : ℝ) * (6 * n + 4 - K) * mS ≤
      κ * (6 - κ) * (n : ℝ) ^ 2 * L + κ * (6 - κ) * c0 * (n : ℝ) ^ 2 + 9 * δ * (n : ℝ) ^ 2
        + 24 * n * L := by
  have hKc : 0 ≤ (K : ℝ) * (6 * n + 4 - K) := by
    have : κ * n ≤ 6 * n := mul_le_mul_of_nonneg_right hκ6 hn0.le
    rw [hKk]; exact mul_nonneg (by positivity) (by linarith)
  have s1 := mul_le_mul_of_nonneg_left hmert hKc
  have e : (K : ℝ) * (6 * n + 4 - K) * (L + c0 + δ) =
      κ * (6 - κ) * (n : ℝ) ^ 2 * L + κ * (6 - κ) * c0 * (n : ℝ) ^ 2
        + κ * (6 - κ) * ((n : ℝ) ^ 2 * δ) + 4 * (κ * n) * L + 4 * (κ * n) * (c0 + δ) := by
    rw [hKk]; ring
  have t1 : κ * (6 - κ) * ((n : ℝ) ^ 2 * δ) ≤ 9 * ((n : ℝ) ^ 2 * δ) :=
    mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (κ - 3)]) (by positivity)
  have t2 : 4 * (κ * n) * (c0 + δ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc0
  have t3 : 4 * (κ * n) * L ≤ 24 * n * L := by
    have : 0 ≤ (n : ℝ) * L := by positivity
    have := mul_le_mul_of_nonneg_right hκ6 this
    linarith
  linarith

/-- The Proposition 8.5 error terms: `5K θ(n/20) + 25 ∑_{p ≤ n/20} p ln p`. -/
theorem prop85_errors_le {n K : ℕ} {κ δ C1 C2 : ℝ} (hn0 : 0 < (n : ℝ)) (hKk : (K : ℝ) = κ * n)
    (hκ6 : κ ≤ 6) (hδ : 0 ≤ δ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hθu : ∀ y, 0 ≤ y → θ y ≤ (1 + δ) * y + C1)
    (hpl : ∀ X : ℝ, 0 ≤ X → ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime, (p : ℝ) * Real.log p ≤
        (1 / 2 + 2 * δ) * X ^ 2 + C2 * X) :
    ∑ p ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (5 * (K : ℝ) + 25 * p) * Real.log p
      ≤ 5 * κ / 20 * (n : ℝ) ^ 2 + 12.5 / 400 * (n : ℝ) ^ 2 + 5 / 2 * δ * (n : ℝ) ^ 2
        + (30 * C1 + 2 * C2) * n := by
  set P := (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime
  have e : ∑ p ∈ P, (5 * (K : ℝ) + 25 * p) * Real.log p
      = 5 * (K : ℝ) * ∑ p ∈ P, Real.log p + 25 * ∑ p ∈ P, (p : ℝ) * Real.log p := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun p _ => by ring
  rw [e]
  have hth : ∑ p ∈ P, Real.log p ≤ θ ((n : ℝ) / 20) := by
    have := sum_log_le_theta_sub P (x := 0) (y := (n : ℝ) / 20) (by positivity) (fun p hp => by
        simp only [P, mem_filter, mem_range] at hp
        refine ⟨hp.2, by exact_mod_cast hp.2.pos, ?_⟩
        exact (Nat.le_floor_iff (by positivity)).1 (Nat.lt_succ_iff.1 hp.1))
    rw [theta_eq_zero_of_lt_two (x := 0) (by norm_num), sub_zero] at this
    exact this
  have hθ20 := hθu ((n : ℝ) / 20) (by positivity)
  have hpl20 := hpl ((n : ℝ) / 20) (by positivity)
  have s1 : 5 * (K : ℝ) * ∑ p ∈ P, Real.log p ≤ 5 * (K : ℝ) * ((1 + δ) * ((n : ℝ) / 20) + C1) :=
    mul_le_mul_of_nonneg_left (hth.trans hθ20) (by positivity)
  have s2 : 5 * (K : ℝ) * ((1 + δ) * ((n : ℝ) / 20) + C1) ≤
      5 * κ / 20 * (n : ℝ) ^ 2 + 3 / 2 * δ * (n : ℝ) ^ 2 + 30 * C1 * n := by
    rw [hKk]
    have a1 : κ * ((n : ℝ) ^ 2 * δ) ≤ 6 * ((n : ℝ) ^ 2 * δ) :=
      mul_le_mul_of_nonneg_right hκ6 (by positivity)
    have a2 : κ * (n * C1) ≤ 6 * (n * C1) := mul_le_mul_of_nonneg_right hκ6 (by positivity)
    linarith
  have : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
  have : 0 ≤ C2 * (n : ℝ) := by positivity
  linarith

/-- The step-majorant cells: `∑_i (n h_i + 13 C)(θ(a_i n) − θ(a_{i−1} n)) ≤
(∑ h_i Δa_i) n² + 9δ (∑ h_i) n² + 78 C M n` once `θ(y) = y + O(δ y)` for `y ≥ n/20`. -/
theorem cells_le {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) {n : ℕ} {δ y0 : ℝ} (hδ : 0 ≤ δ)
    (hδ9 : δ ≤ 1 / 9) (hθa : ∀ y, y0 ≤ y → |θ y - y| ≤ δ * y) (hn0 : 0 < (n : ℝ))
    (hy0n : 20 * y0 ≤ n) :
    ∑ i : Fin C.M, ((n : ℝ) * C.h i + 13 * C.Csum) *
        (θ ((C.a i.succ : ℝ) * n) - θ ((C.a i.castSucc : ℝ) * n)) ≤
      (∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc)) * (n : ℝ) ^ 2
        + 9 * δ * (∑ i : Fin C.M, (C.h i : ℝ)) * (n : ℝ) ^ 2 + 78 * C.Csum * C.M * n := by
  have hi : ∀ i : Fin C.M, ((n : ℝ) * C.h i + 13 * C.Csum) *
      (θ ((C.a i.succ : ℝ) * n) - θ ((C.a i.castSucc : ℝ) * n)) ≤
      (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc) * (n : ℝ) ^ 2
        + 9 * δ * (C.h i : ℝ) * (n : ℝ) ^ 2 + 78 * C.Csum * n := by
    intro i
    obtain ⟨b1, b2⟩ := C.a_mem i.succ
    obtain ⟨c1, c2⟩ := C.a_mem i.castSucc
    have v1 := mul_le_mul_of_nonneg_right b1 hn0.le
    have v2 := mul_le_mul_of_nonneg_right c1 hn0.le
    have u1 := (abs_le.1 (hθa ((C.a i.succ : ℝ) * n) (by linarith))).2
    have u2 := (abs_le.1 (hθa ((C.a i.castSucc : ℝ) * n) (by linarith))).1
    have v3 : δ * n * ((C.a i.succ : ℝ) + C.a i.castSucc) ≤ δ * n * 9 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hdiff : θ ((C.a i.succ : ℝ) * n) - θ ((C.a i.castSucc : ℝ) * n) ≤
        ((C.a i.succ : ℝ) - C.a i.castSucc) * n + 9 * δ * n := by linarith
    have hh : (0 : ℝ) ≤ C.h i := by exact_mod_cast C.h_nonneg i
    have hCs := C.Csum_nonneg
    have hcoef : 0 ≤ (n : ℝ) * C.h i + 13 * C.Csum := by positivity
    have s := mul_le_mul_of_nonneg_left hdiff hcoef
    have hΔ : ((C.a i.succ : ℝ) - C.a i.castSucc) + 9 * δ ≤ 6 := by linarith
    have t : 13 * C.Csum * n * (((C.a i.succ : ℝ) - C.a i.castSucc) + 9 * δ) ≤
        13 * C.Csum * n * 6 := mul_le_mul_of_nonneg_left hΔ (by positivity)
    linarith
  refine (sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_mul, mul_sum, sum_mul]
  ring

/-- `ln(4n) ≤ (δ/1028) √n` gives `1028 n √n ln(4n) ≤ δ n²` and `24 n ln n ≤ δ n²`. -/
theorem log_errors_le {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hn1 : (1 : ℝ) ≤ n)
    (hlog : Real.log (4 * n) ≤ δ / 1028 * Real.sqrt n) :
    1028 * n * Real.sqrt n * Real.log (4 * n) ≤ δ * (n : ℝ) ^ 2 ∧
      24 * n * Real.log n ≤ δ * (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsq1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
  have hsqn : Real.sqrt n ≤ n := by
    have := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg (n : ℝ))
    linarith
  have hLl : Real.log n ≤ Real.log (4 * n) := Real.log_le_log hn0 (by linarith)
  constructor
  · have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1028 * (n : ℝ) * Real.sqrt n by positivity)
    have e : 1028 * (n : ℝ) * Real.sqrt n * (δ / 1028 * Real.sqrt n) =
        δ * n * (Real.sqrt n * Real.sqrt n) := by ring
    rw [e, hsq] at this
    linarith
  · have h' : Real.log n ≤ δ / 1028 * n := by
      have := mul_le_mul_of_nonneg_left hsqn (show 0 ≤ δ / 1028 by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h' (show 0 ≤ 24 * (n : ℝ) by positivity)
    have : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
    linarith

/-- `−γ − ln 2 − ln 20 + δ ≤ 0` for `δ ≤ 1`. -/
theorem c0_add_le {δ : ℝ} (hδ : δ ≤ 1) :
    -Real.eulerMascheroniConstant - Real.log 2 - Real.log 20 + δ ≤ 0 := by
  have h20 : 1 < Real.log 20 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have := Real.one_half_lt_eulerMascheroniConstant
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- **Theorem 8.1 from PNT + Appendix B certificate** (paper §8.5): the two prime-number-theorem
facts and a step majorant on `[κ₁, κ₂]` (`κ₂ ≤ 6`) imply Theorem 8.1 for `κ = K/n ∈ [κ₁, κ₂]`
with `c(κ) = cfunB C κ`. -/
theorem thm81_of_stepMajorant
    (hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
    (hM : Tendsto (fun x : ℝ => mertensSum x - Real.log x) atTop
      (𝓝 (-Real.eulerMascheroniConstant - Real.log 2)))
    {κ₁ κ₂ : ℝ} (C : StepMajorant κ₁ κ₂) (hκ₂ : κ₂ ≤ 6) : Thm81On κ₁ κ₂ (cfunB C) := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨η, hη_def⟩ : ∃ η, η = ε * Real.log 2 := ⟨_, rfl⟩
  have hη : 0 < η := hη_def ▸ mul_pos hε hl2
  obtain ⟨H, hH_def⟩ : ∃ H, H = ∑ i : Fin C.M, (C.h i : ℝ) := ⟨_, rfl⟩
  have hH : 0 ≤ H := hH_def ▸ sum_nonneg fun i _ => by exact_mod_cast C.h_nonneg i
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = min (1 / 9 : ℝ) (η / (2 * (14 + 9 * H))) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ lt_min (by norm_num) (div_pos hη (by positivity))
  have hδ9 : δ ≤ 1 / 9 := hδ_def ▸ min_le_left _ _
  have hδη : δ * (14 + 9 * H) ≤ η / 2 := by
    have := min_le_right (1 / 9 : ℝ) (η / (2 * (14 + 9 * H)))
    rw [← hδ_def, le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨y0, _, hθa⟩ := theta_approx hθ hδ
  obtain ⟨C1, hC1, hθu⟩ := theta_upper_all hθ hδ
  obtain ⟨C2, hC2, hpl⟩ := sum_mul_log_le hθ hδ
  obtain ⟨x0, hx0⟩ := mertens_upper hM hδ
  obtain ⟨NL, hNL⟩ := log_le_eps_sqrt (δ := δ / 1028) (by positivity)
  obtain ⟨B, hB_def⟩ : ∃ B, B = 30 * C1 + 2 * C2 + 78 * C.Csum * C.M := ⟨_, rfl⟩
  have hB : 0 ≤ B := by have := C.Csum_nonneg; rw [hB_def]; positivity
  refine ⟨2400 + NL + ⌈20 * y0⌉₊ + ⌈20 * x0⌉₊ + ⌈2 * B / η⌉₊, ?_⟩
  intro n K hn hodd hκ1 hκ2 S hS
  have hn2400 : 2400 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnr : (2400 : ℝ) ≤ n := by exact_mod_cast hn2400
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0n : 20 * y0 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈20 * y0⌉₊ ≤ n by omega))
  have hx0n : 20 * x0 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈20 * x0⌉₊ ≤ n by omega))
  have hBn : 2 * B / η ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2 * B / η⌉₊ ≤ n by omega))
  obtain ⟨κ, hκ_def⟩ : ∃ κ, κ = (K : ℝ) / n := ⟨_, rfl⟩
  rw [← hκ_def] at hκ1 hκ2 ⊢
  have hKk : (K : ℝ) = κ * n := by rw [hκ_def]; field_simp
  have hκ0 : 0 ≤ κ := by rw [hκ_def]; positivity
  have hκ6 : κ ≤ 6 := hκ2.trans hκ₂
  have hK6 : K ≤ 6 * n := by
    have : (K : ℝ) ≤ 6 * n := by rw [hKk]; exact mul_le_mul_of_nonneg_right hκ6 hn0.le
    exact_mod_cast this
  obtain ⟨c0, hc0_def⟩ : ∃ c0, c0 = -Real.eulerMascheroniConstant - Real.log 2 - Real.log 20 :=
    ⟨_, rfl⟩
  obtain ⟨SH, hSH_def⟩ : ∃ SH,
      SH = ∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc) := ⟨_, rfl⟩
  have hlhs : ∑ p ∈ S, (TPplus p n K : ℝ) * Real.logb 2 p =
      (∑ p ∈ S, (TPplus p n K : ℝ) * Real.log p) / Real.log 2 := by
    rw [sum_div]; refine sum_congr rfl fun p _ => ?_; rw [Real.logb]; ring
  have hrhs : κ * (6 - κ) * (n : ℝ) ^ 2 * Real.logb 2 n + cfunB C κ * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2 =
      (κ * (6 - κ) * (n : ℝ) ^ 2 * Real.log n
        + (κ * (6 - κ) * c0 + SH + 5 * κ / 20 + 12.5 / 400) * (n : ℝ) ^ 2
        + η * (n : ℝ) ^ 2) / Real.log 2 := by
    rw [Real.logb, cfunB, hη_def, hc0_def, hSH_def]; field_simp
  rw [hlhs, hrhs]
  refine div_le_div_of_nonneg_right ?_ hl2.le
  refine (sum_S_le_oddPr S hS).trans ?_
  rw [← sum_filter_add_sum_filter_not (oddPr n) (fun p => 20 * p ≤ n)]
  have h1 := sum_small_le hK6
  have h2 := sum_large_le C hodd hn2400 (hκ_def ▸ hκ1) (hκ_def ▸ hκ2)
  have hE1 := sum_sqrtRange_le (K := K) hn1 hK6
  have hmert : mertensSum ((n : ℝ) / 20) ≤ Real.log n + c0 + δ := by
    have := hx0 ((n : ℝ) / 20) (by linarith)
    rw [Real.log_div (by positivity) (by norm_num)] at this
    rw [hc0_def]; linarith
  have hc0 : c0 + δ ≤ 0 := hc0_def ▸ c0_add_le (by linarith)
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hmain := main_term_le hn0 hKk hκ0 hκ6 hmert hc0 hL0 hδ.le
  obtain ⟨hE1', hLn⟩ := log_errors_le hδ.le (by exact_mod_cast hn1) (hNL n (by omega))
  have hE2 := prop85_errors_le (n := n) hn0 hKk hκ6 hδ.le hC1 hC2 hθu hpl
  have hcells := cells_le C hδ.le hδ9 hθa hn0 hy0n
  rw [← hSH_def, ← hH_def] at hcells
  have hBn' : B * n ≤ η / 2 * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hη] at hBn
    have := mul_le_mul_of_nonneg_right hBn hn0.le
    linarith
  have hδn : δ * (14 + 9 * H) * (n : ℝ) ^ 2 ≤ η / 2 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hδη (by positivity)
  have : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
  rw [hB_def] at hBn'
  linarith


end Hankel2.Fam3
