import RequestProject.TwoAdic.NVNodes
import RequestProject.TwoAdic.InputDefs
import RequestProject.Frame.PSVal

/-!
# II, Lemma 6.1 (node structure modulo `ℓ = 2n + 1`)

Hypotheses of II, Theorem 6.4 (`Hyp`): `(q, d)` admissible, `n` even, `ℓ = 2n + 1` prime,
`ℓ > q + d + 1`.  With `m = n/2` (so the nodes are `|k| ≤ 3m`):

* the affected set `𝒜 = {n + 1 ≤ |k| ≤ 3m}` (`aff`) has `n` elements (`card_aff`);
* every node `k` with `m + 1 ≤ |k|` has the partner (mate) `k ∓ ℓ` (`mate`), a node, and it is the
  only other node congruent to `k` modulo `ℓ` (`mate_spec`); the mate of an affected node is a partner
  (`m + 1 ≤ |k'| ≤ n`) and vice versa;
* the nodes with `|k| ≤ m` have no congruent node (`small_no_mate`); the affected nodes are pairwise
  incongruent (`aff_inj_mod`);
* for every node `k` with `m + 1 ≤ |k|` exactly one zero `z_j` has `ℓ ∣ 2(−k − z_j)`, and then
  `2(−k − z_j) = ∓ℓ` (`zero_spec`; `ez n j k = 2(−k − z_j) = 2j + 1 − 2k − n`).
-/

open Finset

namespace TwoAdicWin.Dom

/-- The hypotheses of II, Theorem 6.4. -/
structure Hyp (q d n ℓ : ℕ) : Prop where
  adm : Admissible q d
  even : Even n
  hℓ : ℓ = 2 * n + 1
  prime : ℓ.Prime
  big : q + d + 1 < ℓ

theorem int_dvd_cases {ℓ : ℕ} {x : ℤ} (h : (ℓ : ℤ) ∣ x) (h1 : -(2 * (ℓ : ℤ)) < x)
    (h2 : x < 2 * ℓ) : x = 0 ∨ x = ℓ ∨ x = -ℓ := by
  obtain ⟨t, rfl⟩ := h
  have : -2 < t := by
    by_contra hc; push_neg at hc; nlinarith
  have : t < 2 := by
    by_contra hc; push_neg at hc; nlinarith
  interval_cases t <;> simp

variable {q d n ℓ : ℕ}

theorem Hyp.n_eq (h : Hyp q d n ℓ) : n = 2 * (n / 2) := by
  obtain ⟨m, hm⟩ := h.even; omega

theorem Hyp.R_eq (h : Hyp q d n ℓ) : R n = 3 * (n / 2) := by
  have := h.n_eq; unfold R; omega

theorem Hyp.ne_two (h : Hyp q d n ℓ) : ℓ ≠ 2 := by have := h.hℓ; omega

theorem Hyp.n_pos (h : Hyp q d n ℓ) : 2 ≤ n := by
  have := h.adm.1; have := h.big; have := h.hℓ; have := h.n_eq; omega

theorem mem_nodes_iff {k : ℤ} : k ∈ nodes n ↔ -(R n : ℤ) ≤ k ∧ k ≤ R n := by
  simp [nodes]

/-- The affected nodes `n + 1 ≤ |k| ≤ 3n/2`. -/
def aff (n : ℕ) : Finset ℤ := (nodes n).filter (fun k => n + 1 ≤ k.natAbs)

/-- The mate (partner) `k ∓ ℓ` of a node. -/
def mate (ℓ : ℕ) (k : ℤ) : ℤ := if 0 < k then k - ℓ else k + ℓ

/-- `ez n j k = 2(−k − z_j) = 2j + 1 − 2k − n`. -/
def ez (n j : ℕ) (k : ℤ) : ℤ := 2 * j + 1 - 2 * k - n

theorem mem_aff_iff {k : ℤ} : k ∈ aff n ↔ k ∈ nodes n ∧ n + 1 ≤ k.natAbs := by
  simp [aff]

theorem mate_spec (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs) :
    mate ℓ k ∈ nodes n ∧ mate ℓ k ≠ k ∧ (k - mate ℓ k = ℓ ∨ k - mate ℓ k = -ℓ) ∧
      ∀ k' ∈ nodes n, (ℓ : ℤ) ∣ k' - k → k' = k ∨ k' = mate ℓ k := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_nodes_iff, hR] at hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_nodes_iff, hR]; unfold mate; split_ifs <;> omega
  · unfold mate; split_ifs <;> omega
  · unfold mate; split_ifs <;> omega
  · intro k' hk' hd
    rw [mem_nodes_iff, hR] at hk'
    rcases int_dvd_cases hd (by omega) (by omega) with h0 | h0 | h0 <;>
      · unfold mate; split_ifs <;> omega

theorem small_no_mate (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : k.natAbs ≤ n / 2) :
    ∀ k' ∈ nodes n, (ℓ : ℤ) ∣ k' - k → k' = k := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_nodes_iff, hR] at hk
  intro k' hk' hd
  rw [mem_nodes_iff, hR] at hk'
  rcases int_dvd_cases hd (by omega) (by omega) with h0 | h0 | h0 <;> omega

theorem mate_of_aff (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ aff n) :
    n / 2 + 1 ≤ (mate ℓ k).natAbs ∧ (mate ℓ k).natAbs ≤ n := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_aff_iff, mem_nodes_iff, hR] at hk
  unfold mate; split_ifs <;> omega

theorem mate_mem_aff (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs)
    (hk2 : k.natAbs ≤ n) : mate ℓ k ∈ aff n := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_nodes_iff, hR] at hk
  rw [mem_aff_iff, mem_nodes_iff, hR]
  unfold mate; split_ifs <;> omega

theorem mate_mate (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) :
    mate ℓ (mate ℓ k) = k := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_nodes_iff, hR] at hk
  unfold mate; split_ifs <;> omega

theorem aff_inj_mod (h : Hyp q d n ℓ) {k k' : ℤ} (hk : k ∈ aff n) (hk' : k' ∈ aff n)
    (hd : (ℓ : ℤ) ∣ k - k') : k = k' := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_aff_iff, mem_nodes_iff, hR] at hk hk'
  rcases int_dvd_cases hd (by omega) (by omega) with h0 | h0 | h0 <;> omega

theorem zero_spec (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs) :
    ∃ js < n, (ez n js k = ℓ ∨ ez n js k = -ℓ) ∧
      ∀ j < n, j ≠ js → ¬ (ℓ : ℤ) ∣ ez n j k := by
  have hn := h.n_eq
  have hR := h.R_eq
  have hl := h.hℓ
  rw [mem_nodes_iff, hR] at hk
  unfold ez
  by_cases hpos : 0 < k
  · refine ⟨(k - (n / 2 : ℕ) - 1).toNat, by omega, by omega, fun j hj hne hd => ?_⟩
    rcases int_dvd_cases hd (by omega) (by omega) with h0 | h0 | h0 <;> omega
  · refine ⟨(3 * (n / 2 : ℕ) + k).toNat, by omega, by omega, fun j hj hne hd => ?_⟩
    rcases int_dvd_cases hd (by omega) (by omega) with h0 | h0 | h0 <;> omega

theorem card_aff (h : Hyp q d n ℓ) : (aff n).card = n := by
  have hn := h.n_eq
  have hR := h.R_eq
  have e : aff n = Icc ((n : ℤ) + 1) (3 * (n / 2 : ℕ)) ∪ Icc (-(3 * (n / 2 : ℕ) : ℤ)) (-(n : ℤ) - 1) := by
    ext k
    rw [mem_aff_iff, mem_nodes_iff, hR, mem_union, mem_Icc, mem_Icc]
    omega
  rw [e, card_union_of_disjoint, Int.card_Icc, Int.card_Icc]
  · omega
  · rw [disjoint_left]
    intro k h1 h2
    rw [mem_Icc] at h1 h2
    omega

end TwoAdicWin.Dom
