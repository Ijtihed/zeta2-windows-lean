import Mathlib

/-!
# Covering the residues by arcs

Let `0 ≤ F ≤ K_b` on the residues `r < ℓ`, and let `x₀ ≤ x₁ ≤ ⋯ ≤ x_m` (rational positions, with
`x_m ≥ ℓ`) be the ends of a chain of arcs with values `v_i ≥ 0` such that `F r ≤ v_i` for every
residue with `x_{i−1} + 1 ≤ r ≤ x_i − 1`.  Then (**`cover_sum`**)

  `∑_{r < ℓ, r > x₀ − 1} F r ≤ ∑_i v_i (x_i − x_{i−1}) + 2 m K_b`:

the residues within distance `< 1` of a left end are at most two per arc, and an arc contains at most
`x_i − x_{i−1}` interior residues.
-/

open Finset

namespace TwoAdicWin.Asm

/-- At most two residues lie in `(x − 1, x + 1)`. -/
theorem card_near_le (ℓ : ℕ) (x : ℚ) :
    ((range ℓ).filter fun r : ℕ => x - 1 < r ∧ (r : ℚ) < x + 1).card ≤ 2 := by
  have hsub : (range ℓ).filter (fun r : ℕ => x - 1 < r ∧ (r : ℚ) < x + 1) ⊆
      ({(⌊x⌋).toNat, (⌊x⌋ + 1).toNat} : Finset ℕ) := by
    intro r hr
    simp only [mem_filter] at hr
    obtain ⟨_, h1, h2⟩ := hr
    have a1 : ⌊x⌋ ≤ (r : ℤ) := by
      have := Int.floor_le x
      have h : ((⌊x⌋ - 1 : ℤ) : ℚ) < ((r : ℤ) : ℚ) := by push_cast; linarith
      have : (⌊x⌋ - 1 : ℤ) < (r : ℤ) := by exact_mod_cast h
      omega
    have a2 : (r : ℤ) ≤ ⌊x⌋ + 1 := by
      have := Int.lt_floor_add_one x
      have h : ((r : ℤ) : ℚ) < ((⌊x⌋ + 2 : ℤ) : ℚ) := by push_cast; linarith
      have : (r : ℤ) < ⌊x⌋ + 2 := by exact_mod_cast h
      omega
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hsub).trans card_le_two

/-- At most `y − x` residues lie in `[x + 1, y − 1]` (for `x ≤ y`). -/
theorem card_mid_le (ℓ : ℕ) {x y : ℚ} (hxy : x ≤ y) :
    (((range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1).card : ℚ) ≤ y - x := by
  have hle : ((range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1).card ≤
      (Icc ⌈x + 1⌉ ⌊y - 1⌋).card := by
    refine card_le_card_of_injOn (fun r : ℕ => (r : ℤ)) (fun r hr => ?_) ?_
    · simp only [coe_filter, Set.mem_setOf_eq] at hr
      simp only [coe_Icc, Set.mem_Icc]
      refine ⟨Int.ceil_le.2 (by push_cast; exact hr.2.1), Int.le_floor.2 (by push_cast; exact hr.2.2)⟩
    · intro a _ b _ h; simpa using h
  rw [Int.card_Icc] at hle
  by_cases h : ⌊y - 1⌋ + 1 - ⌈x + 1⌉ ≤ 0
  · rw [Int.toNat_of_nonpos h] at hle
    have : ((range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1).card = 0 := by omega
    rw [this]; push_cast; linarith
  · push_neg at h
    have h1 : (((range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1).card : ℤ) ≤
        ⌊y - 1⌋ + 1 - ⌈x + 1⌉ := by
      have := Int.toNat_of_nonneg h.le
      omega
    have h2 : ((⌊y - 1⌋ + 1 - ⌈x + 1⌉ : ℤ) : ℚ) ≤ y - x - 1 := by
      push_cast
      linarith [Int.floor_le (y - 1), Int.le_ceil (x + 1)]
    have h3 : ((((range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1).card : ℤ) : ℚ) ≤
        ((⌊y - 1⌋ + 1 - ⌈x + 1⌉ : ℤ) : ℚ) := by exact_mod_cast h1
    push_cast at h2 h3
    linarith

/-- A chain of arcs `(right end, value)` starting at `x`, valid for `F`. -/
def ChainV (ℓ : ℕ) (F : ℕ → ℝ) : ℚ → List (ℚ × ℝ) → Prop
  | x, [] => (ℓ : ℚ) ≤ x
  | x, (y, v) :: rest => x ≤ y ∧ 0 ≤ v ∧
      (∀ r : ℕ, r < ℓ → x + 1 ≤ (r : ℚ) → (r : ℚ) ≤ y - 1 → F r ≤ v) ∧ ChainV ℓ F y rest

/-- `∑_i v_i (x_i − x_{i−1})`. -/
noncomputable def arcSum : ℚ → List (ℚ × ℝ) → ℝ
  | _, [] => 0
  | x, (y, v) :: rest => v * ((y - x : ℚ) : ℝ) + arcSum y rest

/-- **Covering the residues by a chain of arcs.** -/
theorem cover_sum (ℓ : ℕ) (F : ℕ → ℝ) (Kb : ℝ) (hF0 : ∀ r, 0 ≤ F r)
    (hFK : ∀ r < ℓ, F r ≤ Kb) (hKb : 0 ≤ Kb) :
    ∀ (arcs : List (ℚ × ℝ)) (x : ℚ), ChainV ℓ F x arcs →
      ∑ r ∈ (range ℓ).filter (fun r : ℕ => x - 1 < r), F r ≤ arcSum x arcs + 2 * arcs.length * Kb
  | [], x, h => by
    simp only [ChainV] at h
    have : (range ℓ).filter (fun r : ℕ => x - 1 < r) = ∅ := by
      ext r
      simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and, not_lt]
      intro hr
      have : (r : ℚ) + 1 ≤ ℓ := by exact_mod_cast hr
      linarith
    rw [this]; simp [arcSum]
  | (y, v) :: rest, x, h => by
    obtain ⟨hxy, hv, hF, hrest⟩ := h
    have ih := cover_sum ℓ F Kb hF0 hFK hKb rest y hrest
    set A := (range ℓ).filter (fun r : ℕ => x - 1 < r)
    -- split `A` into near / mid / rest
    rw [← sum_filter_add_sum_filter_not A (fun r : ℕ => (r : ℚ) < x + 1)]
    rw [← sum_filter_add_sum_filter_not (A.filter fun r : ℕ => ¬ (r : ℚ) < x + 1)
      (fun r : ℕ => (r : ℚ) ≤ y - 1)]
    -- near
    have h1 : ∑ r ∈ A.filter (fun r : ℕ => (r : ℚ) < x + 1), F r ≤ 2 * Kb := by
      have hsub : A.filter (fun r : ℕ => (r : ℚ) < x + 1) =
          (range ℓ).filter fun r : ℕ => x - 1 < r ∧ (r : ℚ) < x + 1 := by
        rw [filter_filter]
      rw [hsub]
      refine (sum_le_card_nsmul _ _ Kb fun r hr => hFK r (mem_range.1 (mem_filter.1 hr).1)).trans ?_
      rw [nsmul_eq_mul]
      have := card_near_le ℓ x
      have : (((range ℓ).filter fun r : ℕ => x - 1 < r ∧ (r : ℚ) < x + 1).card : ℝ) ≤ 2 := by
        exact_mod_cast this
      nlinarith
    -- mid
    have h2 : ∑ r ∈ (A.filter fun r : ℕ => ¬ (r : ℚ) < x + 1).filter (fun r : ℕ => (r : ℚ) ≤ y - 1),
        F r ≤ v * ((y - x : ℚ) : ℝ) := by
      set B := (A.filter fun r : ℕ => ¬ (r : ℚ) < x + 1).filter (fun r : ℕ => (r : ℚ) ≤ y - 1)
      have hB : B ⊆ (range ℓ).filter fun r : ℕ => x + 1 ≤ r ∧ (r : ℚ) ≤ y - 1 := by
        intro r hr
        simp only [B, A, mem_filter, not_lt] at hr ⊢
        exact ⟨hr.1.1.1, hr.1.2, hr.2⟩
      refine (sum_le_card_nsmul _ _ v fun r hr => ?_).trans ?_
      · have := hB hr
        simp only [mem_filter, mem_range] at this
        exact hF r this.1 this.2.1 this.2.2
      · rw [nsmul_eq_mul]
        have hc := card_mid_le ℓ hxy
        have hc' : (B.card : ℚ) ≤ y - x := (by exact_mod_cast card_le_card hB : (B.card : ℚ) ≤ _).trans hc
        have : (B.card : ℝ) ≤ ((y - x : ℚ) : ℝ) := by exact_mod_cast hc'
        nlinarith
    -- rest
    have h3 : ∑ r ∈ (A.filter fun r : ℕ => ¬ (r : ℚ) < x + 1).filter (fun r : ℕ => ¬ (r : ℚ) ≤ y - 1),
        F r ≤ ∑ r ∈ (range ℓ).filter (fun r : ℕ => y - 1 < r), F r := by
      refine sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun r _ _ => hF0 r)
      simp only [A, mem_filter, not_lt, not_le] at hr ⊢
      exact ⟨hr.1.1.1, hr.2⟩
    simp only [arcSum, List.length_cons]
    push_cast at h2 ⊢
    linarith

end TwoAdicWin.Asm
