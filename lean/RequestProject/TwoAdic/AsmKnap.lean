import RequestProject.Frame.Knapsack

/-!
# Lower bounds for the continuous knapsack with two weight classes (II, Lemma 5.3)

For the weight list `α = (a, …, a, b, …, b)` (`A` copies of `a`, `B` copies of `b`) and loads
`0 ≤ x ≤ A`, `0 ≤ y ≤ B`:

  `a x + b y − (x + y)² − τ (x + y) ≤ ψ̃(α, τ)`  (`le_knap_two`),

by spreading `x` evenly over the first `A` coordinates and `y` over the last `B`.  Also an upper
bound by the dual at `μ = 0` (`knap_le_sum_pos`).
-/

open Finset

namespace PadicWin

theorem sum_fin_append_replicate (A B : ℕ) (a b : ℝ) (g : ℝ → ℕ → ℝ) :
    ∑ k : Fin (List.replicate A a ++ List.replicate B b).length,
        g ((List.replicate A a ++ List.replicate B b).get k) (k : ℕ) =
      ∑ i ∈ range A, g a i + ∑ i ∈ range B, g b (A + i) := by
  have key : ∀ (L : List ℝ), ∑ k : Fin L.length, g (L.get k) k =
      ∑ i ∈ range L.length, g (L.getD i 0) i := by
    intro L
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (L.getD i 0) i)]
    refine Fintype.sum_congr _ _ fun k => ?_
    simp
  rw [key]
  simp only [List.length_append, List.length_replicate]
  rw [sum_range_add]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    congr 1
    simp [List.getElem?_append_left (by simp; omega : i < (List.replicate A a).length), hi]
  · refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    congr 1
    simp [hi]

/-- **Two weight classes**: `a x + b y − (x+y)² − τ(x+y) ≤ ψ̃((a)^A (b)^B, τ)`. -/
theorem le_knap_two (A B : ℕ) (a b τ x y : ℝ) (hx0 : 0 ≤ x) (hxA : x ≤ A) (hy0 : 0 ≤ y)
    (hyB : y ≤ B) :
    a * x + b * y - (x + y) ^ 2 - τ * (x + y) ≤
      knap (List.replicate A a ++ List.replicate B b) τ := by
  set α := List.replicate A a ++ List.replicate B b
  set σ : Fin α.length → ℝ := fun k => if (k : ℕ) < A then x / A else y / B
  have hσ : ∀ k, 0 ≤ σ k ∧ σ k ≤ 1 := by
    intro k
    simp only [σ]
    split_ifs
    · refine ⟨by positivity, ?_⟩
      rcases Nat.eq_zero_or_pos A with h0 | h0
      · simp [h0]
      · rw [div_le_one (by exact_mod_cast h0)]; exact hxA
    · refine ⟨by positivity, ?_⟩
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · simp [h0]
      · rw [div_le_one (by exact_mod_cast h0)]; exact hyB
  have hxA' : (A : ℝ) * (x / A) = x := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · simp [h0] at hxA ⊢; linarith
    · field_simp
  have hyB' : (B : ℝ) * (y / B) = y := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · simp [h0] at hyB ⊢; linarith
    · field_simp
  have h1 : ∑ k, (α.get k - τ) * σ k = (a - τ) * x + (b - τ) * y := by
    have := sum_fin_append_replicate A B a b
      (fun w i => (w - τ) * (if i < A then x / A else y / B))
    simp only at this
    rw [show (∑ k, (α.get k - τ) * σ k) = _ from this]
    have e1 : ∑ i ∈ range A, (a - τ) * (if i < A then x / A else y / B) =
        ∑ i ∈ range A, (a - τ) * (x / A) := sum_congr rfl fun i hi => by rw [if_pos (mem_range.1 hi)]
    have e2 : ∑ i ∈ range B, (b - τ) * (if A + i < A then x / A else y / B) =
        ∑ i ∈ range B, (b - τ) * (y / B) := sum_congr rfl fun i _ => by rw [if_neg (by omega)]
    rw [e1, e2]
    simp only [sum_const, card_range, nsmul_eq_mul]
    linear_combination (a - τ) * hxA' + (b - τ) * hyB'
  have h2 : ∑ k, σ k = x + y := by
    have := sum_fin_append_replicate A B a b (fun _ i => if i < A then x / A else y / B)
    simp only at this
    rw [show (∑ k, σ k) = _ from this]
    have e1 : ∑ i ∈ range A, (if i < A then x / A else y / B) =
        ∑ i ∈ range A, (x / A) := sum_congr rfl fun i hi => by rw [if_pos (mem_range.1 hi)]
    have e2 : ∑ i ∈ range B, (if A + i < A then x / A else y / B) =
        ∑ i ∈ range B, (y / B) := sum_congr rfl fun i _ => by rw [if_neg (by omega)]
    rw [e1, e2]
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [hxA', hyB']
  have hle : knapObj α τ σ ≤ knap α τ :=
    le_csSup (knap_set_bdd α τ) ⟨σ, hσ, rfl⟩
  unfold knapObj at hle
  rw [h1, h2] at hle
  linarith

/-- `ψ̃(α, τ) ≤ ∑_k (α_k − τ)⁺`. -/
theorem knap_le_sum_pos (α : List ℝ) (τ : ℝ) :
    knap α τ ≤ (α.map fun a => max 0 (a - τ)).sum := by
  have := knap_le_dual α τ 0
  simpa [dualB] using this

/-- `ψ̃` is antitone in `τ` on `τ ≥ 0`-independent grounds: `ψ̃(α, τ) ≤ ψ̃(α, τ')` for `τ' ≤ τ`. -/
theorem knap_anti (α : List ℝ) {τ τ' : ℝ} (h : τ' ≤ τ) : knap α τ ≤ knap α τ' := by
  refine csSup_le (knap_set_nonempty α τ) ?_
  rintro v ⟨σ, hσ, rfl⟩
  refine le_trans ?_ (le_csSup (knap_set_bdd α τ') ⟨σ, hσ, rfl⟩)
  unfold knapObj
  have : ∑ k, (α.get k - τ) * σ k ≤ ∑ k, (α.get k - τ') * σ k :=
    sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (by linarith) (hσ k).1
  linarith

end PadicWin
