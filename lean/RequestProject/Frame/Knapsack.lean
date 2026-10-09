import Mathlib

/-!
# The continuous knapsack `ψ̃` (II, Lemma 5.3)

For a finite list of weights `α = (α_k)` and `τ ∈ ℝ`,
`ψ̃(α, τ) = sup_{σ ∈ [0,1]^α} [∑_k (α_k − τ) σ_k − (∑_k σ_k)²]` (`knap`).

The certificate checker does not evaluate `ψ̃` by the greedy rule; it uses the **weak duality**
bound (`knap_le_dual`): for every real `μ`,

  `ψ̃(α, τ) ≤ ∑_k (α_k − τ − μ)⁺ + μ²/4`,

since `(α_k − τ) σ_k ≤ (α_k − τ − μ)⁺ + μ σ_k` for `σ_k ∈ [0,1]` and `μS − S² ≤ μ²/4`.  (By convex
duality the minimum over `μ` equals `ψ̃`, and at the optimal `μ` it coincides with the greedy value
of `check_uniform.py`; only the inequality is needed.)  Also `ψ̃ ≥ 0` (`σ = 0`) and the dual bound is
monotone in the weights (`dualB_mono`).
-/

open Finset

namespace PadicWin

/-- The objective `∑_k (α_k − τ) σ_k − (∑_k σ_k)²`. -/
noncomputable def knapObj (α : List ℝ) (τ : ℝ) (σ : Fin α.length → ℝ) : ℝ :=
  ∑ k, (α.get k - τ) * σ k - (∑ k, σ k) ^ 2

/-- **The continuous knapsack** `ψ̃(α, τ) = sup_{σ ∈ [0,1]^α} knapObj`. -/
noncomputable def knap (α : List ℝ) (τ : ℝ) : ℝ :=
  sSup {v | ∃ σ : Fin α.length → ℝ, (∀ k, 0 ≤ σ k ∧ σ k ≤ 1) ∧ v = knapObj α τ σ}

/-- The dual bound `∑_k (α_k − τ − μ)⁺ + μ²/4`. -/
noncomputable def dualB (α : List ℝ) (τ μ : ℝ) : ℝ :=
  (α.map fun a => max 0 (a - τ - μ)).sum + μ ^ 2 / 4

theorem sum_get_eq_sum_map (α : List ℝ) (f : ℝ → ℝ) :
    ∑ k : Fin α.length, f (α.get k) = (α.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get <;> simp

theorem knapObj_le_dual (α : List ℝ) (τ μ : ℝ) (σ : Fin α.length → ℝ)
    (hσ : ∀ k, 0 ≤ σ k ∧ σ k ≤ 1) : knapObj α τ σ ≤ dualB α τ μ := by
  have h1 : ∀ k, (α.get k - τ) * σ k ≤ max 0 (α.get k - τ - μ) + μ * σ k := by
    intro k
    obtain ⟨h0, h1⟩ := hσ k
    rcases le_total 0 (α.get k - τ - μ) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have h2 : ∑ k, (α.get k - τ) * σ k ≤ ∑ k, max 0 (α.get k - τ - μ) + μ * ∑ k, σ k := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_le_sum fun k _ => h1 k
  rw [knapObj, dualB, ← sum_get_eq_sum_map α (fun a => max 0 (a - τ - μ))]
  nlinarith [sq_nonneg (μ / 2 - ∑ k, σ k)]

theorem knap_set_nonempty (α : List ℝ) (τ : ℝ) :
    {v | ∃ σ : Fin α.length → ℝ, (∀ k, 0 ≤ σ k ∧ σ k ≤ 1) ∧ v = knapObj α τ σ}.Nonempty :=
  ⟨_, fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩, rfl⟩

theorem knap_set_bdd (α : List ℝ) (τ : ℝ) :
    BddAbove {v | ∃ σ : Fin α.length → ℝ, (∀ k, 0 ≤ σ k ∧ σ k ≤ 1) ∧ v = knapObj α τ σ} :=
  ⟨dualB α τ 0, by rintro v ⟨σ, hσ, rfl⟩; exact knapObj_le_dual α τ 0 σ hσ⟩

/-- **Weak duality**: `ψ̃(α, τ) ≤ ∑_k (α_k − τ − μ)⁺ + μ²/4` for every `μ`. -/
theorem knap_le_dual (α : List ℝ) (τ μ : ℝ) : knap α τ ≤ dualB α τ μ :=
  csSup_le (knap_set_nonempty α τ) (by rintro v ⟨σ, hσ, rfl⟩; exact knapObj_le_dual α τ μ σ hσ)

/-- `ψ̃ ≥ 0` (take `σ = 0`). -/
theorem knap_nonneg (α : List ℝ) (τ : ℝ) : 0 ≤ knap α τ := by
  refine le_csSup (knap_set_bdd α τ) ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
  simp [knapObj]

/-- The dual bound is monotone in the weights (pointwise, for lists of equal shape). -/
theorem dualB_map_mono {ι : Type*} (L : List ι) (f g : ι → ℝ) (hfg : ∀ x ∈ L, f x ≤ g x)
    (τ μ : ℝ) : dualB (L.map f) τ μ ≤ dualB (L.map g) τ μ := by
  unfold dualB
  simp only [List.map_map]
  gcongr
  refine List.sum_le_sum fun x hx => ?_
  simp only [Function.comp]
  exact max_le_max le_rfl (by linarith [hfg x hx])

end PadicWin
