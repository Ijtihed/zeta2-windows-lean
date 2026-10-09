import RequestProject.TwoAdic.AsmClass
import RequestProject.TwoAdic.AsmCount
import RequestProject.TwoAdic.AsmDual
import RequestProject.TwoAdic.AsmKnap
import RequestProject.TwoAdic.AsmArcs

/-!
# Single-level primes: middle primes and the homogeneous relaxation (II, Lemma 5.3)

For an odd prime `ℓ` with `4n < ℓ²`, `K = qn`, and admissible `(q, d)`:

* **`middle_bound`**:
  `T⁺_ℓ ≤ q² n (n + 1)/ℓ + (d + 2) q n + q² ℓ/4`.
  (No condition `ℓ ≤ εn` is needed: nodes with `μ = hs = 0` have `D_k = 0`.)
* **`relax_bound`** (II, Lemma 5.3, with weak duality at `λ = qτ`): for every `τ ≥ 0`,
  `T⁺_ℓ ≤ q² (τ n + ∑_{c < ℓ} ψ̃(α_c, τ))`, where `α_c` are the weights of the kept nodes of the class
  `c`: `(N − z) + (1 + δ)` for the hs nodes and `N − z` for the non-hs nodes if `μ = 1` and
  `N − z ≥ 1` (`classAlphas`, i.e. `alphasR` of the runs `Arc.runsOf N #hs z`).
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin

variable {q d n ℓ : ℕ}

/-- The number of hs nodes of the class `c`. -/
def nhs (n ℓ c : ℕ) : ℕ := ((cls n ℓ c).filter fun i => (ℓ : ℤ) ≤ 2 * |nodeOf n i| - 1).card

/-- The weights of the kept nodes of the class `c` (II, Lemma 5.3). -/
noncomputable def classAlphas (n ℓ : ℕ) (δ : ℝ) (c : ℕ) : List ℝ :=
  Cert.alphasR ⟨0, 0, Arc.runsOf (cls n ℓ c).card (nhs n ℓ c) (zc n ℓ c)⟩ δ

theorem alphasR_runsOf (m0 m1 : ℚ) (N nh z : ℕ) (δ : ℝ) :
    Cert.alphasR ⟨m0, m1, Arc.runsOf N nh z⟩ δ =
      List.replicate nh (((N : ℤ) - z : ℤ) + (1 + δ) : ℝ) ++
        List.replicate (if (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z then N - nh else 0)
          (((N : ℤ) - z : ℤ) : ℝ) := by
  unfold Arc.runsOf
  by_cases hk : (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z
  · simp only [if_pos hk]
    by_cases h0 : nh = 0 ∧ N - nh = 0
    · rw [if_pos h0]; have : N = 0 := by omega
      simp [Cert.alphasR, h0.1, this]
    · rw [if_neg h0]; simp [Cert.alphasR, Cert.alphaR, Cert.hsQ]
  · simp only [if_neg hk]
    by_cases h0 : nh = 0
    · simp [Cert.alphasR, h0]
    · rw [if_neg (by tauto)]; simp [Cert.alphasR, Cert.alphaR, Cert.hsQ]

end TwoAdicWin.Asm
