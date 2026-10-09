import RequestProject.TwoAdic.LeafBound
import RequestProject.TwoAdic.TreeFactor

/-!
# Small primes: decomposition of `∑ s_k D_k − penalty` by levels and classes

For an odd prime `ℓ` and a profile `s`, write, at level `ℓ^j` and residue `r` modulo `M = ℓ^j`:

* `cls n M r`: the nodes `k ≡ r (mod M)`, `N = #cls`;
* `zc n M r`: the number of zeros `z` with `M ∣ 2(−k − z)` for `k ≡ r`;
* `Ecl q n M r s = ∑_{k∈cls} s_k q (N − 1 − z) − (S² − ∑_{k∈cls} s_k²)`, `S = ∑_{k ∈ cls} s_k`.

**`sum_D_sub_penalty`**: `∑_k s_k D_k − penalty(s) = ∑_{1 ≤ j ≤ 3n+1} ∑_{r < ℓ^j} Ecl q n ℓ^j r s`,
because `v_ℓ(x) = #{1 ≤ j ≤ 3n+1 : ℓ^j ∣ x}` for `0 < |x| ≤ 4n − 1` (`padicValInt_eq_sum_levels`).
-/

open Finset

namespace TwoAdicWin.Lev

open Dom Leaf

/-- The nodes in the class of `r` modulo `M`. -/
def cls (n M r : ℕ) : Finset (Fin (2 * R n + 1)) :=
  univ.filter fun i => nodeOf n i % (M : ℤ) = r

/-- The residue of the node `i` modulo `M`. -/
def res (n M : ℕ) (i : Fin (2 * R n + 1)) : ℕ := (nodeOf n i % (M : ℤ)).toNat

/-- The number of zeros `z` with `M ∣ 2(−k − z)` for `k ≡ r (mod M)`. -/
def zc (n M r : ℕ) : ℕ := ((range n).filter fun j : ℕ => (M : ℤ) ∣ (2 * (j : ℤ) + 1 - n) - 2 * r).card

/-- The contribution of a class: `∑_{k∈c} s_k q (N − 1 − z) − (S² − ∑_{k∈c} s_k²)`. -/
def Ecl (q n M r : ℕ) (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ i ∈ cls n M r, (s i : ℤ) * q * (((cls n M r).card : ℤ) - 1 - zc n M r) -
    (((∑ i ∈ cls n M r, s i : ℕ) : ℤ) ^ 2 - ((∑ i ∈ cls n M r, s i ^ 2 : ℕ) : ℤ))

variable {n : ℕ}

theorem res_lt {M : ℕ} (hM : 0 < M) (i : Fin (2 * R n + 1)) : res n M i < M := by
  unfold res
  have h1 := Int.emod_nonneg (nodeOf n i) (show (M : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos (nodeOf n i) (show (0 : ℤ) < M by omega)
  omega

theorem mem_cls_res {M : ℕ} (hM : 0 < M) (i : Fin (2 * R n + 1)) : i ∈ cls n M (res n M i) := by
  unfold cls res
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  have h1 := Int.emod_nonneg (nodeOf n i) (show (M : ℤ) ≠ 0 by omega)
  omega

theorem mem_cls_iff {M : ℕ} (hM : 0 < M) (i i' : Fin (2 * R n + 1)) :
    i' ∈ cls n M (res n M i) ↔ (M : ℤ) ∣ nodeOf n i' - nodeOf n i := by
  unfold cls res
  rw [mem_filter]
  have h1 := Int.emod_nonneg (nodeOf n i) (show (M : ℤ) ≠ 0 by omega)
  rw [Int.toNat_of_nonneg h1]
  simp only [mem_univ, true_and]
  constructor
  · intro h; exact Int.modEq_iff_dvd.1 (Int.ModEq.symm h)
  · intro h; exact Int.ModEq.symm (Int.modEq_iff_dvd.2 h)

end TwoAdicWin.Lev
