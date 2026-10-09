import RequestProject.TwoAdic.AsmLeaf1
import RequestProject.TwoAdic.Levels
import RequestProject.TwoAdic.TreePenalty

/-!
# Class decomposition of the tree bound at a single-level prime (II, Lemma 5.3)

For a single-level odd prime `ℓ` (`4n < ℓ²`) and a profile `s`:

* `penalty_ge_level1`: the penalty is at least its first level
  `∑_{c < ℓ} (S_c² − ∑_{k ∈ c} s_k²)`;
* `Ncl_eq_card`, `Zcl_eq_zc`: `N_c` and `z_c` only depend on the class;
* **`tree_sum_le_classes`**: `∑_k f_ℓ(k, s_k) − penalty ≤ ∑_c [∑_{k ∈ c} (g(k, s_k) + s_k²) − S_c²]`
  (`g = gval`, the leaf values of `AsmLeaf1`);
* `TPplus_le_of`: turning a bound for every profile into a bound for `T⁺_ℓ`.
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev

variable {q d n ℓ : ℕ}

/-- `∑_i F i = ∑_{c < M} ∑_{i ∈ cls c} F i`. -/
theorem sum_eq_sum_cls {M : ℕ} (hM : 0 < M) {β : Type*} [AddCommMonoid β]
    (F : Fin (2 * R n + 1) → β) :
    ∑ i, F i = ∑ c ∈ range M, ∑ i ∈ cls n M c, F i := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range M) (g := res n M)
    (fun i _ => mem_range.2 (res_lt hM i))]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  ext i
  simp only [cls, res, mem_filter, mem_univ, true_and]
  have h1 := Int.emod_nonneg (nodeOf n i) (show (M : ℤ) ≠ 0 by omega)
  omega

theorem sq_sum_ge_sum_sq {ι : Type*} (A : Finset ι) (s : ι → ℕ) :
    ∑ i ∈ A, s i ^ 2 ≤ (∑ i ∈ A, s i) ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [sum_insert ha, sum_insert ha]
    nlinarith [Nat.zero_le (s a * ∑ i ∈ A, s i)]

/-- The first level of the penalty. -/
def penL1 (n ℓ : ℕ) (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ c ∈ range ℓ, (((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2 - ((∑ i ∈ cls n ℓ c, s i ^ 2 : ℕ) : ℤ))

theorem penalty_ge_level1 (s : Fin (2 * R n + 1) → ℕ) : penL1 n ℓ s ≤ penalty n ℓ s := by
  unfold penalty
  have hnn : ∀ j ∈ Icc 1 (2 * R n + 1), 0 ≤ ∑ c ∈ range (ℓ ^ j),
      (((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i : ℕ) : ℤ) ^ 2
        - ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i ^ 2 : ℕ) : ℤ)) := by
    intro j _
    refine sum_nonneg fun c _ => ?_
    have := sq_sum_ge_sum_sq (univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c)) s
    have h' : ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i ^ 2 : ℕ) : ℤ) ≤
        ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast this
    linarith
  have h1 : (1 : ℕ) ∈ Icc 1 (2 * R n + 1) := by simp
  refine le_trans (le_of_eq ?_) (single_le_sum hnn h1)
  unfold penL1
  simp only [pow_one, cls]

/-! ### `N_c` and `z_c` depend only on the class -/

theorem Ncl_eq_card {c : ℕ} {i : Fin (2 * R n + 1)} (hi : i ∈ cls n ℓ c) :
    Ncl n ℓ (nodeOf n i) = (cls n ℓ c).card := by
  unfold Ncl cls
  rw [card_filter, card_filter, sum_nodes_eq' n]
  simp only [cls, mem_filter, mem_univ, true_and] at hi
  refine sum_congr rfl fun i' _ => ?_
  have : (ℓ : ℤ) ∣ nodeOf n i' - nodeOf n i ↔ nodeOf n i' % (ℓ : ℤ) = c := by
    rw [← hi]
    constructor
    · intro h; exact (Int.modEq_iff_dvd.2 h).symm
    · intro h; exact Int.modEq_iff_dvd.1 (Int.ModEq.symm h)
  simp only [this]

theorem Zcl_eq_zc {c : ℕ} {i : Fin (2 * R n + 1)} (hi : i ∈ cls n ℓ c) :
    Zcl n ℓ (nodeOf n i) = zc n ℓ c := by
  unfold Zcl zc
  simp only [cls, mem_filter, mem_univ, true_and] at hi
  congr 1
  refine filter_congr fun j _ => ?_
  have hk := Int.emod_add_ediv (nodeOf n i) ℓ
  rw [hi] at hk
  unfold ez
  have e : 2 * (j : ℤ) + 1 - 2 * nodeOf n i - n =
      ((2 * (j : ℤ) + 1 - n) - 2 * c) + ℓ * (-(2 * (nodeOf n i / ℓ))) := by linarith
  rw [e, Int.dvd_add_left (dvd_mul_right _ _)]

/-! ### The tree bound by classes -/

theorem fP_sum_le [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (hsl : 4 * n < ℓ ^ 2) (s : Fin (2 * R n + 1) → ℕ) :
    ∑ i, fP q d n ℓ (nodeOf n i) (s i) ≤ ((∑ i, gval q d n ℓ (nodeOf n i) (s i) : ℤ) : WithBot ℤ) := by
  rw [WithBot.coe_sum]
  exact sum_le_sum fun i _ => fP_le_single hn hn1 h2 hsl (nodeOf_mem_nodes' n i) _

/-- **The tree bound by classes** at a single-level prime. -/
theorem tree_sum_le_classes [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (hsl : 4 * n < ℓ ^ 2) (s : Fin (2 * R n + 1) → ℕ) :
    (∑ i, fP q d n ℓ (nodeOf n i) (s i)) + (((-penalty n ℓ s : ℤ)) : WithBot ℤ) ≤
      ((∑ c ∈ range ℓ, (∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) -
        ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2) : ℤ) : WithBot ℤ) := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  refine (add_le_add (fP_sum_le hn hn1 h2 hsl s) le_rfl).trans ?_
  rw [← WithBot.coe_add]
  refine WithBot.coe_le_coe.2 ?_
  have hpen := penalty_ge_level1 (ℓ := ℓ) s
  have e1 := sum_eq_sum_cls (n := n) hℓ0 (fun i => gval q d n ℓ (nodeOf n i) (s i))
  have e2 : penL1 n ℓ s = ∑ c ∈ range ℓ, (((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2 -
      ∑ i ∈ cls n ℓ c, (s i : ℤ) ^ 2) := by
    unfold penL1; push_cast; rfl
  rw [e1]
  have : ∑ c ∈ range ℓ, (∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) -
      ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2) =
      ∑ c ∈ range ℓ, ∑ i ∈ cls n ℓ c, gval q d n ℓ (nodeOf n i) (s i) - penL1 n ℓ s := by
    rw [e2, ← sum_sub_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_add_distrib]; ring
  rw [this]
  linarith

/-- From a bound for every profile to a bound for `T⁺_ℓ`. -/
theorem TPplus_le_of {K : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ s ∈ profiles q n K, ∃ z : ℤ,
      (∑ i, fP q d n ℓ (nodeOf n i) (s i)) + (((-penalty n ℓ s : ℤ)) : WithBot ℤ) ≤ (z : WithBot ℤ) ∧
        (z : ℝ) ≤ B) :
    (TPplus q d n ℓ K : ℝ) ≤ B := by
  have hT : TP q d n ℓ K ≤ ((⌊B⌋ : ℤ) : WithBot ℤ) := by
    unfold TP
    refine Finset.sup_le fun s hs => ?_
    obtain ⟨z, hz, hzB⟩ := h s hs
    refine hz.trans (WithBot.coe_le_coe.2 ?_)
    exact Int.le_floor.2 hzB
  have hfl : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.2 hB
  unfold TPplus
  have hmax : max (TP q d n ℓ K) 0 ≤ ((⌊B⌋ : ℤ) : WithBot ℤ) :=
    max_le hT (by exact_mod_cast hfl)
  induction h' : max (TP q d n ℓ K) 0 using WithBot.recBotCoe with
  | bot =>
    have : (0 : WithBot ℤ) ≤ max (TP q d n ℓ K) 0 := le_max_right _ _
    rw [h'] at this; exact absurd this (by simp)
  | coe t =>
    rw [h'] at hmax
    simp only [WithBot.unbotD_coe]
    have ht : t ≤ ⌊B⌋ := by exact_mod_cast hmax
    have : (t : ℝ) ≤ ⌊B⌋ := by exact_mod_cast ht
    exact this.trans (Int.floor_le B)

end TwoAdicWin.Asm
