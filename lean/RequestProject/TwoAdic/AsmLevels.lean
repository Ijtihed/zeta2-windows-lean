import RequestProject.TwoAdic.AsmClass

/-!
# The level decomposition of `∑ s_k D_k − penalty`

For an odd prime `ℓ`, `n` even, `n ≥ 1`, and a profile `s`:

* `count_levels_lt`: `v_ℓ(x) = #{1 ≤ j ≤ N + 1 : ℓ^j ∣ x}` for `0 < |x| < ℓ^{N+1}`;
* `Dk_levels`: `D_k = ∑_{1 ≤ j ≤ 2R+1} q (N_j(k) − 1 − z_j(k))`, where `N_j(k)` counts the nodes
  `≡ k (mod ℓ^j)` and `z_j(k)` the zeros with `ℓ^j ∣ 2(−k − z)`;
* **`sum_D_sub_penalty`**: `∑_k s_k D_k − penalty(s) = ∑_{1 ≤ j ≤ 2R+1} ∑_{c < ℓ^j} E_c`, with the
  class contributions `E_c = Ecl q n ℓ^j c s` of `Levels.lean`.
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev

variable {q d n ℓ : ℕ}

theorem count_levels_lt (p : ℕ) [hp : Fact p.Prime] (N : ℕ) (x : ℤ) (hx : x ≠ 0)
    (hxN : x.natAbs < p ^ (N + 1)) :
    ∑ j ∈ Icc 1 (N + 1), (if ((p ^ j : ℕ) : ℤ) ∣ x then (1 : ℤ) else 0) = padicValInt p x := by
  have hv : padicValInt p x ≤ N + 1 := by
    have h1 : ((p ^ padicValInt p x : ℕ) : ℤ) ∣ x := by exact_mod_cast padicValInt_dvd x
    have h2 : p ^ padicValInt p x ≤ x.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hx)
      (Int.natCast_dvd.1 h1)
    have h3 : p ^ padicValInt p x < p ^ (N + 1) := lt_of_le_of_lt h2 hxN
    exact ((Nat.pow_lt_pow_iff_right hp.out.one_lt).1 h3).le
  rw [sum_boole]
  have : (Icc 1 (N + 1)).filter (fun j => ((p ^ j : ℕ) : ℤ) ∣ x) = Icc 1 (padicValInt p x) := by
    ext j
    simp only [mem_filter, mem_Icc]
    rw [show ((p ^ j : ℕ) : ℤ) = (p : ℤ) ^ j by push_cast; rfl, padicValInt_dvd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3.resolve_left hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans hv⟩, Or.inr h2⟩
  rw [this, Nat.card_Icc]
  simp

theorem pow_big [hp : Fact ℓ.Prime] (h2 : ℓ ≠ 2) (hn : Even n) : 4 * n < ℓ ^ (2 * R n + 1) := by
  have hR := R_of_even hn
  have h3 : 3 ≤ ℓ := by
    have := hp.out.two_le
    rcases Nat.lt_or_ge ℓ 3 with h | h
    · interval_cases ℓ; exact absurd rfl h2
    · exact h
  have h1 : 3 * n < 3 ^ (3 * n) := Nat.lt_pow_self (by norm_num)
  have h4 : 3 ^ (3 * n + 1) ≤ ℓ ^ (3 * n + 1) := Nat.pow_le_pow_left h3 _
  rw [show 2 * R n + 1 = 3 * n + 1 by omega]
  rw [pow_succ] at h4
  nlinarith

theorem Dk_levels [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) {k : ℤ}
    (hk : k ∈ nodes n) :
    Dk q n ℓ k = ∑ j ∈ Icc 1 (2 * R n + 1),
      (q : ℤ) * ((Asm.Ncl n (ℓ ^ j) k : ℤ) - 1 - Asm.Zcl n (ℓ ^ j) k) := by
  have hbig := pow_big (n := n) h2 hn
  unfold Dk
  -- node part
  have hA : ∑ m ∈ (nodes n).erase k, (padicValInt ℓ (m - k) : ℤ) =
      ∑ j ∈ Icc 1 (2 * R n + 1), ((Asm.Ncl n (ℓ ^ j) k : ℤ) - 1) := by
    have e1 : ∀ m ∈ (nodes n).erase k, (padicValInt ℓ (m - k) : ℤ) =
        ∑ j ∈ Icc 1 (2 * R n + 1), (if ((ℓ ^ j : ℕ) : ℤ) ∣ m - k then (1 : ℤ) else 0) := by
      intro m hm
      rw [mem_erase] at hm
      refine (count_levels_lt ℓ (2 * R n) (m - k) (sub_ne_zero.2 hm.1) ?_).symm
      have := nodes_diff_natAbs hm.2 hk hn1
      have hR := R_of_even hn
      omega
    rw [sum_congr rfl e1, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_boole]
    unfold Asm.Ncl
    rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨hk, by simp⟩)]
    have : 1 ≤ ((nodes n).filter fun m => ((ℓ ^ j : ℕ) : ℤ) ∣ m - k).card :=
      card_pos.2 ⟨k, mem_filter.2 ⟨hk, by simp⟩⟩
    rw [Nat.cast_sub this, Nat.cast_one]
  -- zero part
  have hB : ∑ t ∈ range n, (padicValInt ℓ (ez n t k) : ℤ) =
      ∑ j ∈ Icc 1 (2 * R n + 1), (Asm.Zcl n (ℓ ^ j) k : ℤ) := by
    have e1 : ∀ t ∈ range n, (padicValInt ℓ (ez n t k) : ℤ) =
        ∑ j ∈ Icc 1 (2 * R n + 1), (if ((ℓ ^ j : ℕ) : ℤ) ∣ ez n t k then (1 : ℤ) else 0) := by
      intro t ht
      refine (count_levels_lt ℓ (2 * R n) _ (ez_ne_zero hn t k) ?_).symm
      have := ez_natAbs hk (mem_range.1 ht)
      omega
    rw [sum_congr rfl e1, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_boole]
    rfl
  rw [hA, hB, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **The level decomposition.** -/
theorem sum_D_sub_penalty [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (s : Fin (2 * R n + 1) → ℕ) :
    ∑ i, (s i : ℤ) * Dk q n ℓ (nodeOf n i) - penalty n ℓ s =
      ∑ j ∈ Icc 1 (2 * R n + 1), ∑ c ∈ range (ℓ ^ j), Ecl q n (ℓ ^ j) c s := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  simp_rw [Dk_levels (q := q) hn hn1 h2 (nodeOf_mem_nodes' n _), mul_sum]
  rw [sum_comm]
  unfold penalty
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hM : 0 < ℓ ^ j := pow_pos hℓ0 j
  rw [sum_eq_sum_cls (n := n) hM, ← sum_sub_distrib]
  refine sum_congr rfl fun c _ => ?_
  unfold Ecl
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [Ncl_eq_card hi, Zcl_eq_zc hi]
  ring

end TwoAdicWin.Asm
