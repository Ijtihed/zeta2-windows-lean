import RequestProject.TwoAdic.AsmSingle

/-!
# Middle primes

For an odd prime `ℓ` with `4n < ℓ²` (single level), `n` even, `K = qn`:

  `T⁺_ℓ ≤ q² n (n + 1)/ℓ + (d + 2) q n + q² ℓ/4`   (**`middle_bound`**).

Per class `c` the leaf values give `∑_{k ∈ c} (g(k, s_k) + s_k²) ≤ S_c β_c` with
`β_c = q (N_c − z_c) + d + 2` (`class_le_middle`); weak duality over the `ℓ` classes, the totals
`∑ N_c = 3n + 1`, `∑ z_c = n` and Popoviciu's inequality (spread `2q`) give the bound.
(No condition `ℓ ≤ εn` is needed.)
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin

variable {q d n ℓ : ℕ}

theorem not_active_iff {k : ℤ} (hact : ¬(muI n ℓ k = 1 ∨ hsI ℓ k = 1)) :
    ¬(2 ≤ Ncl n ℓ k ∨ 1 ≤ Zcl n ℓ k) ∧ ¬((ℓ : ℤ) ≤ 2 * |k| - 1) := by
  refine ⟨fun h => hact (Or.inl (by unfold muI; rw [if_pos h])),
    fun h => hact (Or.inr (by unfold hsI; rw [if_pos h]))⟩

/-- The per-node bound `g(k, s) + s² ≤ s (q (N_c − z_c) + d + 2)` for `s ≤ q`. -/
theorem node_le_middle [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2)
    {k : ℤ} (hk : k ∈ nodes n) {s : ℕ} (hs : s ≤ q) :
    gval q d n ℓ k s + (s : ℤ) ^ 2 ≤ (s : ℤ) * (q * ((Ncl n ℓ k : ℤ) - Zcl n ℓ k) + d + 2) := by
  have hs0 : (0 : ℤ) ≤ s := Int.natCast_nonneg s
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  unfold gval
  split_ifs with hact
  · rw [Dk_single hn hn1 hsl hk]
    unfold cK
    split_ifs
    · nlinarith
    · nlinarith
  · obtain ⟨h1, _⟩ := not_active_iff hact
    have hN := one_le_Ncl (ℓ := ℓ) hk
    have e1 : Ncl n ℓ k = 1 := by omega
    have e2 : Zcl n ℓ k = 0 := by omega
    rw [e1, e2]
    have : (s : ℤ) ≤ q := by exact_mod_cast hs
    push_cast
    nlinarith

/-- The class bound `∑_{k ∈ c} (g(k, s_k) + s_k²) ≤ S_c (q (N_c − z_c) + d + 2)`. -/
theorem class_le_middle [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2)
    (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ q) (c : ℕ) :
    ∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) ≤
      ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) *
        (q * (((cls n ℓ c).card : ℤ) - zc n ℓ c) + d + 2) := by
  push_cast
  rw [sum_mul]
  refine sum_le_sum fun i hi => ?_
  have := node_le_middle (d := d) hn hn1 hsl (nodeOf_mem_nodes' n i) (hs i)
  rwa [Ncl_eq_card hi, Zcl_eq_zc hi] at this

theorem profile_le {K : ℕ} {s : Fin (2 * R n + 1) → ℕ} (hs : s ∈ profiles q n K) (i) : s i ≤ q := by
  unfold profiles at hs
  rw [mem_filter, Fintype.mem_piFinset] at hs
  have := hs.1 i
  rw [mem_range] at this
  omega

theorem profile_sum {K : ℕ} {s : Fin (2 * R n + 1) → ℕ} (hs : s ∈ profiles q n K) :
    ∑ i, s i = K := by
  unfold profiles at hs
  exact (mem_filter.1 hs).2

/-- `∑_{c < ℓ} S_c = K`. -/
theorem sum_S_cls {K : ℕ} (hℓ0 : 0 < ℓ) {s : Fin (2 * R n + 1) → ℕ} (hs : s ∈ profiles q n K) :
    ∑ c ∈ range ℓ, ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℝ) = K := by
  have := sum_eq_sum_cls (n := n) hℓ0 s
  rw [profile_sum hs] at this
  rw [this]; push_cast; rfl

/-- **Middle primes, `A = q`**, valid for every single-level odd prime. -/
theorem middle_bound [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (hsl : 4 * n < ℓ ^ 2) :
    (TPplus q d n ℓ (q * n) : ℝ) ≤
      (q : ℝ) ^ 2 * n * (n + 1) / ℓ + (d + 2) * q * n + (q : ℝ) ^ 2 * ℓ / 4 := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  have hℓodd : Odd ℓ := hp.out.odd_of_ne_two h2
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ0
  refine TPplus_le_of (by positivity) fun s hs => ⟨_, tree_sum_le_classes hn hn1 h2 hsl s, ?_⟩
  have hsq := profile_le hs
  set S : ℕ → ℝ := fun c => ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℝ) with hSdef
  set β : ℕ → ℝ := fun c => q * (((cls n ℓ c).card : ℝ) - zc n ℓ c) + d + 2 with hβdef
  -- step 1: the class bounds
  have step1 : ((∑ c ∈ range ℓ, (∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) -
      ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2) : ℤ) : ℝ) ≤ ∑ c ∈ range ℓ, (S c * β c - S c ^ 2) := by
    push_cast
    refine sum_le_sum fun c _ => ?_
    have h := class_le_middle (d := d) hn hn1 hsl s hsq c
    have h' : ((∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) : ℤ) : ℝ) ≤
        (((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) *
          (q * (((cls n ℓ c).card : ℤ) - zc n ℓ c) + d + 2) : ℤ) := by exact_mod_cast h
    push_cast at h'
    simp only [hSdef, hβdef]
    push_cast
    linarith
  -- step 2: weak duality
  have hC : 0 < (range ℓ).card := by rw [card_range]; exact hℓ0
  have hSsum : ∑ c ∈ range ℓ, S c = ((q * n : ℕ) : ℝ) := sum_S_cls hℓ0 hs
  have step2 := weak_duality (range ℓ) S β ((q * n : ℕ) : ℝ) hC hSsum
  rw [card_range] at step2
  -- the mean of `β`
  have hN : ∑ c ∈ range ℓ, ((cls n ℓ c).card : ℝ) = 3 * n + 1 := by
    have := sum_card_cls n ℓ hℓ0
    have h3 := R_of_even hn
    have : ((∑ c ∈ range ℓ, (cls n ℓ c).card : ℕ) : ℝ) = ((2 * R n + 1 : ℕ) : ℝ) := by rw [this]
    push_cast at this
    rw [this]
    have : ((2 * R n : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [h3]
    push_cast at this
    linarith
  have hZ : ∑ c ∈ range ℓ, (zc n ℓ c : ℝ) = n := by
    have := sum_zc n ℓ hℓodd
    exact_mod_cast this
  have hβsum : ∑ c ∈ range ℓ, β c = q * (2 * n + 1) + ℓ * (d + 2) := by
    simp only [hβdef]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_sub_distrib, hN, hZ]
    simp only [sum_const, card_range, nsmul_eq_mul]
    ring
  -- step 3: Popoviciu
  set m : ℝ := q * (((3 * n + 1) / ℓ : ℕ) : ℝ) - q * (((n / ℓ : ℕ) : ℝ) + 1) + d + 2 with hmdef
  have hβb : ∀ c ∈ range ℓ, m ≤ β c ∧ β c ≤ m + 2 * q := by
    intro c hc
    have hc' := mem_range.1 hc
    obtain ⟨n1, n2⟩ := card_cls_bounds n ℓ c hℓ0 hc'
    obtain ⟨z1, z2⟩ := zc_bounds n ℓ c hℓodd
    have e : 2 * R n + 1 = 3 * n + 1 := by have := R_of_even hn; omega
    have n1a : (3 * n + 1) / ℓ ≤ (cls n ℓ c).card := by rw [← e]; exact n1
    have n2a : (cls n ℓ c).card ≤ (3 * n + 1) / ℓ + 1 := by rw [← e]; exact n2
    have n1' : (((3 * n + 1) / ℓ : ℕ) : ℝ) ≤ (cls n ℓ c).card := by exact_mod_cast n1a
    have n2' : ((cls n ℓ c).card : ℝ) ≤ (((3 * n + 1) / ℓ : ℕ) : ℝ) + 1 := by exact_mod_cast n2a
    have z1' : ((n / ℓ : ℕ) : ℝ) ≤ zc n ℓ c := by exact_mod_cast z1
    have z2' : (zc n ℓ c : ℝ) ≤ ((n / ℓ : ℕ) : ℝ) + 1 := by exact_mod_cast z2
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    simp only [hmdef, hβdef]
    constructor
    · nlinarith
    · nlinarith
  have step3 := popoviciu (range ℓ) β m (2 * q) hC hβb
  rw [card_range] at step3
  -- combine
  refine step1.trans (step2.trans ?_)
  rw [hβsum]
  have e1 : ((q * n : ℕ) : ℝ) * ((q * (2 * n + 1) + ℓ * (d + 2)) / ℓ) - ((q * n : ℕ) : ℝ) ^ 2 / ℓ =
      (q : ℝ) ^ 2 * n * (n + 1) / ℓ + (d + 2) * q * n := by
    push_cast; field_simp; ring
  have e2 : ∑ c ∈ range ℓ, (β c - (q * (2 * n + 1) + ℓ * (d + 2)) / ℓ) ^ 2 / 4 =
      (∑ c ∈ range ℓ, (β c - (∑ c ∈ range ℓ, β c) / ℓ) ^ 2) / 4 := by
    rw [hβsum, sum_div]
  rw [e1, e2]
  have : (ℓ : ℝ) * (2 * q) ^ 2 / 4 / 4 = (q : ℝ) ^ 2 * ℓ / 4 := by ring
  linarith [div_le_div_of_nonneg_right step3 (by norm_num : (0 : ℝ) ≤ 4)]

end TwoAdicWin.Asm
