import RequestProject.TwoAdic.Levels

/-!
# Counting nodes and zeros in residue classes

For a positive modulus `M` and a residue `c < M`:

* `card_cls_bounds`: the class `c` contains between `⌊(3n+1)/M⌋` and `⌊(3n+1)/M⌋ + 1` nodes
  (for even `n`; in general `2R + 1` replaces `3n + 1`);
* `zc_bounds` (odd `M`): between `⌊n/M⌋` and `⌊n/M⌋ + 1` zeros `z` have `M ∣ 2(−k − z)` for `k ≡ c`;
* `sum_card_cls`: `∑_{c < M} N_c = 2R + 1`; `sum_zc` (odd `M`): `∑_{c < M} z_c = n`.
-/

open Finset

namespace TwoAdicWin.Asm

open Lev

/-- The number of integers `≡ v (mod M)` in an interval of length `L` is `⌊L/M⌋` or `⌊L/M⌋ + 1`. -/
theorem card_Ico_modEq_bounds (a : ℤ) (L M : ℕ) (hM : 0 < M) (v : ℤ) :
    L / M ≤ #{x ∈ Ico a (a + L) | x ≡ v [ZMOD M]} ∧
      #{x ∈ Ico a (a + L) | x ≡ v [ZMOD M]} ≤ L / M + 1 := by
  have h := Int.Ico_filter_modEq_card a (a + L) (r := (M : ℤ)) (by exact_mod_cast hM) v
  obtain ⟨k, hk⟩ : ∃ k, k = L / M := ⟨_, rfl⟩
  rw [← hk]
  set α : ℚ := (a - v) / (M : ℚ)
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have e : ((a + L - v : ℤ) : ℚ) / ((M : ℤ) : ℚ) = α + (L : ℚ) / M := by
    simp only [α]; push_cast; field_simp; ring
  have e2 : ((a - v : ℤ) : ℚ) / ((M : ℤ) : ℚ) = α := by simp only [α]; push_cast; ring
  push_cast at h e e2
  rw [e, e2] at h
  have hk1 : k * M ≤ L := by rw [hk]; exact Nat.div_mul_le_self L M
  have hk2 : L < k * M + M := by rw [hk]; exact Nat.lt_div_mul_add hM
  have hfl : (k : ℚ) ≤ (L : ℚ) / M := by
    rw [le_div_iff₀ hMq]; exact_mod_cast hk1
  have hfl2 : (L : ℚ) / M < (k : ℚ) + 1 := by
    rw [div_lt_iff₀ hMq]
    have : (L : ℚ) < k * M + M := by exact_mod_cast hk2
    linarith
  have h1 : ⌈α⌉ + (k : ℤ) ≤ ⌈α + (L : ℚ) / M⌉ := by
    rw [← Int.ceil_add_intCast]
    exact Int.ceil_mono (by push_cast; linarith)
  have h2 : ⌈α + (L : ℚ) / M⌉ ≤ ⌈α⌉ + (k : ℤ) + 1 := by
    have := Int.ceil_add_le α ((L : ℚ) / M)
    have h3 : ⌈(L : ℚ) / M⌉ ≤ (k : ℤ) + 1 := by
      rw [Int.ceil_le]; push_cast; linarith
    linarith
  constructor
  · have : ((k : ℕ) : ℤ) ≤ ((#{x ∈ Ico a (a + L) | x ≡ v [ZMOD M]} : ℕ) : ℤ) := by
      rw [h]; exact le_max_of_le_left (by linarith)
    exact_mod_cast this
  · have : ((#{x ∈ Ico a (a + L) | x ≡ v [ZMOD M]} : ℕ) : ℤ) ≤ (k : ℤ) + 1 := by
      rw [h]; exact max_le (by linarith) (by positivity)
    exact_mod_cast this

theorem card_cls_eq (n M c : ℕ) (hc : c < M) :
    (cls n M c).card = #{x ∈ Ico (-(R n : ℤ)) (-(R n : ℤ) + ((2 * R n + 1 : ℕ) : ℤ)) |
      x ≡ c [ZMOD M]} := by
  unfold cls
  rw [card_filter, card_filter]
  rw [← sum_nodes_eq' n (fun k => if k % (M : ℤ) = c then 1 else 0)]
  have e : nodes n = Ico (-(R n : ℤ)) (-(R n : ℤ) + ((2 * R n + 1 : ℕ) : ℤ)) := by
    ext x; simp only [nodes, mem_Icc, mem_Ico]; push_cast; omega
  rw [e]
  refine sum_congr rfl fun x _ => ?_
  have : x % (M : ℤ) = c ↔ x ≡ c [ZMOD M] := by
    unfold Int.ModEq
    rw [Int.emod_eq_of_lt (a := (c : ℤ)) (b := (M : ℤ)) (by positivity) (by exact_mod_cast hc)]
  simp only [this]

/-- **Nodes per class**: `⌊(2R+1)/M⌋ ≤ N_c ≤ ⌊(2R+1)/M⌋ + 1`. -/
theorem card_cls_bounds (n M c : ℕ) (hM : 0 < M) (hc : c < M) :
    (2 * R n + 1) / M ≤ (cls n M c).card ∧ (cls n M c).card ≤ (2 * R n + 1) / M + 1 := by
  rw [card_cls_eq n M c hc]
  exact card_Ico_modEq_bounds _ _ _ hM _

theorem dvd_two_iff {M : ℕ} (hM : Odd M) (x y : ℤ) :
    (M : ℤ) ∣ 2 * x - y ↔ x ≡ ((M : ℤ) + 1) / 2 * y [ZMOD M] := by
  obtain ⟨t, ht⟩ := hM
  have hM' : (M : ℤ) = 2 * t + 1 := by exact_mod_cast ht
  have hh : ((M : ℤ) + 1) / 2 = t + 1 := by omega
  rw [hh, Int.modEq_comm, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨(t + 1) * w - x, by rw [hM'] at hw ⊢; linear_combination ((t : ℤ) + 1) * hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨y + 2 * w, by rw [hM'] at hw ⊢; linear_combination 2 * hw⟩

theorem zc_eq (n M c : ℕ) (hM : Odd M) :
    zc n M c = #{x ∈ Ico (0 : ℤ) (0 + (n : ℤ)) | x ≡ ((M : ℤ) + 1) / 2 * ((n : ℤ) - 1 + 2 * c)
      [ZMOD M]} := by
  unfold zc
  refine card_bij (fun j _ => (j : ℤ)) (fun j hj => ?_) (fun a _ b _ h => by simp only at h; exact_mod_cast h)
    (fun x hx => ?_)
  · simp only [mem_filter, mem_range, mem_Ico] at hj ⊢
    refine ⟨⟨by positivity, by omega⟩, ?_⟩
    rw [← dvd_two_iff hM]
    have : (2 * (j : ℤ) - ((n : ℤ) - 1 + 2 * c)) = (2 * (j : ℤ) + 1 - n) - 2 * c := by ring
    rw [this]; exact hj.2
  · simp only [mem_filter, mem_Ico] at hx
    refine ⟨x.toNat, ?_, by simp; omega⟩
    simp only [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    have hx2 := (dvd_two_iff hM _ _).2 hx.2
    have : (2 * ((x.toNat : ℕ) : ℤ) + 1 - n) - 2 * c = 2 * x - ((n : ℤ) - 1 + 2 * c) := by
      rw [Int.toNat_of_nonneg hx.1.1]; ring
    rw [this]; exact hx2

/-- **Zeros per class** (odd `M`): `⌊n/M⌋ ≤ z_c ≤ ⌊n/M⌋ + 1`. -/
theorem zc_bounds (n M c : ℕ) (hM : Odd M) :
    n / M ≤ zc n M c ∧ zc n M c ≤ n / M + 1 := by
  rw [zc_eq n M c hM]
  exact card_Ico_modEq_bounds _ _ _ hM.pos _

/-- `∑_{c < M} N_c = 2R + 1`. -/
theorem sum_card_cls (n M : ℕ) (hM : 0 < M) :
    ∑ c ∈ range M, (cls n M c).card = 2 * R n + 1 := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin (2 * R n + 1))))
    (t := range M) (f := res n M) (fun i _ => mem_range.2 (res_lt hM i))
  rw [card_univ, Fintype.card_fin] at this
  refine Eq.trans ?_ this.symm
  refine sum_congr rfl fun c hc => ?_
  congr 1
  ext i
  simp only [cls, res, mem_filter, mem_univ, true_and]
  have h1 := Int.emod_nonneg (nodeOf n i) (show (M : ℤ) ≠ 0 by omega)
  omega

/-- `∑_{c < M} z_c = n` for odd `M`. -/
theorem sum_zc (n M : ℕ) (hM : Odd M) : ∑ c ∈ range M, zc n M c = n := by
  have hM0 : 0 < M := hM.pos
  unfold zc
  simp_rw [card_filter]
  rw [sum_comm]
  have : ∀ j ∈ range n, ∑ c ∈ range M,
      (if (M : ℤ) ∣ 2 * (j : ℤ) + 1 - n - 2 * c then 1 else 0) = 1 := by
    intro j _
    rw [sum_boole]
    simp only [Nat.cast_id]
    rw [card_eq_one]
    set y : ℤ := 2 * (j : ℤ) + 1 - n
    set c0 : ℤ := (((M : ℤ) + 1) / 2 * y) % M
    have hc0 : 0 ≤ c0 := Int.emod_nonneg _ (by omega)
    have hc1 : c0 < M := Int.emod_lt_of_pos _ (by omega)
    refine ⟨c0.toNat, ?_⟩
    ext c
    simp only [mem_filter, mem_range, mem_singleton]
    have key : ∀ c : ℕ, (M : ℤ) ∣ y - 2 * c ↔ (c : ℤ) ≡ c0 [ZMOD M] := by
      intro c
      rw [← dvd_neg, neg_sub, dvd_two_iff hM]
      exact ⟨fun h => h.trans (Int.mod_modEq _ _).symm, fun h => h.trans (Int.mod_modEq _ _)⟩
    rw [key]
    constructor
    · rintro ⟨hc, hmod⟩
      have : (c : ℤ) % M = c0 % M := hmod
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hc),
        Int.emod_eq_of_lt hc0 hc1] at this
      omega
    · rintro rfl
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg hc0]
  rw [sum_congr rfl this]
  simp

end TwoAdicWin.Asm
