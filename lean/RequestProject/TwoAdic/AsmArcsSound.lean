import RequestProject.TwoAdic.AsmArcs
import RequestProject.TwoAdic.AsmCount

/-!
# Soundness of the arc checker

For `n` even, `ℓ` odd, `u = ℓ/n ∈ [a, b]` and a checked arc `[lo, hi]`, every residue `r < ℓ` with
`n·lo(u) + 1 ≤ r ≤ n·hi(u) − 1` has (`arc_data`)

* `N_c = arcN` nodes in its class modulo `ℓ`;
* `arcH` of them hs (`ℓ ≤ 2|k| − 1`);
* `z_c = arcZ` zeros.
-/

open Finset

namespace TwoAdicWin.Arc

open Lev Asm Cert

theorem le_affV_of_geAB {a b u : ℚ} {f : Aff} {c : ℚ} (h : geAB a b f c = true) (ha : a ≤ u)
    (hb : u ≤ b) : c ≤ affV f u := by
  simp only [geAB, Bool.and_eq_true, decide_eq_true_eq, affV] at h ⊢
  rcases le_total 0 f.2 with h0 | h0
  · nlinarith [mul_le_mul_of_nonneg_left ha h0]
  · nlinarith [mul_le_mul_of_nonpos_left hb h0]

theorem affV_le_of_leAB {a b u : ℚ} {f : Aff} {c : ℚ} (h : leAB a b f c = true) (ha : a ≤ u)
    (hb : u ≤ b) : affV f u ≤ c := by
  simp only [leAB, Bool.and_eq_true, decide_eq_true_eq, affV] at h ⊢
  rcases le_total 0 f.2 with h0 | h0
  · nlinarith [mul_le_mul_of_nonneg_left hb h0]
  · nlinarith [mul_le_mul_of_nonpos_left ha h0]

/-- The setting: `n > 0`, `u = ℓ/n ∈ [a, b]`. -/
structure Setting (a b : ℚ) (n ℓ : ℕ) : Prop where
  n_pos : 0 < n
  ha : a ≤ (ℓ : ℚ) / n
  hb : (ℓ : ℚ) / n ≤ b

variable {a b : ℚ} {n ℓ : ℕ}

/-- `c ≤ f(ℓ/n)` scaled by `n`. -/
theorem scale_ge (hs : Setting a b n ℓ) {f : Aff} {c : ℚ} (h : geAB a b f c = true) :
    c * n ≤ f.1 * n + f.2 * ℓ := by
  have h1 := le_affV_of_geAB h hs.ha hs.hb
  have hn : (0 : ℚ) < n := by exact_mod_cast hs.n_pos
  unfold affV at h1
  have : (f.1 + f.2 * (ℓ / n)) * n = f.1 * n + f.2 * ℓ := by field_simp
  nlinarith

theorem scale_le (hs : Setting a b n ℓ) {f : Aff} {c : ℚ} (h : leAB a b f c = true) :
    f.1 * n + f.2 * ℓ ≤ c * n := by
  have h1 := affV_le_of_leAB h hs.ha hs.hb
  have hn : (0 : ℚ) < n := by exact_mod_cast hs.n_pos
  unfold affV at h1
  have : (f.1 + f.2 * (ℓ / n)) * n = f.1 * n + f.2 * ℓ := by field_simp
  nlinarith

/-- The node predicate `|r + jℓ| ≤ 3n/2`. -/
def IsNode (n ℓ : ℕ) (r : ℕ) (j : ℤ) : Prop := -((R n : ℤ)) ≤ (r : ℤ) + j * ℓ ∧ (r : ℤ) + j * ℓ ≤ R n

/-- The hs predicate `ℓ ≤ 2|r + jℓ| − 1`. -/
def IsHs (ℓ : ℕ) (r : ℕ) (j : ℤ) : Prop := (ℓ : ℤ) ≤ 2 * |(r : ℤ) + j * ℓ| - 1

/-- The zero predicate `1 − n ≤ 2r + (2j − 1)ℓ ≤ n − 1`. -/
def IsZero (n ℓ : ℕ) (r : ℕ) (j : ℤ) : Prop :=
  1 - (n : ℤ) ≤ 2 * (r : ℤ) + (2 * j - 1) * ℓ ∧ 2 * (r : ℤ) + (2 * j - 1) * ℓ ≤ (n : ℤ) - 1

instance (n ℓ r : ℕ) (j : ℤ) : Decidable (IsNode n ℓ r j) := by unfold IsNode; infer_instance
instance (ℓ r : ℕ) (j : ℤ) : Decidable (IsHs ℓ r j) := by unfold IsHs; infer_instance
instance (n ℓ r : ℕ) (j : ℤ) : Decidable (IsZero n ℓ r j) := by unfold IsZero; infer_instance

/-- A residue is *good* in the arc `[lo, hi]`. -/
def Good (n ℓ : ℕ) (lo hi : Aff) (r : ℕ) : Prop :=
  lo.1 * n + lo.2 * ℓ + 1 ≤ (r : ℚ) ∧ (r : ℚ) ≤ hi.1 * n + hi.2 * ℓ - 1

theorem R_eq (hn : Even n) : ((R n : ℤ) : ℚ) * 2 = 3 * n := by
  have := R_of_even hn
  have h : ((2 * R n : ℕ) : ℚ) = ((3 * n : ℕ) : ℚ) := by rw [this]
  push_cast at h ⊢; linarith

/-- **Shifts: nodes and hs.** -/
theorem node_of_nodeSt (hn : Even n) (hs : Setting a b n ℓ) {lo hi : Aff} {r : ℕ}
    (hg : Good n ℓ lo hi r) {j : ℤ} {bN bH : Bool} (h : nodeSt a b lo hi j = some (bN, bH)) :
    (IsNode n ℓ r j ↔ bN = true) ∧ (bN = true → (IsHs ℓ r j ↔ bH = true)) := by
  have hR := R_eq hn
  obtain ⟨hg1, hg2⟩ := hg
  have hk1 : (lo.1 * n + (lo.2 + j) * ℓ + 1 : ℚ) ≤ ((r : ℤ) + j * ℓ : ℤ) := by push_cast; linarith
  have hk2 : (((r : ℤ) + j * ℓ : ℤ) : ℚ) ≤ hi.1 * n + (hi.2 + j) * ℓ - 1 := by push_cast; linarith
  set k : ℤ := (r : ℤ) + j * ℓ
  have hnode_iff : IsNode n ℓ r j ↔ (-((R n : ℤ) : ℚ) ≤ (k : ℚ) ∧ (k : ℚ) ≤ ((R n : ℤ) : ℚ)) := by
    unfold IsNode; constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hhs_iff : IsHs ℓ r j ↔ ((ℓ : ℚ) ≤ 2 * |(k : ℚ)| - 1) := by
    unfold IsHs; rw [← Int.cast_abs]; constructor
    · intro h1; exact_mod_cast h1
    · intro h1; exact_mod_cast h1
  unfold nodeSt at h
  split_ifs at h with h1 h2 h3 h4
  · -- node, hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at h1
    have e1 := scale_ge hs h1.1
    have e2 := scale_le hs h1.2
    simp only at e1 e2
    refine ⟨⟨fun _ => rfl, fun _ => hnode_iff.2 ⟨by linarith, by linarith⟩⟩, fun _ => ⟨fun _ => rfl, fun _ => ?_⟩⟩
    rw [hhs_iff]
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · have := scale_ge hs h2; simp only at this
      rw [abs_of_nonneg (by linarith)]; linarith
    · have := scale_le hs h2; simp only at this
      rw [abs_of_neg (by linarith)]; linarith
  · -- node, not hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at h1 h3
    have e1 := scale_ge hs h1.1
    have e2 := scale_le hs h1.2
    have e3 := scale_ge hs h3.1
    have e4 := scale_le hs h3.2
    simp only at e1 e2 e3 e4
    refine ⟨⟨fun _ => rfl, fun _ => hnode_iff.2 ⟨by linarith, by linarith⟩⟩, fun _ => ⟨fun h5 => ?_, fun h5 => absurd h5 (by simp)⟩⟩
    rw [hhs_iff] at h5
    have : |(k : ℚ)| ≤ ℓ / 2 - 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  · -- not a node
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨fun h5 => ?_, fun h5 => absurd h5 (by simp)⟩, fun h5 => absurd h5 (by simp)⟩
    rw [hnode_iff] at h5
    simp only [Bool.or_eq_true] at h4
    rcases h4 with h4 | h4
    · have := scale_le hs h4; simp only at this; linarith [h5.1]
    · have := scale_ge hs h4; simp only at this; linarith [h5.2]

/-- **Shifts: zeros.** -/
theorem zero_of_zeroSt (hs : Setting a b n ℓ) {lo hi : Aff} {r : ℕ}
    (hg : Good n ℓ lo hi r) {j : ℤ} {bZ : Bool} (h : zeroSt a b lo hi j = some bZ) :
    IsZero n ℓ r j ↔ bZ = true := by
  obtain ⟨hg1, hg2⟩ := hg
  have hz_iff : IsZero n ℓ r j ↔ (1 - (n : ℚ) ≤ ((2 * (r : ℤ) + (2 * j - 1) * ℓ : ℤ) : ℚ) ∧
      ((2 * (r : ℤ) + (2 * j - 1) * ℓ : ℤ) : ℚ) ≤ (n : ℚ) - 1) := by
    unfold IsZero; constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [hz_iff]
  push_cast
  unfold zeroSt at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at h1
    have e1 := scale_ge hs h1.1
    have e2 := scale_le hs h1.2
    simp only at e1 e2
    exact ⟨fun _ => rfl, fun _ => ⟨by linarith, by linarith⟩⟩
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun h5 => ?_, fun h5 => absurd h5 (by simp)⟩
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · have := scale_le hs h2; simp only at this; linarith [h5.1]
    · have := scale_ge hs h2; simp only at this; linarith [h5.2]

/-- **Shifts outside `[−J, J]`** carry no node and no zero. -/
theorem out_of_range (hn : Even n) (hs : Setting a b n ℓ) (ha0 : 0 < a) {J : ℕ}
    (hJ : 3 / 2 < (J : ℚ) * a) {r : ℕ} (hr : r < ℓ) {j : ℤ} (hj : j ∉ Icc (-(J : ℤ)) J) :
    ¬ IsNode n ℓ r j ∧ ¬ IsZero n ℓ r j := by
  have hR := R_eq hn
  have hR' : ((R n : ℕ) : ℚ) * 2 = 3 * n := by push_cast at hR; exact hR
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hs.n_pos
  have hl : a * n ≤ ℓ := by
    have := hs.ha; rwa [le_div_iff₀ hn0] at this
  have hJl : 3 / 2 * (n : ℚ) < J * ℓ := by nlinarith
  have hr' : (r : ℚ) < ℓ := by exact_mod_cast hr
  have hr0 : (0 : ℚ) ≤ r := by positivity
  rw [mem_Icc, not_and_or, not_le, not_le] at hj
  rcases hj with hj | hj
  · -- j ≤ −J − 1
    have hj' : (j : ℚ) ≤ -(J : ℚ) - 1 := by
      have : j ≤ -(J : ℤ) - 1 := by omega
      exact_mod_cast this
    have hl0 : (0 : ℚ) ≤ ℓ := by positivity
    have h1 : (j : ℚ) * ℓ ≤ (-(J : ℚ) - 1) * ℓ := mul_le_mul_of_nonneg_right hj' hl0
    constructor
    · rintro ⟨h2, -⟩
      have : (-((R n : ℤ) : ℚ)) ≤ ((r : ℤ) + j * ℓ : ℤ) := by exact_mod_cast h2
      push_cast at this; nlinarith
    · rintro ⟨h2, -⟩
      have : (1 - (n : ℚ)) ≤ ((2 * (r : ℤ) + (2 * j - 1) * ℓ : ℤ) : ℚ) := by exact_mod_cast h2
      push_cast at this; nlinarith
  · -- j ≥ J + 1
    have hj' : (J : ℚ) + 1 ≤ j := by
      have : (J : ℤ) + 1 ≤ j := by omega
      exact_mod_cast this
    have hl0 : (0 : ℚ) ≤ ℓ := by positivity
    have h1 : ((J : ℚ) + 1) * ℓ ≤ j * ℓ := mul_le_mul_of_nonneg_right hj' hl0
    constructor
    · rintro ⟨-, h2⟩
      have : (((r : ℤ) + j * ℓ : ℤ) : ℚ) ≤ ((R n : ℤ) : ℚ) := by exact_mod_cast h2
      push_cast at this; nlinarith
    · rintro ⟨-, h2⟩
      have : ((2 * (r : ℤ) + (2 * j - 1) * ℓ : ℤ) : ℚ) ≤ (n : ℚ) - 1 := by exact_mod_cast h2
      push_cast at this; nlinarith

/-! ### From node indices to shifts -/

/-- Nodes of the class of `r` satisfying `P`, counted by shifts. -/
theorem card_cls_filter_eq (hℓ0 : 0 < ℓ) {r : ℕ} (hr : r < ℓ) (J : ℕ)
    (hJ : ∀ j : ℤ, IsNode n ℓ r j → j ∈ Icc (-(J : ℤ)) J) (P : ℤ → Prop) [DecidablePred P] :
    ((cls n ℓ r).filter fun i => P (nodeOf n i)).card =
      ((Icc (-(J : ℤ)) J).filter fun j => IsNode n ℓ r j ∧ P ((r : ℤ) + j * ℓ)).card := by
  symm
  refine card_bij (fun j hj => (⟨((r : ℤ) + j * ℓ + R n).toNat, by
      simp only [mem_filter, IsNode] at hj; omega⟩ : Fin (2 * R n + 1)))
    (fun j hj => ?_) (fun j₁ hj₁ j₂ hj₂ h => ?_) (fun i hi => ?_)
  · simp only [mem_filter, IsNode] at hj
    obtain ⟨-, ⟨h1, h2⟩, h3⟩ := hj
    simp only [cls, mem_filter, mem_univ, true_and, nodeOf]
    have e : (((((r : ℤ) + j * ℓ + R n).toNat : ℕ) : ℤ) - R n) = (r : ℤ) + j * ℓ := by omega
    refine ⟨?_, ?_⟩
    · rw [e, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)
    · rw [e]; exact h3
  · simp only [mem_filter, IsNode] at hj₁ hj₂
    have := congrArg Fin.val h
    simp only at this
    have e : (r : ℤ) + j₁ * ℓ = (r : ℤ) + j₂ * ℓ := by omega
    have : j₁ * (ℓ : ℤ) = j₂ * ℓ := by linarith
    exact mul_right_cancel₀ (by exact_mod_cast hℓ0.ne') this
  · simp only [cls, mem_filter, mem_univ, true_and] at hi
    obtain ⟨h1, h2⟩ := hi
    set k := nodeOf n i
    have hk := Int.emod_add_ediv k ℓ
    rw [h1] at hk
    have hnode : IsNode n ℓ r (k / ℓ) := by
      unfold IsNode
      have := i.isLt
      simp only [k, nodeOf] at hk ⊢
      constructor <;> linarith [mul_comm ((ℓ : ℤ)) (((i : ℤ) - R n) / ℓ)]
    refine ⟨k / ℓ, ?_, ?_⟩
    · simp only [mem_filter]
      refine ⟨hJ _ hnode, hnode, ?_⟩
      have : (r : ℤ) + k / ℓ * ℓ = k := by linarith [mul_comm ((ℓ : ℤ)) (k / ℓ)]
      rw [this]; exact h2
    · apply Fin.ext
      simp only
      have : (r : ℤ) + k / ℓ * ℓ = k := by linarith [mul_comm ((ℓ : ℤ)) (k / ℓ)]
      rw [this]
      simp only [k, nodeOf]
      omega

/-- Zeros of the class of `r`, counted by shifts. -/
theorem zc_eq_shifts (hn : Even n) (hℓ : Odd ℓ) {r : ℕ} (J : ℕ)
    (hJ : ∀ j : ℤ, IsZero n ℓ r j → j ∈ Icc (-(J : ℤ)) J) :
    zc n ℓ r = ((Icc (-(J : ℤ)) J).filter fun j => IsZero n ℓ r j).card := by
  obtain ⟨c, hc⟩ := hn
  obtain ⟨t, ht⟩ := hℓ
  have hℓ' : (ℓ : ℤ) = 2 * t + 1 := by exact_mod_cast ht
  have hn' : (n : ℤ) = 2 * c := by omega
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by omega
  -- `P(j) = r + jℓ − t − 1 + c`, with `2 P(j) = 2r + (2j − 1)ℓ + n − 1`
  have key : ∀ j : ℤ, 2 * (r : ℤ) + (2 * j - 1) * ℓ = 2 * ((r : ℤ) + j * ℓ - t - 1 + c) + 1 - n := by
    intro j; rw [hn']; linear_combination (-1 : ℤ) * hℓ'
  symm
  unfold zc
  refine card_bij (fun j _ => ((r : ℤ) + j * ℓ - t - 1 + c).toNat) (fun j hj => ?_)
    (fun j₁ hj₁ j₂ hj₂ h => ?_) (fun i hi => ?_)
  · simp only [mem_filter, IsZero] at hj
    obtain ⟨-, h1, h2⟩ := hj
    have k := key j
    simp only [mem_filter, mem_range]
    have hP0 : (0 : ℤ) ≤ (r : ℤ) + j * ℓ - t - 1 + c := by
      generalize 2 * (r : ℤ) + (2 * j - 1) * ℓ = E at h1 h2 k
      generalize (r : ℤ) + j * ℓ - t - 1 + c = P at k ⊢
      omega
    have hP1 : (r : ℤ) + j * ℓ - t - 1 + c < n := by
      generalize 2 * (r : ℤ) + (2 * j - 1) * ℓ = E at h1 h2 k
      generalize (r : ℤ) + j * ℓ - t - 1 + c = P at k ⊢
      omega
    refine ⟨by omega, ?_⟩
    refine ⟨2 * j - 1, ?_⟩
    rw [Int.toNat_of_nonneg hP0]
    linarith [k]
  · simp only at h
    simp only [mem_filter, IsZero] at hj₁ hj₂
    have k1 := key j₁
    have k2 := key j₂
    have hP1 : (0 : ℤ) ≤ (r : ℤ) + j₁ * ℓ - t - 1 + c := by
      generalize 2 * (r : ℤ) + (2 * j₁ - 1) * ℓ = E at hj₁ k1
      generalize (r : ℤ) + j₁ * ℓ - t - 1 + c = P at k1 ⊢
      omega
    have hP2 : (0 : ℤ) ≤ (r : ℤ) + j₂ * ℓ - t - 1 + c := by
      generalize 2 * (r : ℤ) + (2 * j₂ - 1) * ℓ = E at hj₂ k2
      generalize (r : ℤ) + j₂ * ℓ - t - 1 + c = P at k2 ⊢
      omega
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Int.toNat_of_nonneg hP1, Int.toNat_of_nonneg hP2] at this
    have : j₁ * (ℓ : ℤ) = j₂ * ℓ := by linarith
    exact mul_right_cancel₀ hℓ0 this
  · simp only [mem_filter, mem_range] at hi
    obtain ⟨hi1, ⟨m, hm⟩⟩ := hi
    -- `2i + 1 − n − 2r = ℓ m`, so `m` is odd
    have hm' : (2 * (i : ℤ) + 1 - n) - 2 * r = 2 * (t * m) + m := by rw [hm, hℓ']; ring
    have hmodd : ∃ w : ℤ, m = 2 * w - 1 := ⟨(m + 1) / 2, by
      generalize t * m = Q at hm'
      omega⟩
    obtain ⟨w, rfl⟩ := hmodd
    have e : 2 * (r : ℤ) + (2 * w - 1) * ℓ = 2 * i + 1 - n := by linarith
    have hz : IsZero n ℓ r w := by unfold IsZero; rw [e]; omega
    refine ⟨w, ?_, ?_⟩
    · simp only [mem_filter]
      exact ⟨hJ _ hz, hz⟩
    · have k := key w
      rw [e] at k
      have : (r : ℤ) + w * ℓ - t - 1 + c = i := by linarith
      simp only [this, Int.toNat_natCast]

/-! ### The class data of a good residue -/

theorem shifts_toFinset (J : ℕ) : (shifts J).toFinset = Icc (-(J : ℤ)) J := by
  ext j
  simp only [shifts, List.mem_toFinset, List.mem_map, List.mem_range, mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨(j + J).toNat, by omega, by omega⟩

theorem shifts_nodup (J : ℕ) : (shifts J).Nodup := by
  unfold shifts
  refine List.Nodup.map (fun i₁ i₂ h => by simpa using h) List.nodup_range

theorem length_filter_shifts (J : ℕ) (p : ℤ → Bool) :
    ((shifts J).filter p).length = ((Icc (-(J : ℤ)) J).filter fun j => p j = true).card := by
  rw [← List.toFinset_card_of_nodup ((shifts_nodup J).filter p), List.toFinset_filter,
    shifts_toFinset]

theorem nodeSt_isSome {c : CellD} {J : ℕ} {lo hi : Aff} {j : ℤ}
    (h : allDet c.a c.b lo hi J = true) (hj : j ∈ Icc (-(J : ℤ)) J) :
    (nodeSt c.a c.b lo hi j).isSome ∧ (zeroSt c.a c.b lo hi j).isSome := by
  unfold allDet at h
  rw [List.all_eq_true] at h
  have hm : j ∈ shifts J := by rw [← List.mem_toFinset, shifts_toFinset]; exact hj
  have := h j hm
  simpa using this

/-- **The class data of a good residue.** -/
theorem arc_data (hn : Even n) (hℓ : Odd ℓ) {c : CellD} (hs : Setting c.a c.b n ℓ)
    (ha0 : 0 < c.a) {J : ℕ} (hJ : 3 / 2 < (J : ℚ) * c.a) {lo hi : Aff}
    (hdet : allDet c.a c.b lo hi J = true) {r : ℕ} (hr : r < ℓ) (hg : Good n ℓ lo hi r) :
    (cls n ℓ r).card = arcN c.a c.b lo hi J ∧
      ((cls n ℓ r).filter fun i => (ℓ : ℤ) ≤ 2 * |nodeOf n i| - 1).card = arcH c.a c.b lo hi J ∧
      zc n ℓ r = arcZ c.a c.b lo hi J := by
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hJn : ∀ j : ℤ, IsNode n ℓ r j → j ∈ Icc (-(J : ℤ)) J := fun j hj => by
    by_contra h; exact (out_of_range hn hs ha0 hJ hr h).1 hj
  have hJz : ∀ j : ℤ, IsZero n ℓ r j → j ∈ Icc (-(J : ℤ)) J := fun j hj => by
    by_contra h; exact (out_of_range hn hs ha0 hJ hr h).2 hj
  -- the status of each shift
  have hst : ∀ j ∈ Icc (-(J : ℤ)) J,
      (IsNode n ℓ r j ↔ isNodeB c.a c.b lo hi j = true) ∧
      (IsNode n ℓ r j ∧ IsHs ℓ r j ↔ isHsB c.a c.b lo hi j = true) ∧
      (IsZero n ℓ r j ↔ isZeroB c.a c.b lo hi j = true) := by
    intro j hj
    obtain ⟨h1, h2⟩ := nodeSt_isSome hdet hj
    obtain ⟨⟨bN, bH⟩, hb⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨bZ, hz⟩ := Option.isSome_iff_exists.1 h2
    have hnd := node_of_nodeSt hn hs hg hb
    have hzr := zero_of_zeroSt hs hg hz
    refine ⟨?_, ?_, ?_⟩
    · rw [hnd.1]; unfold isNodeB; rw [hb]; cases bN <;> simp
    · unfold isHsB; rw [hb]
      cases bN
      · simp only [Bool.false_eq_true, iff_false] at hnd ⊢
        simp [hnd.1]
      · have h3 := hnd.2 rfl
        have h4 := hnd.1.2 rfl
        cases bH
        · simp only [Bool.false_eq_true, iff_false] at h3
          simp [h3]
        · simp only [iff_true] at h3
          simp [h3, h4]
    · rw [hzr]; unfold isZeroB; rw [hz]; cases bZ <;> simp
  refine ⟨?_, ?_, ?_⟩
  · have := card_cls_filter_eq (n := n) hℓ0 hr J hJn (fun _ => True)
    simp only [and_true, filter_true_of_mem (fun _ _ => trivial)] at this
    rw [this, arcN, length_filter_shifts]
    congr 1
    exact filter_congr fun j hj => (hst j hj).1
  · rw [card_cls_filter_eq (n := n) hℓ0 hr J hJn (fun k => (ℓ : ℤ) ≤ 2 * |k| - 1), arcH,
      length_filter_shifts]
    congr 1
    exact filter_congr fun j hj => (hst j hj).2.1
  · rw [zc_eq_shifts hn hℓ J hJz, arcZ, length_filter_shifts]
    congr 1
    exact filter_congr fun j hj => (hst j hj).2.2

end TwoAdicWin.Arc
