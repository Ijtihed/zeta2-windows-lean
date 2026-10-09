import RequestProject.TwoAdic.AsmMiddle

/-!
# The homogeneous relaxation (II, Lemma 5.3) with weak duality at `λ = qτ`

For an odd prime `ℓ` with `4n < ℓ²`, `n` even, `K = qn` and every `τ ≥ 0`:

  `T⁺_ℓ ≤ q² (τ n + ∑_{c < ℓ} ψ̃(α_c, τ))`   (**`relax_bound`**),

where `α_c = classAlphas n ℓ δ c` are the weights of the kept nodes of the class `c`
(`δ = (d+2)/q − 1`).

Proof (II, proof of Lemma 5.3): `s(D_k + c_k + 1) = s q α_k` for the kept nodes since
`d + 2 = q(1 + δ)`; for the other nodes `g + s² ≤ s²` (`node_relax`); the squares of the other nodes
are absorbed by `S_c²`; then `σ = s/q` is feasible for `ψ̃(α_c, τ)` (`class_relax`).
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin

variable {q d n ℓ : ℕ}

/-- The keep condition of the non-hs nodes of a class with `N` nodes and `z` zeros. -/
def keepC (N z : ℕ) : Prop := (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z

instance (N z : ℕ) : Decidable (keepC N z) := by unfold keepC; infer_instance

theorem q_one_add_delta (hq : 0 < q) : (q : ℝ) * (1 + deltaOf q d) = d + 2 := by
  unfold deltaOf
  have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

/-- The per-node bound of the relaxation. -/
theorem node_relax [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2)
    (hq : 0 < q) {k : ℤ} (hk : k ∈ nodes n) {N z : ℕ} (hN : Ncl n ℓ k = N) (hz : Zcl n ℓ k = z)
    (s : ℕ) :
    ((gval q d n ℓ k s + (s : ℤ) ^ 2 : ℤ) : ℝ) ≤
      if (ℓ : ℤ) ≤ 2 * |k| - 1 then (q : ℝ) * ((((N : ℤ) - z : ℤ) : ℝ) + (1 + deltaOf q d)) * s
      else if keepC N z then (q : ℝ) * (((N : ℤ) - z : ℤ) : ℝ) * s else (s : ℝ) ^ 2 := by
  have hδ := q_one_add_delta (d := d) hq
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hD := Dk_single (q := q) hn hn1 hsl hk
  rw [hN, hz] at hD
  split_ifs with hhs hkeep
  · -- hs node: active
    have hact : muI n ℓ k = 1 ∨ hsI ℓ k = 1 := Or.inr (by unfold hsI; rw [if_pos hhs])
    have hc : cK q d ℓ k = (q : ℤ) + d + 1 := by
      unfold cK hsI; rw [if_pos hhs, if_pos rfl]
    unfold gval
    rw [if_pos hact, hD, hc]
    push_cast
    have : (q : ℝ) * ((N : ℝ) - z + (1 + deltaOf q d)) * s =
        s * ((q : ℝ) * ((N : ℝ) - z) + (q * (1 + deltaOf q d))) := by ring
    rw [this, hδ]
    nlinarith
  · -- kept non-hs node: active through `μ = 1`
    have hmu : muI n ℓ k = 1 := by unfold muI; rw [hN, hz, if_pos hkeep.1]
    have hc : cK q d ℓ k = (q : ℤ) - 1 := by
      unfold cK hsI; rw [if_neg hhs]; simp
    unfold gval
    rw [if_pos (Or.inl hmu), hD, hc]
    push_cast
    nlinarith
  · -- the other nodes
    unfold gval
    split_ifs with hact
    · have hc : cK q d ℓ k = (q : ℤ) - 1 := by
        unfold cK hsI; rw [if_neg hhs]; simp
      rw [hD, hc]
      have hmu : muI n ℓ k = 1 := by
        rcases hact with h | h
        · exact h
        · unfold hsI at h; rw [if_neg hhs] at h; exact absurd h (by norm_num)
      have hc1 : 2 ≤ N ∨ 1 ≤ z := by
        unfold muI at hmu; rw [hN, hz] at hmu
        by_contra hc; rw [if_neg hc] at hmu; exact absurd hmu (by norm_num)
      have hv : (N : ℤ) - z ≤ 0 := by
        unfold keepC at hkeep; push_neg at hkeep; have := hkeep hc1; omega
      have hv' : ((N : ℝ) - z) ≤ 0 := by exact_mod_cast hv
      push_cast
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith [mul_nonneg hs0 hq0, mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs0 hq0) hv']
    · push_cast; linarith

/-- The class bound of the relaxation:
`∑_{k ∈ c} (g(k, s_k) + s_k²) − S_c² ≤ q² ψ̃(α_c, τ) + q τ S_c`. -/
theorem class_relax [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2)
    (hq : 0 < q) (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ q) {τ : ℝ} (hτ : 0 ≤ τ) (c : ℕ) :
    ((∑ i ∈ cls n ℓ c, (gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2) -
        ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) ≤
      (q : ℝ) ^ 2 * knap (classAlphas n ℓ (deltaOf q d) c) τ +
        q * τ * ((∑ i ∈ cls n ℓ c, s i : ℕ) : ℝ) := by
  set C := cls n ℓ c
  set N := C.card
  set z := zc n ℓ c
  set hsP : Fin (2 * R n + 1) → Prop := fun i => (ℓ : ℤ) ≤ 2 * |nodeOf n i| - 1
  set a : ℝ := (((N : ℤ) - z : ℤ) : ℝ) + (1 + deltaOf q d)
  set b : ℝ := (((N : ℤ) - z : ℤ) : ℝ)
  set nh := nhs n ℓ c
  set mk := if keepC N z then N - nh else 0
  -- the three partial sums
  set H : ℕ := ∑ i ∈ C, if hsP i then s i else 0
  set P : ℕ := ∑ i ∈ C, if ¬hsP i ∧ keepC N z then s i else 0
  set O : ℕ := ∑ i ∈ C, if ¬hsP i ∧ ¬keepC N z then s i else 0
  have hS : ∑ i ∈ C, s i = H + P + O := by
    simp only [H, P, O, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp_all
  have hO2 : ∑ i ∈ C, (if ¬hsP i ∧ ¬keepC N z then s i else 0) ^ 2 ≤ O ^ 2 :=
    sq_sum_ge_sum_sq C _
  -- the node bounds summed
  have hnode : ∀ i ∈ C, ((gval q d n ℓ (nodeOf n i) (s i) + (s i : ℤ) ^ 2 : ℤ) : ℝ) ≤
      q * a * ((if hsP i then s i else 0 : ℕ) : ℝ) +
        q * b * ((if ¬hsP i ∧ keepC N z then s i else 0 : ℕ) : ℝ) +
        (((if ¬hsP i ∧ ¬keepC N z then s i else 0 : ℕ) ^ 2 : ℕ) : ℝ) := by
    intro i hi
    have h := node_relax (d := d) (N := N) (z := z) hn hn1 hsl hq (nodeOf_mem_nodes' n i)
      (Ncl_eq_card hi) (Zcl_eq_zc hi) (s i)
    refine h.trans (le_of_eq ?_)
    by_cases h1 : hsP i
    · have h1' : (ℓ : ℤ) ≤ 2 * |nodeOf n i| - 1 := h1
      rw [if_pos h1', if_pos h1, if_neg (show ¬(¬hsP i ∧ keepC N z) from fun h => h.1 h1),
        if_neg (show ¬(¬hsP i ∧ ¬keepC N z) from fun h => h.1 h1)]
      simp only [a]; push_cast; ring
    · have h1' : ¬ (ℓ : ℤ) ≤ 2 * |nodeOf n i| - 1 := h1
      by_cases h2 : keepC N z
      · rw [if_neg h1', if_pos h2, if_neg h1, if_pos (show ¬hsP i ∧ keepC N z from ⟨h1, h2⟩),
          if_neg (show ¬(¬hsP i ∧ ¬keepC N z) from fun h => h.2 h2)]
        simp only [b]; push_cast; ring
      · rw [if_neg h1', if_neg h2, if_neg h1, if_neg (show ¬(¬hsP i ∧ keepC N z) from fun h => h2 h.2),
          if_pos (show ¬hsP i ∧ ¬keepC N z from ⟨h1, h2⟩)]
        push_cast; ring
  have hsum := sum_le_sum hnode
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  push_cast at hsum
  have hO2' : ∑ i ∈ C, (if ¬hsP i ∧ ¬keepC N z then (s i : ℝ) else 0) ^ 2 ≤ (O : ℝ) ^ 2 := by
    have : ((∑ i ∈ C, (if ¬hsP i ∧ ¬keepC N z then s i else 0) ^ 2 : ℕ) : ℝ) ≤ ((O ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hO2
    push_cast at this
    exact this
  have eH : ∑ i ∈ C, (if hsP i then (s i : ℝ) else 0) = H := by simp only [H]; push_cast; rfl
  have eP : ∑ i ∈ C, (if ¬hsP i ∧ keepC N z then (s i : ℝ) else 0) = P := by
    simp only [P]; push_cast; rfl
  -- bounds on `H` and `P`
  have hHle : H ≤ q * nh := by
    simp only [H, nh, nhs]
    rw [← sum_filter]
    refine (sum_le_card_nsmul _ _ q fun i _ => hs i).trans ?_
    rw [smul_eq_mul, mul_comm]
  have hPle : P ≤ q * mk := by
    simp only [P, mk]
    split_ifs with hk
    · have : ∑ i ∈ C, (if ¬hsP i ∧ keepC N z then s i else 0) = ∑ i ∈ C.filter (fun i => ¬hsP i), s i := by
        rw [sum_filter]; exact sum_congr rfl fun i _ => by simp [hk]
      rw [this]
      refine (sum_le_card_nsmul _ _ q fun i _ => hs i).trans ?_
      rw [smul_eq_mul, mul_comm]
      have e1 : nh = (C.filter fun i => hsP i).card := rfl
      have e2 : (C.filter fun i => hsP i).card + (C.filter fun i => ¬ hsP i).card = N :=
        card_filter_add_card_filter_not _
      refine Nat.mul_le_mul_left _ ?_
      omega
    · simp [hk]
  -- the knapsack
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : (0 : ℝ) ≤ H / q := by positivity
  have hxA : (H : ℝ) / q ≤ nh := by
    rw [div_le_iff₀ hqR]; have : (H : ℝ) ≤ q * nh := by exact_mod_cast hHle
    linarith
  have hy0 : (0 : ℝ) ≤ P / q := by positivity
  have hyB : (P : ℝ) / q ≤ mk := by
    rw [div_le_iff₀ hqR]; have : (P : ℝ) ≤ q * mk := by exact_mod_cast hPle
    linarith
  have hk := le_knap_two nh mk a b τ _ _ hx0 hxA hy0 hyB
  have hα : classAlphas n ℓ (deltaOf q d) c = List.replicate nh a ++ List.replicate mk b := by
    unfold classAlphas
    rw [alphasR_runsOf]
    rfl
  rw [← hα] at hk
  -- combine
  have hk' : q * a * H + q * b * P - ((H : ℝ) + P) ^ 2 - q * τ * (H + P) ≤
      (q : ℝ) ^ 2 * knap (classAlphas n ℓ (deltaOf q d) c) τ := by
    have e : q * a * H + q * b * P - ((H : ℝ) + P) ^ 2 - q * τ * (H + P) =
        (q : ℝ) ^ 2 * (a * (H / q) + b * (P / q) - (H / q + P / q) ^ 2 - τ * (H / q + P / q)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  have hScast : ((∑ i ∈ C, s i : ℕ) : ℝ) = H + P + O := by rw [hS]; push_cast; ring
  push_cast
  rw [eH, eP] at hsum
  have hSc : ((∑ i ∈ C, s i : ℕ) : ℝ) = ∑ i ∈ C, (s i : ℝ) := by push_cast; rfl
  rw [← hSc, hScast]
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hO0 : (0 : ℝ) ≤ O := Nat.cast_nonneg _
  have hqτ : 0 ≤ (q : ℝ) * τ := by positivity
  nlinarith [mul_nonneg hqτ hO0, mul_nonneg (add_nonneg hH0 hP0) hO0]

/-- **II, Lemma 5.3 with weak duality at `λ = qτ`.** -/
theorem relax_bound [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (hsl : 4 * n < ℓ ^ 2) (hq : 0 < q) {τ : ℝ} (hτ : 0 ≤ τ) :
    (TPplus q d n ℓ (q * n) : ℝ) ≤
      (q : ℝ) ^ 2 * (τ * n + ∑ c ∈ range ℓ, knap (classAlphas n ℓ (deltaOf q d) c) τ) := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  have hB : 0 ≤ (q : ℝ) ^ 2 * (τ * n + ∑ c ∈ range ℓ, knap (classAlphas n ℓ (deltaOf q d) c) τ) := by
    have := sum_nonneg fun c (_ : c ∈ range ℓ) => knap_nonneg (classAlphas n ℓ (deltaOf q d) c) τ
    positivity
  refine TPplus_le_of hB fun s hs => ⟨_, tree_sum_le_classes hn hn1 h2 hsl s, ?_⟩
  have hsq := profile_le hs
  push_cast
  have h1 := sum_le_sum fun c (_ : c ∈ range ℓ) => class_relax (d := d) hn hn1 hsl hq s hsq hτ c
  push_cast at h1
  refine h1.trans (le_of_eq ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have := sum_S_cls hℓ0 hs
  push_cast at this
  rw [this]
  ring

end TwoAdicWin.Asm
