import RequestProject.Zeta7.Hankel2.Thm81Ranges
import RequestProject.Zeta7.Hankel2.CircleCont

/-!
# Class types and class values `V_t`, `ψ_t` (paper §8.3–§8.4)

For a single-level prime (`p² > 6n`) every node `k` has `D_k = 4 o_k − 6 z_k − g_k`
(`Dk_eq_single`), and `f⁺(k, s)` depends only on the node data `(D_k, μ_k, hs_k, 1[o_k > 0])`
(`fPlus_eq_fPlusT`).  In a class with `N` nodes and `z` zeros (and `g ∈ {0,1}`) all nodes have
`o = N − 1`, `z`, `g` and `μ = 1[o + z + g > 0]`, so the class value `V_c(S)` only depends on the
**type** `(N, z, h)` (`h` = number of `hs`-nodes) and on `g`:

* `VT t g S` is `V_t(S) = max_{∑ s_k = S} [∑_k f⁺(k, s_k) − S² + ∑_k s_k²]`, written in terms of the
  numbers `a_j` (resp. `b_j`) of `hs`-nodes (resp. non-`hs` nodes) carrying `s_k = j`;
* `psiT t g λ` is `ψ_t(λ) = max_S (V_t(S) − λ S)` (`psiT_spec`).

Main results:
* `Vc_sub_le_psiT`: for a class `c` not containing the node `n/2` (`g = 0`),
  `V_c(S) − λ S ≤ ψ_{t(c)}(λ)` where `t(c) = (N_c, z_c, h_c)` is its type;
* `Vc_sub_le_crude`: for every class, `V_c(S) − λ S ≤ N(16N + 34) + 4N|λ|`;
* `psiT_nonneg`, `psiT_le`: `0 ≤ ψ_t(λ) ≤ N(16N + 34) + 4N|λ|`.
-/

open Finset

namespace Hankel2.Fam3

/-! ### `f⁺` as a function of the node data -/

/-- The `β`-part of `v̄_a` for node data `(D, μ, hs)`. -/
noncomputable def vbarBetaT (D : ℤ) (mu hs : ℕ) (a : ℕ) : ℤ :=
  if h : a ≤ 3 then (Icc 1 (4 - a)).inf' (nonempty_Icc.2 (by omega)) fun i =>
    -D - ((4 - i - a : ℕ) : ℤ) * mu - ((i + 4 : ℕ) : ℤ) * hs
  else 0

/-- `v̄_a` for node data `(D, μ, hs)`. -/
noncomputable def vbarT (D : ℤ) (mu hs a : ℕ) : ℤ :=
  if a ≤ 1 then min (vbarBetaT D mu hs a) (-D - ((1 - a : ℕ) : ℤ) * mu) else vbarBetaT D mu hs a

/-- The unclipped `f⁺` for node data `(D, μ, hs, 1[o > 0])`. -/
noncomputable def fPlusRawT (D : ℤ) (mu hs oi s : ℕ) : WithBot ℤ :=
  (univ.filter fun R : Finset (Fin 4) => R.card = s).sup fun R =>
    (admPerms R).sup fun σ =>
      (((∑ i, -vbarT D mu hs (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i)) +
        (ellR R : ℤ) * oi : ℤ) : WithBot ℤ)

/-- `f⁺` (clipped at `0`) for node data `(D, μ, hs, 1[o > 0])`. -/
noncomputable def fPlusT (D : ℤ) (mu hs oi s : ℕ) : ℤ :=
  WithBot.unbotD 0 (max (fPlusRawT D mu hs oi s) 0)

theorem fPlus_eq_fPlusT (p n : ℕ) (k : ℤ) (s : ℕ) :
    fPlus p n k s = fPlusT (Dk p n k) (muI p n k) (hsK p k) (oI p n k) s := rfl


/-! ### The bound `f⁺ ≤ 4 max(D + 3μ + 8 hs, 0) + 6·1[o>0]` -/

theorem vbarBetaT_ge (D : ℤ) (mu hs : ℕ) {a : ℕ} (ha : a ≤ 3) :
    -D - 3 * (mu : ℤ) - 8 * (hs : ℤ) ≤ vbarBetaT D mu hs a := by
  unfold vbarBetaT
  rw [dif_pos ha]
  refine Finset.le_inf' _ _ fun i hi => ?_
  obtain ⟨h1, h2⟩ := mem_Icc.1 hi
  have e1 : ((4 - i - a : ℕ) : ℤ) ≤ 3 := by omega
  have e2 : ((i + 4 : ℕ) : ℤ) ≤ 8 := by omega
  have := mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg (α := ℤ) mu)
  have := mul_le_mul_of_nonneg_right e2 (Nat.cast_nonneg (α := ℤ) hs)
  linarith

theorem vbarT_ge (D : ℤ) (mu hs : ℕ) {a : ℕ} (ha : a ≤ 3) :
    -D - 3 * (mu : ℤ) - 8 * (hs : ℤ) ≤ vbarT D mu hs a := by
  have h := vbarBetaT_ge D mu hs ha
  unfold vbarT
  split_ifs with h1
  · refine le_min h ?_
    have e : ((1 - a : ℕ) : ℤ) ≤ 1 := by omega
    have := mul_le_mul_of_nonneg_right e (Nat.cast_nonneg (α := ℤ) mu)
    have : (0 : ℤ) ≤ hs := Nat.cast_nonneg _
    linarith
  · exact h

theorem ellR_le_six (R : Finset (Fin 4)) : ellR R ≤ 6 := by
  unfold ellR
  have : ∑ r ∈ R, (r : ℕ) ≤ ∑ r : Fin 4, (r : ℕ) := Finset.sum_le_sum_of_subset (Finset.subset_univ R)
  simp [Fin.sum_univ_four] at this
  omega

/-- A crude bound on `f⁺`. -/
theorem fPlusT_le (D : ℤ) (mu hs oi s : ℕ) :
    fPlusT D mu hs oi s ≤ 4 * max (D + 3 * mu + 8 * hs) 0 + 6 * oi := by
  set B := max (D + 3 * (mu : ℤ) + 8 * hs) 0
  have hB : 0 ≤ B := le_max_right _ _
  have hraw : fPlusRawT D mu hs oi s ≤ ((4 * B + 6 * oi : ℤ) : WithBot ℤ) := by
    unfold fPlusRawT
    refine Finset.sup_le fun R hR => Finset.sup_le fun σ hσ => WithBot.coe_le_coe.2 ?_
    have hadm := (Finset.mem_filter.1 hσ).2
    have hterm : ∀ i : Fin R.card,
        -vbarT D mu hs (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i) ≤ B := by
      intro i
      have := vbarT_ge D mu hs (a := ((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i) (hadm i)
      have : D + 3 * (mu : ℤ) + 8 * hs ≤ B := le_max_left _ _
      linarith
    have h1 : ∑ i, -vbarT D mu hs (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i) ≤ R.card * B := by
      calc _ ≤ ∑ _i : Fin R.card, B := Finset.sum_le_sum fun i _ => hterm i
        _ = R.card * B := by simp
    have h2 : (R.card : ℤ) ≤ 4 := by
      have := Finset.card_le_univ R; simp at this; exact_mod_cast this
    have h3 : (ellR R : ℤ) * oi ≤ 6 * oi := by
      have := ellR_le_six R
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (Nat.cast_nonneg _)
    nlinarith
  unfold fPlusT
  have h0 : (0 : ℤ) ≤ 4 * B + 6 * oi := by positivity
  induction h : fPlusRawT D mu hs oi s with
  | bot => simp; exact h0
  | coe r =>
    rw [h] at hraw
    have hr : r ≤ 4 * B + 6 * oi := WithBot.coe_le_coe.1 hraw
    rcases le_total r 0 with hr0 | hr0
    · rw [max_eq_right (by exact_mod_cast hr0)]; simpa using h0
    · rw [max_eq_left (by exact_mod_cast hr0)]; simpa using hr

theorem fPlusT_zero (D : ℤ) (mu hs oi : ℕ) : fPlusT D mu hs oi 0 = 0 := by
  unfold fPlusT fPlusRawT
  have : (univ.filter fun R : Finset (Fin 4) => R.card = 0) = {∅} := by
    ext R; simp [Finset.card_eq_zero]
  rw [this, Finset.sup_singleton]
  have hadm : admPerms (∅ : Finset (Fin 4)) = univ := by
    ext σ; simp [admPerms]
  rw [hadm]
  simp [ellR]

/-! ### Class types and the class values `V_t(S)`, `ψ_t(λ)` -/

/-- `D = 4(N − 1) − 6z − g` for a class with `N` nodes and `z` zeros. -/
def DT (N z g : ℕ) : ℤ := 4 * ((N : ℤ) - 1) - 6 * z - g

/-- `μ = 1[o + z + g > 0]`, `o = N − 1`. -/
def muT (N z g : ℕ) : ℕ := if 0 < N - 1 + z + g then 1 else 0

/-- `1[o > 0]`, `o = N − 1`. -/
def oiT (N : ℕ) : ℕ := if 0 < N - 1 then 1 else 0

/-- `f⁺(k, s)` of a node of `hs`-value `hs` in a class of type `t = (N, z, h)` with flag `g`. -/
noncomputable def typeF (t : Circle.CType) (g hs s : ℕ) : ℤ :=
  fPlusT (DT t.1 t.2.1 g) (muT t.1 t.2.1 g) hs (oiT t.1) s

/-- The node-count data of a class with `N` nodes, `h` of them `hs`-nodes: `a j` (resp. `b j`)
is the number of `hs`-nodes (resp. non-`hs` nodes) carrying `s_k = j`, `0 ≤ j ≤ 4`. -/
def cntVecs (N h : ℕ) : Finset ((Fin 5 → ℕ) × (Fin 5 → ℕ)) :=
  (Fintype.piFinset (fun _ => range (h + 1)) ×ˢ Fintype.piFinset (fun _ => range (N - h + 1))).filter
    fun ab => ∑ j, ab.1 j = h ∧ ∑ j, ab.2 j = N - h

/-- `S = ∑_k s_k` of count data. -/
def cvS (ab : (Fin 5 → ℕ) × (Fin 5 → ℕ)) : ℕ := ∑ j : Fin 5, (j : ℕ) * (ab.1 j + ab.2 j)

/-- `∑_k f⁺(k, s_k) + ∑_k s_k²` of count data. -/
noncomputable def cvF (t : Circle.CType) (g : ℕ) (ab : (Fin 5 → ℕ) × (Fin 5 → ℕ)) : ℤ :=
  ∑ j : Fin 5, ((ab.1 j : ℤ) * typeF t g 1 j + (ab.2 j : ℤ) * typeF t g 0 j +
    ((j : ℕ) : ℤ) ^ 2 * (ab.1 j + ab.2 j))

/-- **The class value** `V_t(S) = max_{∑ s_k = S} [∑_k f⁺(k, s_k) − S² + ∑_k s_k²]` of a class of
type `t = (N, z, h)` with flag `g` (`⊥` if `S > 4N`). -/
noncomputable def VT (t : Circle.CType) (g S : ℕ) : WithBot ℤ :=
  ((cntVecs t.1 t.2.2).filter fun ab => cvS ab = S).sup fun ab =>
    ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : WithBot ℤ)

theorem cntVecs_nonempty (N h : ℕ) : (cntVecs N h).Nonempty := by
  refine ⟨(Pi.single 0 h, Pi.single 0 (N - h)), Finset.mem_filter.2 ⟨?_, ?_, ?_⟩⟩
  · simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun j => ?_, fun j => ?_⟩ <;> by_cases hj : j = 0 <;> simp [hj, Pi.single_apply]
  · simp
  · simp

/-- `ψ_t(λ) = max_S (V_t(S) − λ S)` (see `psiT_spec`). -/
noncomputable def psiT (t : Circle.CType) (g : ℕ) (lam : ℝ) : ℝ :=
  (cntVecs t.1 t.2.2).sup' (cntVecs_nonempty _ _) fun ab =>
    ((cvF t g ab - (cvS ab : ℤ) ^ 2 : ℤ) : ℝ) - lam * cvS ab

/-- `ψ_t(λ) = max_S (V_t(S) − λ S)`: it bounds every `V_t(S) − λ S` and is attained. -/
theorem psiT_spec (t : Circle.CType) (g : ℕ) (lam : ℝ) :
    (∀ S : ℕ, ∀ v : ℤ, VT t g S = v → (v : ℝ) - lam * S ≤ psiT t g lam) ∧
      ∃ S : ℕ, ∃ v : ℤ, VT t g S = v ∧ psiT t g lam = (v : ℝ) - lam * S := by
  constructor
  · intro S v hv
    unfold VT at hv
    set D := (cntVecs t.1 t.2.2).filter fun ab => cvS ab = S
    rcases D.eq_empty_or_nonempty with hD | hD
    · rw [hD, Finset.sup_empty] at hv; exact absurd hv WithBot.bot_ne_coe
    obtain ⟨ab, hab, hv'⟩ := Finset.exists_mem_eq_sup D hD
      (fun ab => ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : WithBot ℤ))
    rw [hv', WithBot.coe_inj] at hv
    have hS := (Finset.mem_filter.1 hab).2
    have := Finset.le_sup' (fun ab => ((cvF t g ab - (cvS ab : ℤ) ^ 2 : ℤ) : ℝ) - lam * cvS ab)
      (Finset.mem_filter.1 hab).1
    unfold psiT
    rw [← hv]; simp only [hS] at this ⊢; exact this
  · obtain ⟨ab, hab, heq⟩ := Finset.exists_mem_eq_sup' (cntVecs_nonempty t.1 t.2.2)
      (fun ab => ((cvF t g ab - (cvS ab : ℤ) ^ 2 : ℤ) : ℝ) - lam * cvS ab)
    set S := cvS ab
    have hmem : ab ∈ (cntVecs t.1 t.2.2).filter fun ab' => cvS ab' = S :=
      Finset.mem_filter.2 ⟨hab, rfl⟩
    -- `V_t(S)` is finite; its maximiser is also a candidate for `ψ`
    set D := (cntVecs t.1 t.2.2).filter fun ab' => cvS ab' = S
    obtain ⟨ab', hab', hv'⟩ := Finset.exists_mem_eq_sup D ⟨ab, hmem⟩
      (fun ab => ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : WithBot ℤ))
    refine ⟨S, cvF t g ab' - (S : ℤ) ^ 2, hv', le_antisymm ?_ ?_⟩
    · unfold psiT; rw [heq]
      have h1 : ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : WithBot ℤ) ≤ ((cvF t g ab' - (S : ℤ) ^ 2 : ℤ)) := by
        rw [← hv']; exact Finset.le_sup (f := fun ab => ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : WithBot ℤ)) hmem
      have h2 : ((cvF t g ab - (S : ℤ) ^ 2 : ℤ) : ℝ) ≤ ((cvF t g ab' - (S : ℤ) ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast WithBot.coe_le_coe.1 h1
      simp only [S] at h2 ⊢; linarith
    · have hS' := (Finset.mem_filter.1 hab').2
      have := Finset.le_sup' (fun ab => ((cvF t g ab - (cvS ab : ℤ) ^ 2 : ℤ) : ℝ) - lam * cvS ab)
        (Finset.mem_filter.1 hab').1
      unfold psiT; simp only [hS'] at this; exact this

theorem psiT_nonneg (t : Circle.CType) (g : ℕ) (lam : ℝ) : 0 ≤ psiT t g lam := by
  have hmem : (Pi.single 0 t.2.2, Pi.single 0 (t.1 - t.2.2)) ∈ cntVecs t.1 t.2.2 := by
    refine Finset.mem_filter.2 ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun j => ?_, fun j => ?_⟩ <;> by_cases hj : j = 0 <;> simp [hj, Pi.single_apply]
    · simp
    · simp
  refine le_trans ?_ (Finset.le_sup' _ hmem)
  have hS : cvS (Pi.single 0 t.2.2, Pi.single 0 (t.1 - t.2.2)) = 0 := by
    unfold cvS
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  have hF : cvF t g (Pi.single 0 t.2.2, Pi.single 0 (t.1 - t.2.2)) = 0 := by
    unfold cvF
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = 0
    · subst hj; simp [typeF, fPlusT_zero]
    · simp [hj]
  simp only [hS, hF]; simp


theorem typeF_le (t : Circle.CType) (g : ℕ) {hs : ℕ} (hhs : hs ≤ 1) (s : ℕ) :
    typeF t g hs s ≤ 16 * t.1 + 34 := by
  have h := fPlusT_le (DT t.1 t.2.1 g) (muT t.1 t.2.1 g) hs (oiT t.1) s
  have hmu : muT t.1 t.2.1 g ≤ 1 := by unfold muT; split_ifs <;> omega
  have hoi : oiT t.1 ≤ 1 := by unfold oiT; split_ifs <;> omega
  have hD : DT t.1 t.2.1 g ≤ 4 * (t.1 : ℤ) - 4 := by unfold DT; omega
  have hmax : max (DT t.1 t.2.1 g + 3 * (muT t.1 t.2.1 g : ℤ) + 8 * hs) 0 ≤ 4 * (t.1 : ℤ) + 7 := by
    apply max_le _ (by positivity)
    have : (muT t.1 t.2.1 g : ℤ) ≤ 1 := by exact_mod_cast hmu
    have : (hs : ℤ) ≤ 1 := by exact_mod_cast hhs
    linarith
  have : (oiT t.1 : ℤ) ≤ 1 := by exact_mod_cast hoi
  unfold typeF; linarith

theorem sum_cnt_eq (N h : ℕ) (hh : h ≤ N) {ab : (Fin 5 → ℕ) × (Fin 5 → ℕ)} (hab : ab ∈ cntVecs N h) :
    ∑ j : Fin 5, (ab.1 j + ab.2 j) = N := by
  obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hab
  rw [Finset.sum_add_distrib, h1, h2]; omega

/-- **Bound on `ψ_t`** (paper Lemma 8.7): `ψ_t(λ) ≤ N(16N + 50) + 4N|λ|` for a type
`t = (N, z, h)` with `h ≤ N`. -/
theorem psiT_le (t : Circle.CType) (g : ℕ) (lam : ℝ) (hh : t.2.2 ≤ t.1) :
    psiT t g lam ≤ t.1 * (16 * t.1 + 50) + 4 * t.1 * |lam| := by
  unfold psiT
  refine Finset.sup'_le _ _ fun ab hab => ?_
  have hN := sum_cnt_eq t.1 t.2.2 hh hab
  have hNr : ∑ j : Fin 5, ((ab.1 j : ℝ) + ab.2 j) = t.1 := by exact_mod_cast hN
  have hS : (cvS ab : ℝ) ≤ 4 * t.1 := by
    unfold cvS; push_cast
    rw [← hNr, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have : ((j : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (Nat.lt_succ_iff.1 j.isLt)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hS0 : (0 : ℝ) ≤ cvS ab := Nat.cast_nonneg _
  have hF : (cvF t g ab : ℝ) ≤ t.1 * (16 * t.1 + 34) + 16 * t.1 := by
    unfold cvF; push_cast
    calc ∑ j : Fin 5, ((ab.1 j : ℝ) * (typeF t g 1 j : ℝ) + (ab.2 j : ℝ) * (typeF t g 0 j : ℝ) +
          ((j : ℕ) : ℝ) ^ 2 * ((ab.1 j : ℝ) + ab.2 j))
        ≤ ∑ j : Fin 5, (((ab.1 j : ℝ) + ab.2 j) * (16 * t.1 + 34) + 16 * ((ab.1 j : ℝ) + ab.2 j)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have e1 : (typeF t g 1 j : ℝ) ≤ 16 * t.1 + 34 := by exact_mod_cast typeF_le t g le_rfl j
          have e0 : (typeF t g 0 j : ℝ) ≤ 16 * t.1 + 34 := by exact_mod_cast typeF_le t g (by norm_num) j
          have ej : ((j : ℕ) : ℝ) ^ 2 ≤ 16 := by
            have : ((j : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (Nat.lt_succ_iff.1 j.isLt)
            have : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
            nlinarith
          have := mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg (α := ℝ) (ab.1 j))
          have := mul_le_mul_of_nonneg_left e0 (Nat.cast_nonneg (α := ℝ) (ab.2 j))
          have := mul_le_mul_of_nonneg_right ej (show (0 : ℝ) ≤ (ab.1 j : ℝ) + ab.2 j by positivity)
          nlinarith
      _ = t.1 * (16 * t.1 + 34) + 16 * t.1 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hNr]
  have hlam : -(lam * cvS ab) ≤ 4 * t.1 * |lam| := by
    have := neg_abs_le lam
    have h1 : -(lam * cvS ab) ≤ |lam| * cvS ab := by nlinarith [abs_nonneg lam]
    have h2 : |lam| * cvS ab ≤ |lam| * (4 * t.1) := mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    linarith
  push_cast
  nlinarith

/-! ### Single-level primes: the node data of a class -/

section Single

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem padicValInt_eq_ite (h6 : 6 * n < p ^ 2) {x : ℤ} (hx0 : x ≠ 0) (h1 : -(4 * n : ℤ) ≤ x)
    (h2 : x ≤ 4 * n) : (padicValInt p x : ℤ) = if (p : ℤ) ∣ x then 1 else 0 := by
  have := padicValInt_eq_sum_levels hx0 (N := 1)
    (padicValInt_le_of_abs_le (four_n_lt_pow_one h6) h1 h2)
  rw [this]
  by_cases hx : (p : ℤ) ∣ x
  · simp [hx, Finset.filter_singleton]
  · simp [hx, Finset.filter_singleton]


/-- For `p² > 6n` and odd `n`: `D_k = 4 o_k − 6 z_k − g_k`. -/
theorem Dk_eq_single (h6 : 6 * n < p ^ 2) (hn : n % 2 = 1) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    Dk p n k = 4 * (oK p n k : ℤ) - 6 * (zK p n k : ℤ) - (gK p n k : ℤ) := by
  have hk' := Finset.mem_Icc.1 hk
  unfold Dk oK zK gK cntL zL
  have e1 : ∑ m ∈ (Fam3PF.nodes n).erase k, (padicValInt p (k - m) : ℤ) =
      ∑ m ∈ (Fam3PF.nodes n).erase k, (if (p : ℤ) ∣ k - m then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hne, hm'⟩ := Finset.mem_erase.1 hm
    have := Finset.mem_Icc.1 hm'
    exact padicValInt_eq_ite h6 (sub_ne_zero.2 (Ne.symm hne)) (by omega) (by omega)
  have e2 : ∑ j ∈ range n, (padicValInt p (2 * k - 2 * j - 1) : ℤ) =
      ∑ j ∈ range n, (if (p : ℤ) ∣ 2 * k - 2 * (j : ℤ) - 1 then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    exact padicValInt_eq_ite h6 (by omega) (by omega) (by omega)
  have e3 : (padicValInt p ((n : ℤ) - 2 * k) : ℤ) = if (p : ℤ) ∣ (n : ℤ) - 2 * k then 1 else 0 :=
    padicValInt_eq_ite h6 (by omega) (by omega) (by omega)
  rw [e1, e2, e3, Finset.sum_boole, Finset.sum_boole]
  split_ifs <;> simp

end Single



/-! ### The type of a residue class and `V_c(S) − λS ≤ ψ_{t(c)}(λ)` -/

/-- The nodes of the residue class `c` mod `p`. -/
def clsC (p n c : ℕ) : Finset (Fin (3 * n + 1)) := univ.filter fun i => nodeOf n i % (p : ℤ) = c

/-- The number `h_c` of `hs`-nodes in the class `c`. -/
def hsCnt (p n c : ℕ) : ℕ := #{i ∈ clsC p n c | hsK p (nodeOf n i) = 1}

/-- The flag `g_c = 1[p ∣ n − 2c]` of the class `c` (the class containing `n/2`). -/
def gC (p n c : ℕ) : ℕ := if (p : ℤ) ∣ (n : ℤ) - 2 * c then 1 else 0

/-- The type `t(c) = (N_c, z_c, h_c)` of the residue class `c` mod `p`. -/
def clsType (p n c : ℕ) : Circle.CType := (clsN n p c, zL n p c, hsCnt p n c)

theorem card_clsC (p n c : ℕ) : (clsC p n c).card = clsN n p c := by
  unfold clsC clsN
  refine Finset.card_bij (fun i _ => nodeOf n i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.2 ⟨nodeOf_mem n i, hi⟩
  · intro i _ j _ h
    simp only [nodeOf] at h
    exact Fin.ext (by omega)
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have := Finset.mem_Icc.1 hm1
    refine ⟨⟨(m + n).toNat, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, nodeOf]
      rw [show (((m + n).toNat : ℕ) : ℤ) - n = m by omega]; exact hm2
    · simp only [nodeOf]; omega

theorem hsCnt_le (p n c : ℕ) : hsCnt p n c ≤ clsN n p c := by
  rw [← card_clsC]; exact Finset.card_filter_le _ _

theorem hsK_le_one (p : ℕ) (k : ℤ) : hsK p k ≤ 1 := by unfold hsK; split_ifs <;> omega

theorem dvd_n_sub_two_iff {p n c : ℕ} {k : ℤ} (hk : k % (p : ℤ) = c) :
    (p : ℤ) ∣ (n : ℤ) - 2 * k ↔ (p : ℤ) ∣ (n : ℤ) - 2 * c := by
  have e : (n : ℤ) - 2 * k = ((n : ℤ) - 2 * c) - (p : ℤ) * (2 * (k / p)) := by
    have := Int.emod_add_mul_ediv k p; rw [hk] at this; linarith
  rw [e, dvd_sub_left (dvd_mul_right _ _)]

/-- For `p² > 6n` and odd `n`, the `f⁺` of a node of the class `c` is the `f⁺` of its type. -/
theorem fPlus_eq_typeF {p : ℕ} [Fact p.Prime] {n c : ℕ} (h6 : 6 * n < p ^ 2) (hn : n % 2 = 1)
    {i : Fin (3 * n + 1)} (hi : i ∈ clsC p n c) (s : ℕ) :
    fPlus p n (nodeOf n i) s = typeF (clsType p n c) (gC p n c) (hsK p (nodeOf n i)) s := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hic : nodeOf n i % (p : ℤ) = c := (Finset.mem_filter.1 hi).2
  have hk := nodeOf_mem n i
  have hN : cntL n p (nodeOf n i) + 1 = clsN n p c := by
    rw [cntL_add_one hp0 hk, hic]; rfl
  have hz : zL n p (nodeOf n i) = zL n p c := by rw [zL_emod, hic]
  have hg : gK p n (nodeOf n i) = gC p n c := by
    unfold gK gC
    by_cases h : (p : ℤ) ∣ (n : ℤ) - 2 * c
    · rw [if_pos ((dvd_n_sub_two_iff hic).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((dvd_n_sub_two_iff hic).1 h')), if_neg h]
  rw [fPlus_eq_fPlusT]
  unfold typeF clsType
  simp only
  have hD : Dk p n (nodeOf n i) = DT (clsN n p c) (zL n p c) (gC p n c) := by
    rw [Dk_eq_single h6 hn hk]; unfold DT oK zK; rw [hz, hg]; push_cast; omega
  have hmu : muI p n (nodeOf n i) = muT (clsN n p c) (zL n p c) (gC p n c) := by
    unfold muI muT oK zK; rw [hz, hg, show clsN n p c - 1 = cntL n p (nodeOf n i) by omega]
  have hoi : oI p n (nodeOf n i) = oiT (clsN n p c) := by
    unfold oI oiT oK; rw [show clsN n p c - 1 = cntL n p (nodeOf n i) by omega]
  rw [hD, hmu, hoi]

/-- Regrouping a sum over the nodes of a class by the values `(hs_k, s_k)`. -/
theorem sum_fiber_hs {ι : Type*} [DecidableEq ι] (C : Finset ι) (hs s : ι → ℕ)
    (hhs : ∀ i ∈ C, hs i ≤ 1) (hs5 : ∀ i ∈ C, s i < 5) (G : ℕ → ℕ → ℝ) :
    ∑ i ∈ C, G (hs i) (s i) = ∑ j : Fin 5, ((#{i ∈ C | hs i = 1 ∧ s i = j} : ℝ) * G 1 j +
      (#{i ∈ C | hs i = 0 ∧ s i = j} : ℝ) * G 0 j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := s) (t := range 5) fun i hi => mem_range.2 (hs5 i hi)]
  rw [Finset.sum_range (fun j => ∑ i ∈ C with s i = j, G (hs i) (s i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun i => hs i = 1)]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => G 1 j), Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    · congr 3; ext i; simp only [Finset.mem_filter]; tauto
    · intro i hi
      simp only [Finset.mem_filter] at hi
      rw [hi.2, hi.1.2]
  · rw [Finset.sum_congr rfl (g := fun _ => G 0 j), Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    · congr 3; ext i; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, h1, h2⟩; exact ⟨hi, by have := hhs i hi; omega, h1⟩
      · rintro ⟨hi, h1, h2⟩; exact ⟨hi, h2, by omega⟩
    · intro i hi
      simp only [Finset.mem_filter] at hi
      have := hhs i hi.1.1
      rw [show hs i = 0 by omega, hi.1.2]

/-- **The class value is dominated by the type value** (paper eq. (dual) and §8.4): for
`p² > 6n`, odd `n` and every class `c`, `V_c(S) − λ S ≤ ψ_{t(c)}(λ)` where `t(c)` is the type
of the class and `g_c` its flag. -/
theorem Vc_sub_le_psiT {p : ℕ} [Fact p.Prime] {n c : ℕ} (h6 : 6 * n < p ^ 2) (hn : n % 2 = 1)
    (lam : ℝ) (S : ℕ) (v : ℤ) (hv : Vc p n c S = v) :
    (v : ℝ) - lam * S ≤ psiT (clsType p n c) (gC p n c) lam := by
  classical
  set C := clsC p n c
  unfold Vc at hv
  rcases (clsProfiles p n c S).eq_empty_or_nonempty with hE | hne
  · rw [hE, Finset.sup_empty] at hv; exact absurd hv WithBot.bot_ne_coe
  obtain ⟨s, hs, hsv⟩ := Finset.exists_mem_eq_sup _ hne (fun s =>
    (((∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), fPlus p n (nodeOf n i) (s i))
      - (S : ℤ) ^ 2 + ∑ i ∈ univ.filter (fun i => nodeOf n i % (p : ℤ) = c), (s i : ℤ) ^ 2 : ℤ) :
        WithBot ℤ))
  rw [hsv, WithBot.coe_inj] at hv
  obtain ⟨hs5, hsupp, hsum⟩ : (∀ i, s i < 5) ∧ (∀ i, nodeOf n i % (p : ℤ) ≠ c → s i = 0) ∧
      ∑ i, s i = S := by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hs
    exact ⟨fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 h1 i), h2, h3⟩
  -- the count data
  set hsf : Fin (3 * n + 1) → ℕ := fun i => hsK p (nodeOf n i)
  set ab : (Fin 5 → ℕ) × (Fin 5 → ℕ) :=
    (fun j => #{i ∈ C | hsf i = 1 ∧ s i = j}, fun j => #{i ∈ C | hsf i = 0 ∧ s i = j})
  have hhs : ∀ i ∈ C, hsf i ≤ 1 := fun i _ => hsK_le_one p _
  have hfib := sum_fiber_hs C hsf s hhs (fun i _ => hs5 i)
  have hSC : ∑ i ∈ C, s i = S := by
    rw [← hsum, ← Finset.sum_filter_add_sum_filter_not univ (fun i => nodeOf n i % (p : ℤ) = c)]
    rw [Finset.sum_eq_zero (s := univ.filter fun i => ¬ nodeOf n i % (p : ℤ) = c)
      (fun i hi => hsupp i (Finset.mem_filter.1 hi).2), add_zero]
    rfl
  -- the three regrouped sums
  have eN : ∑ j : Fin 5, ((ab.1 j : ℝ) + ab.2 j) = clsN n p c := by
    have h1 : ∑ i ∈ C, (1 : ℝ) = (C.card : ℝ) := by simp
    have := hfib (fun _ _ => (1 : ℝ)); simp only [mul_one] at this
    rw [← card_clsC, ← h1, this]

  have eH : ∑ j : Fin 5, (ab.1 j : ℝ) = hsCnt p n c := by
    rw [show (hsCnt p n c : ℝ) = ∑ i ∈ C, (if hsf i = 1 then (1 : ℝ) else 0) by
      unfold hsCnt; rw [Finset.sum_boole]]
    rw [hfib (fun hs _ => if hs = 1 then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun j _ => by simp [ab]
  have eS : (cvS ab : ℝ) = S := by
    have := hfib (fun _ s => (s : ℝ))
    unfold cvS; push_cast
    rw [← hSC]; push_cast; rw [this]
    refine Finset.sum_congr rfl fun j _ => by ring
  have eF : (cvF (clsType p n c) (gC p n c) ab : ℝ) =
      ∑ i ∈ C, ((fPlus p n (nodeOf n i) (s i) : ℝ) + (s i : ℝ) ^ 2) := by
    rw [Finset.sum_congr rfl fun i hi => by rw [fPlus_eq_typeF h6 hn hi (s i)]]
    have := hfib (fun hs s => (typeF (clsType p n c) (gC p n c) hs s : ℝ) + (s : ℝ) ^ 2)
    rw [this]; unfold cvF; push_cast
    refine Finset.sum_congr rfl fun j _ => by ring
  -- membership in the count data
  have hmem : ab ∈ cntVecs (clsType p n c).1 (clsType p n c).2.2 := by
    simp only [clsType]
    have eH' : ∑ j : Fin 5, ab.1 j = hsCnt p n c := by exact_mod_cast eH
    have eN' : ∑ j : Fin 5, (ab.1 j + ab.2 j) = clsN n p c := by exact_mod_cast eN
    have eB : ∑ j : Fin 5, ab.2 j = clsN n p c - hsCnt p n c := by
      rw [Finset.sum_add_distrib, eH'] at eN'; omega
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun j => ?_,
      Fintype.mem_piFinset.2 fun j => ?_⟩, eH', eB⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff, ← eH']
      exact Finset.single_le_sum (f := ab.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    · rw [Finset.mem_range, Nat.lt_succ_iff, ← eB]
      exact Finset.single_le_sum (f := ab.2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hle := Finset.le_sup' (fun ab => ((cvF (clsType p n c) (gC p n c) ab - (cvS ab : ℤ) ^ 2 : ℤ) : ℝ)
    - lam * cvS ab) hmem
  unfold psiT
  refine le_trans (le_of_eq ?_) hle
  rw [← hv]; push_cast
  rw [eF, eS, Finset.sum_add_distrib]
  simp only [C, clsC]
  ring

/-- **A crude bound for every class** (paper Lemma 8.7): `V_c(S) − λ S ≤ N_c(16 N_c + 50) + 4 N_c |λ|`. -/
theorem Vc_sub_le_crude {p : ℕ} [Fact p.Prime] {n c : ℕ} (h6 : 6 * n < p ^ 2) (hn : n % 2 = 1)
    (lam : ℝ) (S : ℕ) (v : ℤ) (hv : Vc p n c S = v) :
    (v : ℝ) - lam * S ≤ clsN n p c * (16 * clsN n p c + 50) + 4 * clsN n p c * |lam| :=
  (Vc_sub_le_psiT h6 hn lam S v hv).trans (psiT_le _ _ _ (hsCnt_le p n c))

end Hankel2.Fam3
