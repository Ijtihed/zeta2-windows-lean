import Mathlib

/-!
# Minors of truncated Hankel blocks, for general size (P, Prop. 5.1)

For `c : ℕ → R` put `M(F, G) = det[c(F i + G j)]_{i,j<s}` for row and column index maps
`F, G : Fin s → ℕ` (`hdet`).  The main result `hdet_mem_of_std` says: every minor `M(F, G)` with
`F, G` strictly increasing lies in any additive subgroup containing all the minors
`M(R, {0, …, s−1})` with `R` strictly increasing and `∑ R + ∑_{i<s} i = ∑ F + ∑ G`.  If moreover
`c m = 0` for `m ≥ q`, only `R` with all entries `< q` are needed (`hdet_mem_of_std_trunc`).

This is the general form of the finite case check `Hankel2.hminor_reduce` (which treated `q = 4`
case by case).  The proof uses only the "self-adjointness" identity
`∑_{|I| = k} M(F + 1_I, G) = ∑_{|J| = k} M(F, G + 1_J)` (`hdet_adjoint`), which holds because the
entries depend only on `F i + G j`, and an induction on `(s² + 1) ∑ G + ∑ i·G i`.
-/

open Matrix Finset

namespace PadicWin

variable {R : Type*} [CommRing R]

/-- `M(F, G) = det[c(F i + G j)]`. -/
def hdet (c : ℕ → R) {s : ℕ} (F G : Fin s → ℕ) : R :=
  (Matrix.of fun i j => c (F i + G j)).det

/-- `F + 1_I`. -/
def bump {s : ℕ} (F : Fin s → ℕ) (I : Finset (Fin s)) : Fin s → ℕ :=
  fun i => F i + if i ∈ I then 1 else 0

/-- The standard indices `{0, …, s−1}`. -/
def stdF (s : ℕ) : Fin s → ℕ := fun i => (i : ℕ)

/-- **Self-adjointness**: `∑_{|I|=k} M(F + 1_I, G) = ∑_{|J|=k} M(F, G + 1_J)`. -/
theorem hdet_adjoint (c : ℕ → R) {s : ℕ} (F G : Fin s → ℕ) (k : ℕ) :
    ∑ I ∈ powersetCard k (univ : Finset (Fin s)), hdet c (bump F I) G =
      ∑ J ∈ powersetCard k (univ : Finset (Fin s)), hdet c F (bump G J) := by
  simp only [hdet, det_apply, of_apply, bump]
  rw [Finset.sum_comm, Finset.sum_comm (s := powersetCard k univ)]
  refine sum_congr rfl fun σ _ => ?_
  symm
  refine Finset.sum_nbij' (fun J => J.map σ.toEmbedding) (fun I => I.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [mem_powersetCard, subset_univ, true_and, card_map] at hJ ⊢
    exact hJ
  · intro I hI
    simp only [mem_powersetCard, subset_univ, true_and, card_map] at hI ⊢
    exact hI
  · intro J _
    ext x; simp
  · intro I _
    ext x; simp
  · intro J _
    congr 1
    refine prod_congr rfl fun i _ => ?_
    have : (σ i ∈ J.map σ.toEmbedding) ↔ i ∈ J := by simp
    simp only [this]
    ring_nf

theorem hdet_eq_zero_of_not_inj_left (c : ℕ → R) {s : ℕ} {F : Fin s → ℕ}
    (hF : ¬ Function.Injective F) (G : Fin s → ℕ) : hdet c F G = 0 := by
  simp only [Function.Injective, not_forall] at hF
  obtain ⟨i, j, hij, hne⟩ := hF
  exact det_zero_of_row_eq hne (by funext l; simp [hij])

theorem hdet_eq_zero_of_not_inj_right (c : ℕ → R) {s : ℕ} (F : Fin s → ℕ) {G : Fin s → ℕ}
    (hG : ¬ Function.Injective G) : hdet c F G = 0 := by
  simp only [Function.Injective, not_forall] at hG
  obtain ⟨i, j, hij, hne⟩ := hG
  exact det_zero_of_column_eq hne (by intro l; simp [hij])

theorem bump_monotone {s : ℕ} {F : Fin s → ℕ} (hF : StrictMono F) (I : Finset (Fin s)) :
    Monotone (bump F I) := by
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · have := hF h
    simp only [bump]; split_ifs <;> omega
  · rw [h]

theorem sum_bump {s : ℕ} (F : Fin s → ℕ) (I : Finset (Fin s)) :
    ∑ i, bump F I i = ∑ i, F i + I.card := by
  simp only [bump, sum_add_distrib, sum_boole, Nat.cast_id]
  congr 2
  ext; simp

theorem wsum_bump {s : ℕ} (F : Fin s → ℕ) (I : Finset (Fin s)) :
    ∑ i : Fin s, (i : ℕ) * bump F I i = ∑ i : Fin s, (i : ℕ) * F i + ∑ i ∈ I, (i : ℕ) := by
  simp only [bump, mul_add, mul_ite, mul_one, mul_zero]
  rw [sum_add_distrib, ← sum_filter]; congr 2; ext; simp

/-- `∑_{j ∈ J} j < ∑_{j ∈ top} j` for `top = {i ≥ m}`, `|J| = |top|`, `J ≠ top`. -/
theorem sum_lt_sum_top {s : ℕ} (m : Fin s) (J : Finset (Fin s))
    (hcard : J.card = (univ.filter fun i => m ≤ i).card) (hne : J ≠ univ.filter fun i => m ≤ i) :
    ∑ j ∈ J, (j : ℕ) < ∑ j ∈ univ.filter (fun i => m ≤ i), (j : ℕ) := by
  set T := univ.filter fun i : Fin s => m ≤ i
  have h1 := sum_sdiff (s₁ := J ∩ T) (s₂ := J) (f := fun j : Fin s => (j : ℕ)) inter_subset_left
  have h2 := sum_sdiff (s₁ := J ∩ T) (s₂ := T) (f := fun j : Fin s => (j : ℕ)) inter_subset_right
  have hc : (J \ (J ∩ T)).card = (T \ (J ∩ T)).card := by
    rw [card_sdiff_of_subset inter_subset_left, card_sdiff_of_subset inter_subset_right, hcard]
  have hpos : 0 < (J \ (J ∩ T)).card := by
    rw [card_pos]
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
    have hJT : J ⊆ T := fun x hx => (mem_inter.1 (h hx)).2
    exact hne (eq_of_subset_of_card_le hJT (by rw [hcard]))
  have hlo : ∑ j ∈ J \ (J ∩ T), (j : ℕ) ≤ (J \ (J ∩ T)).card * ((m : ℕ) - 1) := by
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun j hj => ?_
    simp only [mem_sdiff, mem_inter, T, mem_filter, mem_univ, true_and, not_and] at hj
    have := hj.2 hj.1
    rw [not_le] at this
    have : (j : ℕ) < m := this
    omega
  have hhi : (T \ (J ∩ T)).card * (m : ℕ) ≤ ∑ j ∈ T \ (J ∩ T), (j : ℕ) := by
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun j hj => ?_
    simp only [mem_sdiff, T, mem_filter, mem_univ, true_and] at hj
    exact hj.1
  have hm : 0 < (m : ℕ) := by
    by_contra h0
    push_neg at h0
    have : J \ (J ∩ T) = ∅ := by
      ext j
      simp only [mem_sdiff, mem_inter, T, mem_filter, mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro hj h
      exact h hj (by rw [Fin.le_def]; omega)
    rw [this] at hpos; simp at hpos
  rw [hc] at hlo
  simp only at h1 h2
  have : (T \ (J ∩ T)).card * ((m : ℕ) - 1) < (T \ (J ∩ T)).card * (m : ℕ) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by rw [← hc]; exact hpos)
  omega

/-- A strictly increasing `G : Fin s → ℕ` other than `0, 1, …, s−1` has an index `m` such that
lowering all entries from `m` on by one keeps it strictly increasing. -/
theorem exists_lower {s : ℕ} {G : Fin s → ℕ} (hG : StrictMono G) (hne : G ≠ stdF s) :
    ∃ m : Fin s, ((m : ℕ) = 0 ∧ 1 ≤ G m) ∨
      (∃ h : (m : ℕ) - 1 < s, 0 < (m : ℕ) ∧ G ⟨(m : ℕ) - 1, h⟩ + 1 < G m) := by
  by_contra hno
  push_neg at hno
  apply hne
  funext i
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero =>
    have := (hno ⟨0, hi⟩).1 rfl
    simp only [stdF]; omega
  | succ j ih =>
    have h1 := (hno ⟨j + 1, hi⟩).2 (by simpa using (by omega : j < s)) (by simp)
    have h2 := ih (by omega)
    have h3 : G ⟨j, by omega⟩ < G ⟨j + 1, hi⟩ := hG (Fin.mk_lt_mk.2 (by omega))
    simp only [stdF] at h2 ⊢
    simp only [add_tsub_cancel_right] at h1
    omega

/-- The subgroup generated by the standard minors of total index `N`. -/
def stdSpan (c : ℕ → R) (s N : ℕ) : AddSubgroup R :=
  AddSubgroup.closure {x | ∃ Rw : Fin s → ℕ, StrictMono Rw ∧
    ∑ i, Rw i + ∑ i, stdF s i = N ∧ x = hdet c Rw (stdF s)}

theorem hdet_mem_stdSpan_aux (c : ℕ → R) (s : ℕ) :
    ∀ μ : ℕ, ∀ G : Fin s → ℕ, (s * s + 1) * ∑ i, G i + ∑ i : Fin s, (i : ℕ) * G i = μ → StrictMono G →
      ∀ F : Fin s → ℕ, StrictMono F → hdet c F G ∈ stdSpan c s (∑ i, F i + ∑ i, G i) := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro G hμ hG F hF
  by_cases hstd : G = stdF s
  · subst hstd
    exact AddSubgroup.subset_closure ⟨F, hF, rfl, rfl⟩
  obtain ⟨m, hm⟩ := exists_lower hG hstd
  set T := univ.filter fun i : Fin s => m ≤ i with hT
  set k := T.card
  have hGpos : ∀ i, m ≤ i → 1 ≤ G i := by
    intro i hi
    rcases hm with ⟨h0, h1⟩ | ⟨h, hpos, hlt⟩
    · exact h1.trans (hG.monotone hi)
    · exact (by omega : 1 ≤ G m).trans (hG.monotone hi)
  set G' : Fin s → ℕ := fun i => G i - if m ≤ i then 1 else 0 with hG'
  have hbG : bump G' T = G := by
    funext i
    simp only [bump, hG', hT, mem_filter, mem_univ, true_and]
    split_ifs with h
    · have := hGpos i h; omega
    · simp
  have hG'strict : StrictMono G' := by
    intro i j hij
    have hgij := hG hij
    simp only [hG']
    by_cases hi : m ≤ i
    · have hj : m ≤ j := hi.trans hij.le
      simp only [if_pos hi, if_pos hj]
      have := hGpos i hi; omega
    · by_cases hj : m ≤ j
      · simp only [if_neg hi, if_pos hj, tsub_zero]
        push_neg at hi
        rcases hm with ⟨h0, h1⟩ | ⟨h, hpos, hlt⟩
        · exact absurd hi (by rw [Fin.lt_def]; omega)
        · have hle : i ≤ (⟨(m : ℕ) - 1, h⟩ : Fin s) := by
            rw [Fin.le_def]; simp; rw [Fin.lt_def] at hi; omega
          have h3 := hG.monotone hle
          have h4 := hG.monotone hj
          omega
      · simp only [if_neg hi, if_neg hj, tsub_zero]; exact hgij
  have hmT : m ∈ T := by simp [hT]
  have hk : 1 ≤ k := card_pos.2 ⟨m, hmT⟩
  have hsumG : ∑ i, G i = ∑ i, G' i + k := by rw [← sum_bump, hbG]
  have hwG : ∑ i : Fin s, (i : ℕ) * G i = ∑ i : Fin s, (i : ℕ) * G' i + ∑ j ∈ T, (j : ℕ) := by
    rw [← wsum_bump, hbG]
  -- the adjoint identity
  have hid := hdet_adjoint c F G' k
  have hTmem : T ∈ powersetCard k (univ : Finset (Fin s)) := by simp [k]
  rw [← Finset.add_sum_erase (powersetCard k univ) (fun J => hdet c F (bump G' J)) hTmem,
    hbG] at hid
  have hMG : hdet c F G = ∑ I ∈ powersetCard k univ, hdet c (bump F I) G' -
      ∑ J ∈ (powersetCard k univ).erase T, hdet c F (bump G' J) := by
    rw [hid]; abel
  rw [hMG]
  refine AddSubgroup.sub_mem _ (AddSubgroup.sum_mem _ fun I hI => ?_)
    (AddSubgroup.sum_mem _ fun J hJ => ?_)
  · -- the lowered column set: induction on `μ`
    have hIc : I.card = k := (mem_powersetCard.1 hI).2
    by_cases hinj : Function.Injective (bump F I)
    · have hstr := (bump_monotone hF I).strictMono_of_injective hinj
      have hlt : (s * s + 1) * ∑ i, G' i + ∑ i : Fin s, (i : ℕ) * G' i < μ := by
        rw [← hμ, hsumG, hwG, mul_add]
        have : k ≤ (s * s + 1) * k := Nat.le_mul_of_pos_left k (by omega)
        omega
      have := ih _ hlt G' rfl hG'strict (bump F I) hstr
      rwa [sum_bump, hIc, add_assoc, add_comm k, ← hsumG] at this
    · rw [hdet_eq_zero_of_not_inj_left c hinj]; exact AddSubgroup.zero_mem _
  · -- the other raised column sets: smaller weighted sum
    obtain ⟨hJT, hJ⟩ := mem_erase.1 hJ
    have hJc : J.card = k := (mem_powersetCard.1 hJ).2
    by_cases hinj : Function.Injective (bump G' J)
    · have hstr := (bump_monotone hG'strict J).strictMono_of_injective hinj
      have hsl := sum_lt_sum_top m J hJc hJT
      have hlt : (s * s + 1) * ∑ i, bump G' J i + ∑ i : Fin s, (i : ℕ) * bump G' J i < μ := by
        rw [← hμ, sum_bump, wsum_bump, hsumG, hwG, hJc]
        have : ∑ j ∈ J, (j : ℕ) < ∑ j ∈ T, (j : ℕ) := hsl
        omega
      have := ih _ hlt (bump G' J) rfl hstr F hF
      rwa [sum_bump, hJc, ← hsumG] at this
    · rw [hdet_eq_zero_of_not_inj_right c F hinj]; exact AddSubgroup.zero_mem _

/-- **Reduction to standard columns.** -/
theorem hdet_mem_stdSpan (c : ℕ → R) {s : ℕ} {F G : Fin s → ℕ} (hF : StrictMono F)
    (hG : StrictMono G) : hdet c F G ∈ stdSpan c s (∑ i, F i + ∑ i, G i) :=
  hdet_mem_stdSpan_aux c s _ G rfl hG F hF

/-- **Reduction to standard columns, truncated version**: if `c m = 0` for `m ≥ q`, any additive
subgroup containing the standard minors `M(R, {0..s−1})` with `R` strictly increasing, entries `< q`
and `∑ R + ∑_{i<s} i = ∑ F + ∑ G` contains `M(F, G)`. -/
theorem hdet_mem_of_std_trunc (c : ℕ → R) {q : ℕ} (hc : ∀ m, q ≤ m → c m = 0) {s : ℕ}
    {F G : Fin s → ℕ} (hF : StrictMono F) (hG : StrictMono G) (H : AddSubgroup R)
    (hH : ∀ Rw : Fin s → ℕ, StrictMono Rw → (∀ i, Rw i < q) →
      ∑ i, Rw i + ∑ i, stdF s i = ∑ i, F i + ∑ i, G i → hdet c Rw (stdF s) ∈ H) :
    hdet c F G ∈ H := by
  have h := hdet_mem_stdSpan c hF hG
  refine (AddSubgroup.closure_le H).2 ?_ h
  rintro x ⟨Rw, hR, hsum, rfl⟩
  by_cases hq : ∀ i, Rw i < q
  · exact hH Rw hR hq hsum
  · push_neg at hq
    obtain ⟨i, hi⟩ := hq
    have : hdet c Rw (stdF s) = 0 := by
      refine det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [of_apply]
      exact hc _ (by omega)
    rw [SetLike.mem_coe, this]; exact H.zero_mem

end PadicWin
