import RequestProject.Zeta7.Hankel2.CertCircle

/-!
# The Appendix B certificate checker and the construction of `StepMajorant`

A certificate for `κ ∈ [κ₁, κ₂]` is a list of subcells `(b_i, λ_i, h_i)` (`b_0 = 1/20` is
implicit, `a_i = b_{i−1}`), with `λ_i ∈ ℤ` and `h_i ∈ ℚ`, together with a table of tangent points.

* `chainOK`: the computable check (`0 < a_i < b_i`, `h_i ≥ 0`, and at both ends `u` of every
  subcell `max(λκ₁, λκ₂) + gpotQ u λ ≤ h`);
* `refinesOK`: every `c/m`, `2c/(2m−1)` (`c ≤ 3`, `m ≤ 60`) in `(1/20, 9/2)` is a partition point
  (larger `m` give points `< 1/20`);
* **`mkStepMajorant`**: from `chainOK`, `refinesOK` and `lastB = 9/2`, a `StepMajorant κ₁ κ₂`;
* `stepSum`, `mkStepMajorant_sum`: `∑ h_i (a_i − a_{i−1})` as a computable rational.
-/

open Finset

namespace Hankel2.CertC

open Hankel2.Fam3 Hankel2.Circle

/-- A subcell record `(b, λ, h, tab)`; `tab` is a (small) table of tangent points for the types
occurring on the subcell (any table is sound). -/
abbrev SubRec := ℚ × ℤ × ℚ × List (ℕ × ℕ)

/-- Check of one subcell `[a, b]`. -/
def subOK (κ₁ κ₂ a : ℚ) (r : SubRec) : Bool :=
  decide (0 < a) && decide (a < r.1) && decide (0 ≤ r.2.2.1) &&
    decide (gpotQ r.2.2.2 a r.2.1 + max (r.2.1 * κ₁) (r.2.1 * κ₂) ≤ r.2.2.1) &&
    decide (gpotQ r.2.2.2 r.1 r.2.1 + max (r.2.1 * κ₁) (r.2.1 * κ₂) ≤ r.2.2.1)

/-- Check of a chain of subcells starting at `a`. -/
def chainOK (κ₁ κ₂ : ℚ) : ℚ → List SubRec → Bool
  | _, [] => true
  | a, r :: rs => subOK κ₁ κ₂ a r && chainOK κ₁ κ₂ r.1 rs

/-- The right end of a chain. -/
def lastB : ℚ → List SubRec → ℚ
  | a, [] => a
  | _, r :: rs => lastB r.1 rs

theorem chainOK_append (κ₁ κ₂ a : ℚ) (l₁ l₂ : List SubRec) :
    chainOK κ₁ κ₂ a (l₁ ++ l₂) = (chainOK κ₁ κ₂ a l₁ && chainOK κ₁ κ₂ (lastB a l₁) l₂) := by
  induction l₁ generalizing a with
  | nil => simp [chainOK, lastB]
  | cons r rs ih => simp [chainOK, lastB, ih, Bool.and_assoc]

theorem lastB_append (a : ℚ) (l₁ l₂ : List SubRec) : lastB a (l₁ ++ l₂) = lastB (lastB a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons r rs ih => exact ih _

/-- The partition points `a_0 = a, a_1 = b_0, …`. -/
def ptsL (a : ℚ) (l : List SubRec) : List ℚ := a :: l.map Prod.fst

theorem chainOK_get (κ₁ κ₂ : ℚ) :
    ∀ (l : List SubRec) (a : ℚ), chainOK κ₁ κ₂ a l = true →
      ∀ i < l.length, subOK κ₁ κ₂ ((ptsL a l).getD i 0) (l.getD i default) = true ∧
        (ptsL a l).getD (i + 1) 0 = (l.getD i default).1 := by
  intro l
  induction l with
  | nil => intro a _ i hi; simp at hi
  | cons r rs ih =>
    intro a h i hi
    simp only [chainOK, Bool.and_eq_true] at h
    rcases i with _ | i
    · simp [ptsL, h.1]
    · have := ih r.1 h.2 i (by simp at hi; omega)
      simpa [ptsL] using this

theorem lastB_eq (a : ℚ) (l : List SubRec) : lastB a l = (ptsL a l).getD l.length 0 := by
  induction l generalizing a with
  | nil => rfl
  | cons r rs ih => simp [lastB, ih, ptsL]

/-- The list of candidate points of `𝓑`: `c/m` and `2c/(2m−1)`, `c ∈ {1,2,3}`, `1 ≤ m ≤ 60`. -/
def bCands : List ℚ :=
  (List.range 3).flatMap fun c => (List.range 60).flatMap fun m =>
    [((c + 1 : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ), 2 * ((c + 1 : ℕ) : ℚ) / (2 * ((m + 1 : ℕ) : ℚ) - 1)]

/-- Every candidate in `(1/20, 9/2)` is a partition point. -/
def refinesOK (pts : List ℚ) : Bool :=
  bCands.all fun q => decide (q ≤ 1 / 20) || decide (9 / 2 ≤ q) || pts.contains q

theorem mem_bCands {c m : ℕ} (hc : c ∈ ({1, 2, 3} : Finset ℕ)) (hm1 : 1 ≤ m) (hm : m ≤ 60) :
    (c : ℚ) / m ∈ bCands ∧ 2 * (c : ℚ) / (2 * (m : ℚ) - 1) ∈ bCands := by
  simp only [bCands, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨⟨c - 1, by omega, m', by omega, Or.inl ?_⟩, ⟨c - 1, by omega, m', by omega, Or.inr ?_⟩⟩ <;>
    rw [show c - 1 + 1 = c by omega]

/-- **`refines` from the computable check.** -/
theorem refines_of_OK {pts : List ℚ} (h : refinesOK pts = true) :
    ∀ b ∈ Bset, (1 / 20 : ℝ) < b → b < 9 / 2 → ∃ q ∈ pts, (q : ℝ) = b := by
  intro b hb h1 h2
  obtain ⟨c, hc, m, hm1, hbm⟩ := hb
  have hc3 : (c : ℝ) ≤ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> norm_num
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm60 : m ≤ 60 := by
    by_contra hcon
    have hm61 : (61 : ℝ) ≤ m := by exact_mod_cast (show 61 ≤ m by omega)
    rcases hbm with rfl | rfl
    · have : (c : ℝ) / m ≤ 3 / 61 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
      linarith
    · have : 2 * (c : ℝ) / (2 * m - 1) ≤ 6 / 121 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
      linarith
  have hall := List.all_eq_true.1 h
  obtain ⟨hq1, hq2⟩ := mem_bCands hc hm1 hm60
  rcases hbm with rfl | rfl
  · have := hall _ hq1
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
    have hcast : (((c : ℚ) / m : ℚ) : ℝ) = (c : ℝ) / m := by push_cast; rfl
    rcases this with (h3 | h3) | h3
    · exfalso; have := (Rat.cast_le (K := ℝ)).2 h3; rw [hcast] at this; push_cast at this; linarith
    · exfalso; have := (Rat.cast_le (K := ℝ)).2 h3; rw [hcast] at this; push_cast at this; linarith
    · exact ⟨_, h3, hcast⟩
  · have := hall _ hq2
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
    have hcast : ((2 * (c : ℚ) / (2 * (m : ℚ) - 1) : ℚ) : ℝ) = 2 * (c : ℝ) / (2 * (m : ℝ) - 1) := by
      push_cast; rfl
    rcases this with (h3 | h3) | h3
    · exfalso; have := (Rat.cast_le (K := ℝ)).2 h3; rw [hcast] at this; push_cast at this; linarith
    · exfalso; have := (Rat.cast_le (K := ℝ)).2 h3; rw [hcast] at this; push_cast at this; linarith
    · exact ⟨_, h3, hcast⟩

/-- **The step majorant of a checked certificate.** -/
def mkStepMajorant (κ₁ κ₂ : ℚ) (K₁ K₂ : ℝ) (hK₁ : K₁ = κ₁) (hK₂ : K₂ = κ₂)
    (l : List SubRec) (hchain : chainOK κ₁ κ₂ (1 / 20) l = true)
    (hlast : lastB (1 / 20) l = 9 / 2) (href : refinesOK (ptsL (1 / 20) l) = true) :
    StepMajorant K₁ K₂ where
  M := l.length
  a j := (ptsL (1 / 20) l).getD j 0
  a_strictMono := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    obtain ⟨h1, h2⟩ := chainOK_get κ₁ κ₂ l _ hchain i i.isLt
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [h2]
    simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1.1.2
  a_zero := rfl
  a_last := by
    simp only [Fin.val_last]
    rw [← lastB_eq, hlast]
  refines := by
    intro b hb h1 h2
    obtain ⟨q, hq, hqb⟩ := refines_of_OK href b hb h1 h2
    obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem hq
    refine ⟨⟨j, by simpa [ptsL] using hj⟩, ?_⟩
    simp only
    rw [List.getD_eq_getElem _ _ hj, hjq, hqb]
  lam i := ((l.getD i default).2.1 : ℚ)
  h i := (l.getD i default).2.2.1
  dom := by
    intro i u hu κ hκ
    obtain ⟨h1, h2⟩ := chainOK_get κ₁ κ₂ l _ hchain i i.isLt
    set r := l.getD i default
    simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨⟨ha0, hab⟩, _⟩, hA⟩, hB⟩ := h1
    have hlam : ((r.2.1 : ℚ) : ℝ) = (r.2.1 : ℝ) := by push_cast; rfl
    rw [hlam]
    have hmax : ∀ κ' : ℚ, (κ' = κ₁ ∨ κ' = κ₂) → (r.2.1 : ℝ) * κ' ≤
        ((max (r.2.1 * κ₁) (r.2.1 * κ₂) : ℚ) : ℝ) := by
      intro κ' hκ'
      have : (r.2.1 : ℚ) * κ' ≤ max (r.2.1 * κ₁) (r.2.1 * κ₂) := by
        rcases hκ' with rfl | rfl
        · exact le_max_left _ _
        · exact le_max_right _ _
      have := (Rat.cast_le (K := ℝ)).2 this
      push_cast at this ⊢; exact this
    have hκ' : ∃ κ' : ℚ, (κ' = κ₁ ∨ κ' = κ₂) ∧ κ = κ' := by
      rcases hκ with rfl | rfl
      · exact ⟨κ₁, Or.inl rfl, hK₁⟩
      · exact ⟨κ₂, Or.inr rfl, hK₂⟩
    obtain ⟨κ', hκ'1, rfl⟩ := hκ'
    have hm := hmax κ' hκ'1
    rcases hu with rfl | rfl
    · simp only [Fin.val_castSucc]
      have hg := gfun_le_gpotQ r.2.2.2 ha0 r.2.1 (κ' : ℝ)
      have := (Rat.cast_le (K := ℝ)).2 hA
      push_cast at this
      push_cast at hm
      linarith
    · simp only [Fin.val_succ]
      rw [h2]
      have hg := gfun_le_gpotQ r.2.2.2 (ha0.trans hab) r.2.1 (κ' : ℝ)
      have := (Rat.cast_le (K := ℝ)).2 hB
      push_cast at this
      push_cast at hm
      linarith
  h_nonneg := by
    intro i
    obtain ⟨h1, -⟩ := chainOK_get κ₁ κ₂ l _ hchain i i.isLt
    simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1.2

/-- `∑ h_i (b_i − a_i)` along a chain. -/
def stepSum : ℚ → List SubRec → ℚ
  | _, [] => 0
  | a, r :: rs => r.2.2.1 * (r.1 - a) + stepSum r.1 rs

theorem stepSum_append (a : ℚ) (l₁ l₂ : List SubRec) :
    stepSum a (l₁ ++ l₂) = stepSum a l₁ + stepSum (lastB a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [stepSum, lastB]
  | cons r rs ih => simp [stepSum, lastB, ih]; ring

theorem stepSum_eq (a : ℚ) (l : List SubRec) :
    stepSum a l = ∑ i ∈ Finset.range l.length,
      (l.getD i default).2.2.1 * ((ptsL a l).getD (i + 1) 0 - (ptsL a l).getD i 0) := by
  induction l generalizing a with
  | nil => simp [stepSum]
  | cons r rs ih =>
    have e : ptsL a (r :: rs) = a :: ptsL r.1 rs := rfl
    rw [List.length_cons, Finset.sum_range_succ', stepSum, ih, e]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have e0 : (ptsL r.1 rs).getD 0 0 = r.1 := rfl
    rw [e0]; ring

theorem mkStepMajorant_sum (κ₁ κ₂ : ℚ) (K₁ K₂ : ℝ) (hK₁ : K₁ = κ₁)
    (hK₂ : K₂ = κ₂) (l : List SubRec) (hchain : chainOK κ₁ κ₂ (1 / 20) l = true)
    (hlast : lastB (1 / 20) l = 9 / 2) (href : refinesOK (ptsL (1 / 20) l) = true) :
    let C := mkStepMajorant κ₁ κ₂ K₁ K₂ hK₁ hK₂ l hchain hlast href
    ∑ i : Fin C.M, (C.h i : ℝ) * ((C.a i.succ : ℝ) - C.a i.castSucc) = (stepSum (1 / 20) l : ℝ) := by
  intro C
  rw [stepSum_eq, Rat.cast_sum]
  simp only [C, mkStepMajorant, Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((l.getD i default).2.2.1 : ℝ) *
    (((ptsL (1 / 20) l).getD (i + 1) 0 : ℚ) - ((ptsL (1 / 20) l).getD i 0 : ℚ) : ℝ)) l.length]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

/-- A checked block of subcells from `a` to `c`, with step sum at most `S`. -/
def Blk (κ₁ κ₂ a : ℚ) (l : List SubRec) (c S : ℚ) : Prop :=
  chainOK κ₁ κ₂ a l = true ∧ lastB a l = c ∧ stepSum a l ≤ S

theorem blk_app {κ₁ κ₂ a b c S₁ S₂ : ℚ} {l r : List SubRec} (hl : Blk κ₁ κ₂ a l b S₁)
    (hr : Blk κ₁ κ₂ b r c S₂) : Blk κ₁ κ₂ a (l ++ r) c (S₁ + S₂) := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h4, h5, h6⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [chainOK_append, h1, h2, h4]; rfl
  · rw [lastB_append, h2, h5]
  · rw [stepSum_append, h2]; linarith

theorem blk_mono {κ₁ κ₂ a c S S' : ℚ} {l : List SubRec} (h : Blk κ₁ κ₂ a l c S) (hS : S ≤ S') :
    Blk κ₁ κ₂ a l c S' :=
  ⟨h.1, h.2.1, h.2.2.trans hS⟩

end Hankel2.CertC
