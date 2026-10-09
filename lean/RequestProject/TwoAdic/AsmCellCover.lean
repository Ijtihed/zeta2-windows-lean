import RequestProject.TwoAdic.AsmRelax
import RequestProject.TwoAdic.AsmArcsSound
import RequestProject.TwoAdic.AsmCover

/-!
# Exact counting of the class types in a certificate cell (II, Cor. 5.4)

For a certificate cell `c = [a, b]` with checked arcs `D` (`cellArcsOK c D`), an odd prime `ℓ` with
`u = ℓ/n ∈ [a, b]`, `n` even, `0 ≤ τ`, `δ ≤ 1` (**`cell_cover`**):

  `∑_{r < ℓ} ψ̃(α_r, τ) ≤ n ∑_t meas_t(u) ψ̃_t(τ) + 2 m K_b`,

where `α_r = classAlphas n ℓ δ r`, `m` is the number of arcs and `K_b = 2N(N+2)`,
`N = ⌊(3n+1)/ℓ⌋ + 1` bounds the number of nodes of a class.  This replaces the continuous circle
model by exact integer counting: residues in the interior of an arc have the class data of the arc
(`arc_data`), at most two residues per arc are near its left end, and the arcs of each type have total
length at most `meas_t(u)` (checked at both ends of the cell; everything is affine in `u`).
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin Arc Cert

variable {n ℓ : ℕ}

theorem knap_nil (τ : ℝ) : knap [] τ = 0 :=
  le_antisymm (by simpa [dualB] using knap_le_dual [] τ 0) (knap_nonneg _ _)

theorem alphasR_eq_of_runs {t t' : TypeD} (h : t.runs = t'.runs) (δ : ℝ) :
    alphasR t δ = alphasR t' δ := by
  unfold alphasR; rw [h]

/-- Comparison of affine functions inside `[a, b]` from the two ends. -/
theorem affV_le_affV {a b u : ℚ} {f g : Aff} (ha : affV f a ≤ affV g a) (hb : affV f b ≤ affV g b)
    (hau : a ≤ u) (hub : u ≤ b) : affV f u ≤ affV g u := by
  unfold affV at *
  rcases eq_or_lt_of_le (hau.trans hub) with hab | hab
  · have : u = a := le_antisymm (hab ▸ hub) hau
    subst this; exact ha
  · have key : ((g.1 - f.1) + (g.2 - f.2) * u) * (b - a) =
        ((g.1 - f.1) + (g.2 - f.2) * a) * (b - u) + ((g.1 - f.1) + (g.2 - f.2) * b) * (u - a) := by
      ring
    have h1 : 0 ≤ ((g.1 - f.1) + (g.2 - f.2) * u) * (b - a) := by
      rw [key]
      exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
    have h2 : 0 ≤ (g.1 - f.1) + (g.2 - f.2) * u := nonneg_of_mul_nonneg_left h1 (by linarith)
    linarith

/-- The position `f(u) n = f₀ n + f₁ ℓ` of an affine end. -/
def pos (n ℓ : ℕ) (f : Aff) : ℚ := f.1 * n + f.2 * ℓ

theorem pos_eq (hn : 0 < n) (f : Aff) : pos n ℓ f = n * affV f ((ℓ : ℚ) / n) := by
  unfold pos affV
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem pos_le_of (hs : Setting a b n ℓ) {f g : Aff} (ha : affV f a ≤ affV g a)
    (hb : affV f b ≤ affV g b) : pos n ℓ f ≤ pos n ℓ g := by
  rw [pos_eq hs.n_pos, pos_eq hs.n_pos]
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  exact mul_le_mul_of_nonneg_left (affV_le_affV ha hb hs.ha hs.hb) hn

/-- The value of an arc. -/
noncomputable def valIdx (c : CellD) (δ τ : ℝ) : Option ℕ → ℝ
  | none => 0
  | some t => knap (alphasR (c.types.getD t typ0) δ) τ

theorem valIdx_nonneg (c : CellD) (δ τ : ℝ) (o : Option ℕ) : 0 ≤ valIdx c δ τ o := by
  cases o <;> simp [valIdx, knap_nonneg]

/-- The arcs as positions and values. -/
noncomputable def arcList (c : CellD) (n ℓ : ℕ) (δ τ : ℝ) (arcs : List (Aff × Option ℕ)) :
    List (ℚ × ℝ) :=
  arcs.map fun p => (pos n ℓ p.1, valIdx c δ τ p.2)

theorem runs_beq_iff (l l' : List RunD) : (l == l') = true ↔ l = l' := beq_iff_eq

/-- The checked arcs form a valid chain for `F r = ψ̃(α_r, τ)`. -/
theorem chainV_of (hn : Even n) (hℓ : Odd ℓ) {c : CellD} (hs : Setting c.a c.b n ℓ) (ha0 : 0 < c.a)
    {J : ℕ} (hJ : 3 / 2 < (J : ℚ) * c.a) (δ τ : ℝ) :
    ∀ (arcs : List (Aff × Option ℕ)) (lo : Aff), chainOK c.a c.b lo arcs = true →
      arcsAllOK c J lo arcs = true →
      ChainV ℓ (fun r => knap (classAlphas n ℓ δ r) τ) (pos n ℓ lo) (arcList c n ℓ δ τ arcs)
  | [], lo, h1, _ => by
    simp only [chainOK, decide_eq_true_eq] at h1
    subst h1
    simp [ChainV, arcList, pos]
  | (hi, idx) :: rest, lo, h1, h2 => by
    simp only [chainOK, arcsAllOK, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    have ih := chainV_of hn hℓ hs ha0 hJ δ τ rest hi h1.2 h2.2
    simp only [arcList, List.map_cons] at ih ⊢
    refine ⟨pos_le_of hs h1.1.1 h1.1.2, valIdx_nonneg c δ τ idx, fun r hr h3 h4 => ?_, ih⟩
    have hg : Good n ℓ lo hi r := ⟨by simpa [pos] using h3, by simpa [pos] using h4⟩
    have hOK := h2.1
    unfold arcOK at hOK
    simp only [Bool.and_eq_true] at hOK
    obtain ⟨hN, hH, hZ⟩ := arc_data hn hℓ hs ha0 hJ hOK.1 hr hg
    have hcl : classAlphas n ℓ δ r = alphasR ⟨0, 0, runsOf (arcN c.a c.b lo hi J)
        (arcH c.a c.b lo hi J) (arcZ c.a c.b lo hi J)⟩ δ := by
      unfold classAlphas nhs; rw [hN, hH, hZ]
    cases idx with
    | none =>
      have h0 := (runs_beq_iff _ _).1 hOK.2
      simp only at h0 ⊢
      rw [hcl, h0]
      simp [valIdx, alphasR, knap_nil]
    | some t =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hOK
      have h0 := (runs_beq_iff _ _).1 hOK.2.2
      simp only [valIdx]
      rw [hcl, alphasR_eq_of_runs (t' := ⟨0, 0, runsOf (arcN c.a c.b lo hi J)
        (arcH c.a c.b lo hi J) (arcZ c.a c.b lo hi J)⟩) h0]

/-- The type indices of the arcs are valid. -/
def idxOK (c : CellD) : Option ℕ → Prop
  | none => True
  | some t => t < c.types.length

theorem pos_measSum_step (t : ℕ) (lo hi : Aff) (idx : Option ℕ) (m : Aff) :
    pos n ℓ (if idx = some t then (m.1 + (hi.1 - lo.1), m.2 + (hi.2 - lo.2)) else m) =
      pos n ℓ m + if idx = some t then pos n ℓ hi - pos n ℓ lo else 0 := by
  split_ifs
  · simp [pos]; ring
  · simp

/-- `arcSum` is `∑_t ψ̃_t · (total length of the arcs of type t)`. -/
theorem arcSum_eq (c : CellD) (J : ℕ) (δ τ : ℝ) :
    ∀ (arcs : List (Aff × Option ℕ)) (lo : Aff), arcsAllOK c J lo arcs = true →
      arcSum (pos n ℓ lo) (arcList c n ℓ δ τ arcs) =
        ∑ t ∈ range c.types.length, valIdx c δ τ (some t) * ((pos n ℓ (measSum t lo arcs) : ℚ) : ℝ)
  | [], lo, _ => by simp [arcSum, arcList, measSum, pos]
  | (hi, idx) :: rest, lo, h2 => by
    simp only [arcsAllOK, Bool.and_eq_true] at h2
    have ih := arcSum_eq c J δ τ rest hi h2.2
    simp only [arcList, List.map_cons, arcSum] at ih ⊢
    rw [ih]
    simp only [measSum]
    simp_rw [pos_measSum_step]
    push_cast
    simp_rw [mul_add, sum_add_distrib]
    have hOK := h2.1
    unfold arcOK at hOK
    simp only [Bool.and_eq_true] at hOK
    cases idx with
    | none => simp [valIdx]
    | some t0 =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hOK
      have ht0 : t0 ∈ range c.types.length := mem_range.2 hOK.2.1
      have : ∑ x ∈ range c.types.length, valIdx c δ τ (some x) *
          (((if some t0 = some x then pos n ℓ hi - pos n ℓ lo else 0 : ℚ)) : ℝ) =
          valIdx c δ τ (some t0) * (((pos n ℓ hi : ℚ) : ℝ) - ((pos n ℓ lo : ℚ) : ℝ)) := by
        rw [sum_eq_single_of_mem t0 ht0 (fun b _ hb => by
          rw [if_neg (fun h => hb (Option.some_inj.1 h).symm)]; simp)]
        rw [if_pos rfl]; push_cast; ring
      rw [this]
      ring

theorem sum_range_getD (L : List TypeD) (f : TypeD → ℝ) :
    ∑ t ∈ range L.length, f (L.getD t typ0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, add_comm]

/-- The weights of a class are bounded: `ψ̃(α_r, τ) ≤ 2N(N + 2)`, `N = N_r`. -/
theorem knap_classAlphas_le {r : ℕ} {δ τ : ℝ} (hδ : δ ≤ 1) (hτ : 0 ≤ τ) :
    knap (classAlphas n ℓ δ r) τ ≤
      2 * ((cls n ℓ r).card : ℝ) * ((cls n ℓ r).card + 2) := by
  refine (knap_le_sum_pos _ τ).trans ?_
  unfold classAlphas
  rw [alphasR_runsOf]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  set N := (cls n ℓ r).card
  set z := zc n ℓ r
  have hnh : nhs n ℓ r ≤ N := card_filter_le _ _
  have hmk : (if (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z then N - nhs n ℓ r else 0) ≤ N := by
    split_ifs <;> omega
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have ha : max 0 ((((N : ℤ) - z : ℤ) : ℝ) + (1 + δ) - τ) ≤ N + 2 := by
    push_cast; exact max_le (by positivity) (by linarith)
  have hb : max 0 ((((N : ℤ) - z : ℤ) : ℝ) - τ) ≤ N := by
    push_cast; exact max_le (by positivity) (by linarith)
  have hnh' : (nhs n ℓ r : ℝ) ≤ N := by exact_mod_cast hnh
  have hmk' : ((if (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z then N - nhs n ℓ r else 0 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast hmk
  have h0a : 0 ≤ max 0 ((((N : ℤ) - z : ℤ) : ℝ) + (1 + δ) - τ) := le_max_left _ _
  have h0b : 0 ≤ max 0 ((((N : ℤ) - z : ℤ) : ℝ) - τ) := le_max_left _ _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (nhs n ℓ r : ℝ) * max 0 ((((N : ℤ) - z : ℤ) : ℝ) + (1 + δ) - τ) +
        ((if (2 ≤ N ∨ 1 ≤ z) ∧ 1 ≤ (N : ℤ) - z then N - nhs n ℓ r else 0 : ℕ) : ℝ) *
          max 0 ((((N : ℤ) - z : ℤ) : ℝ) - τ)
      ≤ N * (N + 2) + N * N := by
        gcongr
    _ ≤ 2 * N * (N + 2) := by nlinarith

/-- **Exact counting in a certificate cell.** -/
theorem cell_cover (hn : Even n) (hℓ : Odd ℓ) {c : CellD} {D : ArcsD} (hok : cellArcsOK c D = true)
    (hs : Setting c.a c.b n ℓ) {δ τ : ℝ} (hδ : δ ≤ 1) (hτ : 0 ≤ τ) :
    ∑ r ∈ range ℓ, knap (classAlphas n ℓ δ r) τ ≤
      n * (c.types.map fun t => measR t ((ℓ : ℝ) / n) * knap (alphasR t δ) τ).sum +
        2 * D.arcs.length * (2 * (((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) *
          ((((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) + 2)) := by
  unfold cellArcsOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨ha0, hab⟩, hJ⟩, hchain⟩, hall⟩, hmeas⟩ := hok
  have hℓ0 : 0 < ℓ := hℓ.pos
  set Nb : ℕ := (3 * n + 1) / ℓ + 1
  set Kb : ℝ := 2 * (Nb : ℝ) * ((Nb : ℝ) + 2)
  have hKb : 0 ≤ Kb := by positivity
  have hFK : ∀ r < ℓ, knap (classAlphas n ℓ δ r) τ ≤ Kb := by
    intro r hr
    refine (knap_classAlphas_le hδ hτ).trans ?_
    have h1 := (card_cls_bounds n ℓ r hℓ0 hr).2
    have e : 2 * R n + 1 = 3 * n + 1 := by have := R_of_even hn; omega
    have h1a : (cls n ℓ r).card ≤ (3 * n + 1) / ℓ + 1 := by rw [← e]; exact h1
    have h1' : ((cls n ℓ r).card : ℝ) ≤ Nb := by exact_mod_cast h1a
    have h0 : (0 : ℝ) ≤ (cls n ℓ r).card := Nat.cast_nonneg _
    simp only [Kb]
    nlinarith
  have hcov := cover_sum ℓ (fun r => knap (classAlphas n ℓ δ r) τ) Kb (fun r => knap_nonneg _ _)
    hFK hKb (arcList c n ℓ δ τ D.arcs) (pos n ℓ (0, 0))
    (chainV_of hn hℓ hs ha0 hJ δ τ D.arcs (0, 0) hchain hall)
  have hfilter : (range ℓ).filter (fun r : ℕ => pos n ℓ (0, 0) - 1 < r) = range ℓ := by
    refine filter_true_of_mem fun r _ => ?_
    simp only [pos]
    have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
    linarith
  rw [hfilter, arcSum_eq c D.J δ τ D.arcs (0, 0) hall] at hcov
  have hlen : (arcList c n ℓ δ τ D.arcs).length = D.arcs.length := by simp [arcList]
  rw [hlen] at hcov
  refine hcov.trans (add_le_add_left ?_ _)
  -- the measures
  rw [← sum_range_getD, mul_sum]
  refine sum_le_sum fun t ht => ?_
  have hm := hmeas
  unfold measOK at hm
  rw [List.all_eq_true] at hm
  have := hm t (List.mem_range.2 (mem_range.1 ht))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := this
  have hle : pos n ℓ (measSum t (0, 0) D.arcs) ≤ n * measQ (c.types.getD t typ0) ((ℓ : ℚ) / n) := by
    rw [pos_eq hs.n_pos]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    have := affV_le_affV (g := ((c.types.getD t typ0).m0, (c.types.getD t typ0).m1)) h1 h2 hs.ha hs.hb
    exact this
  have hle' : ((pos n ℓ (measSum t (0, 0) D.arcs) : ℚ) : ℝ) ≤
      n * measR (c.types.getD t typ0) ((ℓ : ℝ) / n) := by
    have := (Rat.cast_le (K := ℝ)).2 hle
    refine this.trans (le_of_eq ?_)
    simp only [measQ, measR]
    push_cast
    ring
  simp only [valIdx]
  have h0 := knap_nonneg (alphasR (c.types.getD t typ0) δ) τ
  calc knap (alphasR (c.types.getD t typ0) δ) τ * ((pos n ℓ (measSum t (0, 0) D.arcs) : ℚ) : ℝ)
      ≤ knap (alphasR (c.types.getD t typ0) δ) τ * (n * measR (c.types.getD t typ0) ((ℓ : ℝ) / n)) :=
        mul_le_mul_of_nonneg_left hle' h0
    _ = n * (measR (c.types.getD t typ0) ((ℓ : ℝ) / n) * knap (alphasR (c.types.getD t typ0) δ) τ) := by
        ring

end TwoAdicWin.Asm
