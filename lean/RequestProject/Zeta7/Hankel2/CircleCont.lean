import RequestProject.Zeta7.Hankel2.CircleModel

/-!
# The circle model (paper §8.4): finiteness of the types and continuity in `u`

* `ctype_mem_box`: for `u ≥ a > 0` every type lies in a fixed finite box (a class has at most
  `3/a + 1` nodes and at most `1/a + 1` zeros);
* `Gpot_eq_sum`: hence `∑_t meas_t(u) ψ(t)` is a finite sum over that box;
* `meas_lipschitz`: `|meas_t(u) − meas_t(u')| ≤ C(a, U) |u − u'|` on `[a, U]` (the continuity
  across the points of `𝓑`);
* `Gpot_affine_on_cell`, `Gpot_lipschitz` and **`Gpot_le_max`**: on a closed interval `[a, b]`
  (`a > 0`) whose interior contains no point of `𝓑`, `Gpot ψ` is affine, hence bounded by
  `max(Gpot ψ a, Gpot ψ b)`.  This is how a step majorant checked at the endpoints of the subcells
  bounds `g(λ, ·)` on the whole subcell.
-/

open MeasureTheory Set

namespace Hankel2.Circle

/-! ### Counting integers in an interval -/

theorem ncard_le_of_bounds {S : Set ℤ} {u α L : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (h : ∀ m ∈ S, α ≤ m * u ∧ m * u ≤ α + L) : (S.ncard : ℝ) ≤ L / u + 1 := by
  have hsub : S ⊆ ↑(Finset.Icc ⌈α / u⌉ ⌊(α + L) / u⌋) := by
    intro m hm
    obtain ⟨h1, h2⟩ := h m hm
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · exact Int.ceil_le.2 (by rw [div_le_iff₀ hu]; linarith)
    · exact Int.le_floor.2 (by rw [le_div_iff₀ hu]; linarith)
  have h1 : S.ncard ≤ (Finset.Icc ⌈α / u⌉ ⌊(α + L) / u⌋).card := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Int.card_Icc] at h1
  have h2 : ((⌊(α + L) / u⌋ + 1 - ⌈α / u⌉).toNat : ℝ) ≤ L / u + 1 := by
    rcases le_or_gt 0 (⌊(α + L) / u⌋ + 1 - ⌈α / u⌉) with hc | hc
    · have : (((⌊(α + L) / u⌋ + 1 - ⌈α / u⌉).toNat : ℤ) : ℝ) =
          ((⌊(α + L) / u⌋ + 1 - ⌈α / u⌉ : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg hc]
      rw [show (((⌊(α + L) / u⌋ + 1 - ⌈α / u⌉).toNat : ℕ) : ℝ) =
        (((⌊(α + L) / u⌋ + 1 - ⌈α / u⌉).toNat : ℤ) : ℝ) from rfl, this]
      push_cast
      have := Int.floor_le ((α + L) / u)
      have := Int.le_ceil (α / u)
      have : (α + L) / u - α / u = L / u := by ring
      linarith
    · rw [Int.toNat_of_nonpos hc.le]; simp only [Nat.cast_zero]; positivity
  exact le_trans (by exact_mod_cast h1) h2

/-! ### The box of types -/

/-- The size of the box of types for `u ≥ a`. -/
noncomputable def boxN (a : ℝ) : ℕ := ⌊3 / a⌋₊ + 2

/-- A finite box containing every type occurring for `u ≥ a`. -/
noncomputable def typeBox (a : ℝ) : Finset CType :=
  Finset.range (boxN a) ×ˢ Finset.range (boxN a) ×ˢ Finset.range (boxN a)

theorem ncard_nodeSet_le {u : ℝ} (hu : 0 < u) (x : ℝ) : ((nodeSet u x).ncard : ℝ) ≤ 3 / u + 1 :=
  ncard_le_of_bounds (α := -1 - x) hu (by norm_num) fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩

theorem ncard_zSet_le {u : ℝ} (hu : 0 < u) (x : ℝ) : ((zSet u x).ncard : ℝ) ≤ 1 / u + 1 :=
  ncard_le_of_bounds (α := u / 2 - x) hu (by norm_num)
    fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩

theorem ncard_hsSet_le {u : ℝ} (hu : 0 < u) (x : ℝ) : ((hsSet u x).ncard : ℝ) ≤ 3 / u + 1 :=
  ncard_le_of_bounds (α := -1 - x) hu (by norm_num)
    fun m hm => ⟨by linarith [hm.1.1], by linarith [hm.1.2]⟩

theorem lt_boxN {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) {k : ℕ} (hk : (k : ℝ) ≤ 3 / u + 1) :
    k < boxN a := by
  have h1 : 3 / u ≤ 3 / a := div_le_div_of_nonneg_left (by norm_num) ha hau
  have h2 : 3 / a < (⌊3 / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have : (k : ℝ) < (boxN a : ℝ) := by unfold boxN; push_cast; linarith
  exact_mod_cast this

theorem ctype_mem_box {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) (x : ℝ) : ctype u x ∈ typeBox a := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  simp only [typeBox, ctype, Finset.mem_product, Finset.mem_range]
  refine ⟨lt_boxN ha hau (ncard_nodeSet_le hu x), lt_boxN ha hau ?_, lt_boxN ha hau (ncard_hsSet_le hu x)⟩
  have := ncard_zSet_le hu x
  have : 1 / u ≤ 3 / u := div_le_div_of_nonneg_right (by norm_num) hu.le
  linarith

theorem meas_eq_zero_of_not_mem {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) {t : CType}
    (ht : t ∉ typeBox a) : meas u t = 0 := by
  unfold meas
  have : {x ∈ Ico 0 u | ctype u x = t} = ∅ := by
    ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro _ h; exact ht (h ▸ ctype_mem_box ha hau x)
  rw [this]; simp

theorem meas_nonneg (u : ℝ) (t : CType) : 0 ≤ meas u t := ENNReal.toReal_nonneg

/-- `Gpot ψ u` is the finite sum over the box of types. -/
theorem Gpot_eq_sum (ψ : CType → ℝ) {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    Gpot ψ u = ∑ t ∈ typeBox a, meas u t * ψ t := by
  unfold Gpot
  apply finsum_eq_sum_of_support_subset
  intro t ht
  by_contra h
  exact ht (by simp [meas_eq_zero_of_not_mem ha hau h])

/-! ### Lipschitz continuity of `meas_t` -/

/-- The range of the relevant shifts `m`. -/
noncomputable def shiftM (a U : ℝ) : ℕ := ⌈(U + 3) / a⌉₊ + 1

/-- The positions whose type may differ at `u` and `u'`. -/
def switchSet (M : ℕ) (u u' : ℝ) : Set ℝ :=
  ⋃ i : Fin 4, ⋃ m ∈ Finset.Icc (-(M : ℤ)) M,
    Icc (min (bpt u i + m * u) (bpt u' i + m * u')) (max (bpt u i + m * u) (bpt u' i + m * u'))

theorem iff_of_not_mem_minmax {e e' x : ℝ} (h : x ∉ Icc (min e e') (max e e')) :
    (e ≤ x ↔ e' ≤ x) ∧ (x ≤ e ↔ x ≤ e') ∧ (x < e ↔ x < e') := by
  have : x < min e e' ∨ max e e' < x := by
    by_contra hc; push_neg at hc; exact h ⟨hc.1, hc.2⟩
  rcases this with h | h
  · have h1 := min_le_left e e'; have h2 := min_le_right e e'
    exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩,
      ⟨fun _ => by linarith, fun _ => by linarith⟩⟩
  · have h1 := le_max_left e e'; have h2 := le_max_right e e'
    exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩,
      ⟨fun _ => by linarith, fun _ => by linarith⟩⟩

theorem le_shiftM (a U : ℝ) : (U + 3) / a ≤ (shiftM a U : ℝ) - 1 := by
  unfold shiftM; push_cast
  have := Nat.le_ceil ((U + 3) / a); linarith

theorem nodeSet_bound {a U v x : ℝ} (ha : 0 < a) (hav : a ≤ v) (hx0 : 0 ≤ x) (hxU : x ≤ U)
    {m : ℤ} (hm : m ∈ nodeSet v x) : |(m : ℝ)| ≤ (U + 3) / a := by
  obtain ⟨h1, h2⟩ := hm
  rw [abs_le, ← neg_div, div_le_iff₀ ha, le_div_iff₀ ha]
  rcases le_or_gt 0 (m : ℝ) with hm0 | hm0
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem zSet_bound {a U v x : ℝ} (ha : 0 < a) (hav : a ≤ v) (hx0 : 0 ≤ x) (hxU : x ≤ U)
    {m : ℤ} (hm : m ∈ zSet v x) : |(m : ℝ)| ≤ (U + 3) / a := by
  obtain ⟨h1, h2⟩ := hm
  have hv : 0 < v := lt_of_lt_of_le ha hav
  rw [abs_le, ← neg_div, div_le_iff₀ ha, le_div_iff₀ ha]
  rcases le_or_gt m 0 with hm0 | hm0
  · have hm0' : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
    constructor <;> nlinarith
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hv2 : v ≤ 2 := by nlinarith
    constructor <;> nlinarith

theorem mem_shift_of_bound {a U : ℝ} {m : ℤ} (h : |(m : ℝ)| ≤ (U + 3) / a) :
    -m ∈ Finset.Icc (-(shiftM a U : ℤ)) (shiftM a U) ∧
      -m - 1 ∈ Finset.Icc (-(shiftM a U : ℤ)) (shiftM a U) := by
  have hM := le_shiftM a U
  rw [abs_le] at h
  have h1 : (m : ℝ) ≤ (shiftM a U : ℝ) - 1 := by linarith
  have h2 : -((shiftM a U : ℝ) - 1) ≤ m := by linarith
  have h1' : m ≤ (shiftM a U : ℤ) - 1 := by exact_mod_cast h1
  have h2' : -((shiftM a U : ℤ) - 1) ≤ m := by exact_mod_cast h2
  simp only [Finset.mem_Icc]; omega

/-- Away from the switching set, the types at `u` and `u'` agree. -/
theorem ctype_eq_of_not_switch {a U u u' x : ℝ} (ha : 0 < a) (hau : a ≤ u) (hau' : a ≤ u')
    (hx0 : 0 ≤ x) (hxU : x ≤ U) (hx : x ∉ switchSet (shiftM a U) u u') :
    ctype u x = ctype u' x := by
  set M := shiftM a U
  have H : ∀ (i : Fin 4) (j : ℤ), j ∈ Finset.Icc (-(M : ℤ)) M → _ := fun i j hj =>
    iff_of_not_mem_minmax (e := bpt u i + j * u) (e' := bpt u' i + j * u') (x := x) (by
      intro hmem; apply hx; simp only [switchSet, mem_iUnion]; exact ⟨i, j, hj, hmem⟩)
  have kN : ∀ m : ℤ, |(m : ℝ)| ≤ (U + 3) / a → (m ∈ nodeSet u x ↔ m ∈ nodeSet u' x) := by
    intro m hm
    obtain ⟨hm1, _⟩ := mem_shift_of_bound hm
    have h0 := H 0 (-m) hm1; have h1 := H 1 (-m) hm1
    simp only [bpt0, bpt1, Int.cast_neg] at h0 h1
    simp only [nodeSet, mem_setOf_eq]
    constructor
    · rintro ⟨p, q⟩
      exact ⟨by have := h0.1.1 (by linarith); linarith, by have := h1.2.1.1 (by linarith); linarith⟩
    · rintro ⟨p, q⟩
      exact ⟨by have := h0.1.2 (by linarith); linarith, by have := h1.2.1.2 (by linarith); linarith⟩
  have hN : nodeSet u x = nodeSet u' x := by
    ext m; constructor
    · intro hm; exact (kN m (nodeSet_bound ha hau hx0 hxU hm)).1 hm
    · intro hm; exact (kN m (nodeSet_bound ha hau' hx0 hxU hm)).2 hm
  have kZ : ∀ m : ℤ, |(m : ℝ)| ≤ (U + 3) / a → (m ∈ zSet u x ↔ m ∈ zSet u' x) := by
    intro m hm
    obtain ⟨hm1, _⟩ := mem_shift_of_bound hm
    have h2 := H 2 (-m) hm1; have h3 := H 3 (-m) hm1
    simp only [bpt2, bpt3, Int.cast_neg] at h2 h3
    simp only [zSet, mem_setOf_eq]
    constructor
    · rintro ⟨p, q⟩
      exact ⟨by have := h2.1.1 (by linarith); linarith, by have := h3.2.2.1 (by linarith); linarith⟩
    · rintro ⟨p, q⟩
      exact ⟨by have := h2.1.2 (by linarith); linarith, by have := h3.2.2.2 (by linarith); linarith⟩
  have hZ : zSet u x = zSet u' x := by
    ext m; constructor
    · intro hm; exact (kZ m (zSet_bound ha hau hx0 hxU hm)).1 hm
    · intro hm; exact (kZ m (zSet_bound ha hau' hx0 hxU hm)).2 hm
  have kH : ∀ m : ℤ, |(m : ℝ)| ≤ (U + 3) / a → (m ∈ hsSet u x ↔ m ∈ hsSet u' x) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := mem_shift_of_bound hm
    have h2 := H 2 (-m) hm1; have h2' := H 2 (-m - 1) hm2
    simp only [bpt2, Int.cast_neg, Int.cast_sub, Int.cast_one] at h2 h2'
    simp only [hsSet, mem_setOf_eq, hN, le_abs']
    constructor
    · rintro ⟨p, q | q⟩
      · exact ⟨p, Or.inl (by have := h2'.2.1.1 (by linarith); linarith)⟩
      · exact ⟨p, Or.inr (by have := h2.1.1 (by linarith); linarith)⟩
    · rintro ⟨p, q | q⟩
      · exact ⟨p, Or.inl (by have := h2'.2.1.2 (by linarith); linarith)⟩
      · exact ⟨p, Or.inr (by have := h2.1.2 (by linarith); linarith)⟩
  have hH : hsSet u x = hsSet u' x := by
    ext m; constructor
    · intro hm; exact (kH m (nodeSet_bound ha hau hx0 hxU hm.1)).1 hm
    · intro hm; exact (kH m (nodeSet_bound ha hau' hx0 hxU hm.1)).2 hm
  simp only [ctype, hN, hZ, hH]

theorem volume_switchSet_le (M : ℕ) {u u' : ℝ} (huu : u ≤ u') :
    volume (switchSet M u u') ≤ ENNReal.ofReal (4 * (2 * M + 1) * ((M + 1) * (u' - u))) := by
  set c : ℝ := (M + 1) * (u' - u)
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (by linarith)
  have hterm : ∀ (i : Fin 4) (m : ℤ), m ∈ Finset.Icc (-(M : ℤ)) M →
      volume (Icc (min (bpt u i + m * u) (bpt u' i + m * u'))
        (max (bpt u i + m * u) (bpt u' i + m * u'))) ≤ ENNReal.ofReal c := by
    intro i m hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    rw [max_sub_min_eq_abs, abs_sub_comm]
    have hb : |bpt u i - bpt u' i| ≤ u' - u := by
      revert i; refine fin4_cases ?_ ?_ ?_ ?_ <;>
        simp only [bpt0, bpt1, bpt2, bpt3, sub_self, abs_zero] <;> (try linarith)
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
    have hm' : |(m : ℝ)| ≤ M := by
      simp only [Finset.mem_Icc] at hm
      rw [abs_le]; constructor
      · have : -(M : ℤ) ≤ m := hm.1; exact_mod_cast this
      · exact_mod_cast hm.2
    have : bpt u i + m * u - (bpt u' i + m * u') = (bpt u i - bpt u' i) + m * (u - u') := by ring
    rw [this]
    calc |(bpt u i - bpt u' i) + m * (u - u')| ≤ |bpt u i - bpt u' i| + |(m : ℝ)| * |u - u'| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (u' - u) + M * (u' - u) := by
          rw [abs_sub_comm u u', abs_of_nonneg (show 0 ≤ u' - u by linarith)]
          have := mul_le_mul_of_nonneg_right hm' (show 0 ≤ u' - u by linarith)
          linarith

      _ = c := by simp only [c]; ring
  calc volume (switchSet M u u')
      ≤ ∑ i : Fin 4, volume (⋃ m ∈ Finset.Icc (-(M : ℤ)) M,
          Icc (min (bpt u i + m * u) (bpt u' i + m * u'))
            (max (bpt u i + m * u) (bpt u' i + m * u'))) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin 4, ∑ m ∈ Finset.Icc (-(M : ℤ)) M, ENNReal.ofReal c := by
        gcongr with i
        exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun m hm => hterm i m hm)
    _ = ENNReal.ofReal (4 * (2 * M + 1) * c) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc,
          ← ENNReal.ofReal_nsmul, ← ENNReal.ofReal_nsmul]
        congr 1
        have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
        rw [this, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring

/-- The Lipschitz constant of `meas_t` on `[a, U]`. -/
noncomputable def lipC (a U : ℝ) : ℝ := 1 + 4 * (2 * shiftM a U + 1) * (shiftM a U + 1)

/-- **`meas_t` is Lipschitz on `[a, U]`** (`a > 0`): `|meas_t(u) − meas_t(u')| ≤ C (u' − u)`. -/
theorem meas_lipschitz {a U u u' : ℝ} (ha : 0 < a) (hau : a ≤ u) (huu : u ≤ u') (hU : u' ≤ U)
    (t : CType) : |meas u t - meas u' t| ≤ lipC a U * (u' - u) := by
  set M := shiftM a U
  set Sw := switchSet M u u'
  set A := {x ∈ Ico 0 u | ctype u x = t}
  set A' := {x ∈ Ico 0 u' | ctype u' x = t}
  have hau' : a ≤ u' := hau.trans huu
  have hS := volume_switchSet_le M huu
  have hSf : volume Sw ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  have hSr : (volume Sw).toReal ≤ 4 * (2 * M + 1) * ((M + 1) * (u' - u)) :=
    ENNReal.toReal_le_of_le_ofReal (by have : 0 ≤ u' - u := by linarith
                                       positivity) hS
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    (measure_mono fun x hx => hx.1)
  have hAf' : volume A' ≠ ⊤ := ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    (measure_mono fun x hx => hx.1)
  have h1 : A ⊆ A' ∪ Sw := by
    intro x hx
    by_cases hxs : x ∈ Sw
    · exact Or.inr hxs
    · refine Or.inl ⟨⟨hx.1.1, lt_of_lt_of_le hx.1.2 huu⟩, ?_⟩
      rw [← ctype_eq_of_not_switch ha hau hau' hx.1.1 (by linarith [hx.1.2]) hxs]; exact hx.2
  have h2 : A' ⊆ (A ∪ Sw) ∪ Ico u u' := by
    intro x hx
    by_cases hxu : x < u
    · by_cases hxs : x ∈ Sw
      · exact Or.inl (Or.inr hxs)
      · refine Or.inl (Or.inl ⟨⟨hx.1.1, hxu⟩, ?_⟩)
        rw [ctype_eq_of_not_switch ha hau hau' hx.1.1 (by linarith [hx.1.2]) hxs]; exact hx.2
    · exact Or.inr ⟨not_lt.1 hxu, hx.1.2⟩
  have e1 : volume A ≤ volume A' + volume Sw := (measure_mono h1).trans (measure_union_le _ _)
  have e2 : volume A' ≤ volume A + volume Sw + ENNReal.ofReal (u' - u) := by
    refine (measure_mono h2).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Ico]; gcongr; exact measure_union_le _ _
  have r1 : meas u t ≤ meas u' t + (volume Sw).toReal := by
    unfold meas
    rw [← ENNReal.toReal_add hAf' hSf]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAf', hSf⟩) e1
  have r2 : meas u' t ≤ meas u t + (volume Sw).toReal + (u' - u) := by
    unfold meas
    rw [← ENNReal.toReal_ofReal (show 0 ≤ u' - u by linarith), ← ENNReal.toReal_add hAf hSf,
      ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hAf, hSf⟩) ENNReal.ofReal_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hAf, hSf⟩,
      ENNReal.ofReal_ne_top⟩) e2
  unfold lipC
  rw [abs_le]
  constructor <;> nlinarith

/-! ### `Gpot`: affine on cells, Lipschitz, bounded by its endpoint values -/

theorem Gpot_lipschitz (ψ : CType → ℝ) {a U u u' : ℝ} (ha : 0 < a) (hau : a ≤ u) (huu : u ≤ u')
    (hU : u' ≤ U) :
    |Gpot ψ u - Gpot ψ u'| ≤ (∑ t ∈ typeBox a, |ψ t|) * lipC a U * (u' - u) := by
  rw [Gpot_eq_sum ψ ha hau, Gpot_eq_sum ψ ha (hau.trans huu), ← Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (meas_lipschitz ha hau huu hU t) (abs_nonneg _)

theorem Gpot_affine_on_cell (ψ : CType → ℝ) {J : Set ℝ} (hJ : J.OrdConnected) {a : ℝ} (ha : 0 < a)
    (hJa : J ⊆ Ici a) (hJB : ∀ u ∈ J, u ∉ Bset) : AffOn (Gpot ψ) J := by
  have hJ0 : J ⊆ Ioi 0 := fun u hu => lt_of_lt_of_le ha (hJa hu)
  obtain ⟨α, β, h⟩ := affOn_sum (J := J) (typeBox a) (fun t u => meas u t * ψ t) fun t _ => by
    obtain ⟨a1, b1, h1⟩ := meas_affine_on_cell hJ hJ0 hJB t
    exact ⟨a1 * ψ t, b1 * ψ t, fun u hu => by
      have := h1 u hu; simp only at this; beta_reduce; rw [this]; ring⟩

  exact ⟨α, β, fun u hu => by rw [Gpot_eq_sum ψ ha (hJa hu)]; exact h u hu⟩

/-- **The endpoint bound.** If `0 < a < b` and the open interval `(a, b)` contains no point of
`𝓑`, then `Gpot ψ` is affine on `[a, b]`, so `Gpot ψ u ≤ max (Gpot ψ a) (Gpot ψ b)` for
`u ∈ [a, b]`. -/
theorem Gpot_le_max (ψ : CType → ℝ) {a b u : ℝ} (ha : 0 < a) (hab : a < b)
    (hB : ∀ v ∈ Ioo a b, v ∉ Bset) (hu : u ∈ Icc a b) :
    Gpot ψ u ≤ max (Gpot ψ a) (Gpot ψ b) := by
  obtain ⟨α, β, hG⟩ := Gpot_affine_on_cell ψ ordConnected_Ioo ha (fun v hv => le_of_lt hv.1) hB
  set K := (∑ t ∈ typeBox a, |ψ t|) * lipC a b
  have hK : 0 ≤ K := by
    apply mul_nonneg (Finset.sum_nonneg fun t _ => abs_nonneg _)
    unfold lipC; positivity
  have endA : Gpot ψ a = α + β * a := by
    by_contra hne
    set d := |Gpot ψ a - (α + β * a)|
    have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
    set δ := min ((b - a) / 2) (d / (2 * (K + |β| + 1)))
    have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
    have hδ1 : δ ≤ (b - a) / 2 := min_le_left _ _
    have hδ2 : δ ≤ d / (2 * (K + |β| + 1)) := min_le_right _ _
    have hv : a + δ ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hL := Gpot_lipschitz ψ ha le_rfl (show a ≤ a + δ by linarith) hv.2.le
    rw [hG _ hv] at hL
    have : d ≤ K * δ + |β| * δ := by
      have e : Gpot ψ a - (α + β * a) = (Gpot ψ a - (α + β * (a + δ))) + β * δ := by ring
      calc d = |(Gpot ψ a - (α + β * (a + δ))) + β * δ| := by rw [← e]
        _ ≤ |Gpot ψ a - (α + β * (a + δ))| + |β * δ| := abs_add_le _ _
        _ ≤ K * δ + |β| * δ := by
            rw [abs_mul, abs_of_pos hδ0]; simp only [add_sub_cancel_left] at hL
            linarith
    have h3 : (K + |β|) * δ ≤ (K + |β|) * (d / (2 * (K + |β| + 1))) :=
      mul_le_mul_of_nonneg_left hδ2 (by positivity)
    have h4 : (K + |β|) * (d / (2 * (K + |β| + 1))) < d := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg β]
    linarith
  have endB : Gpot ψ b = α + β * b := by
    by_contra hne
    set d := |Gpot ψ b - (α + β * b)|
    have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
    set δ := min ((b - a) / 2) (d / (2 * (K + |β| + 1)))
    have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
    have hδ1 : δ ≤ (b - a) / 2 := min_le_left _ _
    have hδ2 : δ ≤ d / (2 * (K + |β| + 1)) := min_le_right _ _
    have hv : b - δ ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hL := Gpot_lipschitz ψ ha hv.1.le (show b - δ ≤ b by linarith) le_rfl
    rw [hG _ hv] at hL
    have : d ≤ K * δ + |β| * δ := by
      have e : Gpot ψ b - (α + β * b) = -((α + β * (b - δ)) - Gpot ψ b) - β * δ := by ring
      calc d = |-((α + β * (b - δ)) - Gpot ψ b) - β * δ| := by rw [← e]
        _ ≤ |-((α + β * (b - δ)) - Gpot ψ b)| + |β * δ| := abs_sub _ _
        _ ≤ K * δ + |β| * δ := by
            rw [abs_neg, abs_mul, abs_of_pos hδ0]
            have : b - (b - δ) = δ := by ring
            rw [this] at hL
            linarith
    have h3 : (K + |β|) * δ ≤ (K + |β|) * (d / (2 * (K + |β| + 1))) :=
      mul_le_mul_of_nonneg_left hδ2 (by positivity)
    have h4 : (K + |β|) * (d / (2 * (K + |β| + 1))) < d := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg β]
    linarith
  have hGu : Gpot ψ u = α + β * u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, endA]
    rcases eq_or_lt_of_le hu.2 with h' | h'
    · rw [h', endB]
    · exact hG u ⟨h, h'⟩
  rw [hGu, endA, endB]
  rcases le_total 0 β with hβ | hβ
  · exact le_max_of_le_right (by nlinarith [hu.2])
  · exact le_max_of_le_left (by nlinarith [hu.1])

end Hankel2.Circle
