import Mathlib

/-!
# The circle model (paper §8.4): definitions and Lemma 8.6 (Cells)

Put `u = p/n`.  The residue class `r mod p` is identified with the position `x = r/n` on the
circle `ℝ/uℤ`.  In the limit `n → ∞` the class at position `x` has

* nodes at the points `y = x + m u ∈ [−1, 2]` (`nodeSet u x`, their number is `N`);
* `z(x) = #{y ∈ [0,1) : y + u/2 ≡ x (mod u)}` (`zSet u x`), since `2j+1 ≡ 2k ⟺ k ≡ j + (p+1)/2`;
* an `hs`-node at `y` iff `|y| ≥ u/2` (`hsSet u x`, their number is `h`).

The **type** of the position is `ctype u x = (N, z, h)` (the node data `(o, z, μ, hs)` of all
nodes of the class are functions of `(N, z, h)`, see `ClassType.lean`; the rare `g` is treated as an
error term).  `meas u t` is the Lebesgue measure of the set of positions `x ∈ [0, u)` of type
`t`, and for a weight `ψ` on types `Gpot ψ u = ∑_t meas_t(u) ψ(t)`.

`Bset = {c/m, 2c/(2m−1) : c ∈ {1,2,3}, m ≥ 1}` is the set `𝓑` of the paper.

Main results (Lemma 8.6):
* `ctype_const_of_avoid`: the type is constant on every interval avoiding the four boundary points
  `−1, 2, u/2, u/2 + 1` (mod `u`), collected in `Ebad u`;
* `meas_affine_on_cell`: on every interval `J ⊆ (0,∞)` containing no point of `𝓑`, each
  `meas_t` is an affine function of `u`;
* `types_const_on_cell`: on such `J` the set of types (of positive measure) is constant;
* `meas_lipschitz`: `meas_t` is Lipschitz on `[a, U]` for `a > 0` (so it is continuous also
  across the points of `𝓑`);
* `Gpot_le_max`: on a closed interval whose interior avoids `𝓑`, `Gpot ψ` is bounded by its
  values at the two endpoints.
-/

open MeasureTheory Set

namespace Hankel2.Circle

/-! ### Definitions -/

/-- The four boundary points `−1, 2, u/2, u/2 + 1` of the circle model. -/
noncomputable def bpt (u : ℝ) : Fin 4 → ℝ := ![-1, 2, u / 2, u / 2 + 1]

/-- The nodes `x + m u ∈ [−1, 2]` of the class at position `x` (indexed by `m`). -/
def nodeSet (u x : ℝ) : Set ℤ := {m | -1 ≤ x + m * u ∧ x + m * u ≤ 2}

/-- The zeros `y ∈ [0,1)` with `y + u/2 ≡ x (mod u)` (indexed by `m`, `y = x − u/2 + m u`). -/
def zSet (u x : ℝ) : Set ℤ := {m | 0 ≤ x - u / 2 + m * u ∧ x - u / 2 + m * u < 1}

/-- The `hs`-nodes: nodes `y` with `|y| ≥ u/2`. -/
def hsSet (u x : ℝ) : Set ℤ := {m | m ∈ nodeSet u x ∧ u / 2 ≤ |x + m * u|}

/-- A class type `(N, z, h)`: number of nodes, number of zeros, number of `hs`-nodes. -/
abbrev CType := ℕ × ℕ × ℕ

/-- The type of the class at position `x` of the circle `ℝ/uℤ`. -/
noncomputable def ctype (u x : ℝ) : CType :=
  ((nodeSet u x).ncard, (zSet u x).ncard, (hsSet u x).ncard)

/-- The boundary points `−1, 2, u/2, u/2 + 1` modulo `u`. -/
def Ebad (u : ℝ) : Set ℝ := {e | ∃ i : Fin 4, ∃ m : ℤ, e = bpt u i + m * u}

/-- `meas_t(u)`: the measure of the set of positions `x ∈ [0, u)` of type `t`. -/
noncomputable def meas (u : ℝ) (t : CType) : ℝ := (volume {x ∈ Ico 0 u | ctype u x = t}).toReal

/-- `∑_t meas_t(u) ψ(t)` (only finitely many types have positive measure, see `Gpot_eq_sum`). -/
noncomputable def Gpot (ψ : CType → ℝ) (u : ℝ) : ℝ := ∑ᶠ t, meas u t * ψ t

/-- The set `𝓑 = {c/m, 2c/(2m−1) : c ∈ {1,2,3}, m ≥ 1}` of the paper (Lemma 8.6). -/
def Bset : Set ℝ :=
  {b | ∃ c : ℕ, c ∈ ({1, 2, 3} : Finset ℕ) ∧ ∃ m : ℕ, 1 ≤ m ∧
    (b = (c : ℝ) / m ∨ b = 2 * (c : ℝ) / (2 * (m : ℝ) - 1))}

/-- A function is affine on `J`. -/
def AffOn (f : ℝ → ℝ) (J : Set ℝ) : Prop := ∃ a b : ℝ, ∀ u ∈ J, f u = a + b * u

/-! ### Constancy of the type away from the boundary points -/

theorem bpt_add_mem_Ebad (u : ℝ) (i : Fin 4) (m : ℤ) : bpt u i + m * u ∈ Ebad u := ⟨i, m, rfl⟩

/-- Threshold comparisons are constant on an interval avoiding the threshold. -/
theorem le_iff_of_not_mem {e x x' : ℝ} (hxx : x ≤ x') (he : e ∉ Icc x x') :
    (e ≤ x ↔ e ≤ x') ∧ (x ≤ e ↔ x' ≤ e) ∧ (x < e ↔ x' < e) := by
  simp only [mem_Icc, not_and_or, not_le] at he
  rcases he with h | h
  · refine ⟨⟨fun h' => by linarith, fun h' => by linarith⟩, ⟨fun _ => by linarith, fun h' => by linarith⟩,
      ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
  · refine ⟨⟨fun h' => by linarith, fun h' => by linarith⟩, ⟨fun _ => by linarith, fun h' => by linarith⟩,
      ⟨fun _ => by linarith, fun h' => by linarith⟩⟩

/-- **The type is constant on every interval `[x, x']` containing no boundary point**
(`−1, 2, u/2, u/2+1` mod `u`). -/
theorem ctype_const_of_avoid {u x x' : ℝ} (hxx : x ≤ x') (h : ∀ e ∈ Ebad u, e ∉ Icc x x') :
    ctype u x = ctype u x' := by
  have H : ∀ (i : Fin 4) (m : ℤ), _ := fun i m => le_iff_of_not_mem hxx (h _ (bpt_add_mem_Ebad u i m))
  have hN : nodeSet u x = nodeSet u x' := by
    ext m
    have h0 := H 0 (-m); have h1 := H 1 (-m)
    simp only [bpt, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg] at h0 h1
    simp only [nodeSet, mem_setOf_eq]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by have := h0.1.1 (by linarith); linarith, by have := h1.2.1.1 (by linarith); linarith⟩
    · rintro ⟨a, b⟩
      exact ⟨by have := h0.1.2 (by linarith); linarith, by have := h1.2.1.2 (by linarith); linarith⟩
  have hZ : zSet u x = zSet u x' := by
    ext m
    have h2 := H 2 (-m); have h3 := H 3 (-m)
    simp only [bpt, Int.cast_neg] at h2 h3
    simp only [Matrix.cons_val] at h2 h3
    simp only [zSet, mem_setOf_eq]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by have := h2.1.1 (by linarith); linarith, by have := h3.2.2.1 (by linarith); linarith⟩
    · rintro ⟨a, b⟩
      exact ⟨by have := h2.1.2 (by linarith); linarith, by have := h3.2.2.2 (by linarith); linarith⟩
  have hH : hsSet u x = hsSet u x' := by
    ext m
    have h2 := H 2 (-m); have h2' := H 2 (-m - 1)
    simp only [bpt, Int.cast_neg, Int.cast_sub, Int.cast_one] at h2 h2'
    simp only [Matrix.cons_val] at h2 h2'
    simp only [hsSet, mem_setOf_eq, hN, le_abs']
    constructor
    · rintro ⟨a, b | b⟩
      · refine ⟨a, Or.inl ?_⟩
        have := h2'.2.1.1 (by linarith); linarith
      · refine ⟨a, Or.inr ?_⟩
        have := h2.1.1 (by linarith); linarith
    · rintro ⟨a, b | b⟩
      · refine ⟨a, Or.inl ?_⟩
        have := h2'.2.1.2 (by linarith); linarith
      · refine ⟨a, Or.inr ?_⟩
        have := h2.1.2 (by linarith); linarith
  simp only [ctype, hN, hZ, hH]


/-! ### Representatives of the boundary points and the combinatorial type -/

/-- `k_i(u) = ⌊b_i/u⌋`. -/
noncomputable def kk (u : ℝ) (i : Fin 4) : ℤ := ⌊bpt u i / u⌋

/-- The representative `ρ_i(u) = b_i − k_i(u) u ∈ [0, u)` of the boundary point `b_i`. -/
noncomputable def rho (u : ℝ) (i : Fin 4) : ℝ := bpt u i - kk u i * u

theorem bpt_eq_rho (u : ℝ) (i : Fin 4) : bpt u i = rho u i + kk u i * u := by
  unfold rho; ring

theorem rho_nonneg {u : ℝ} (hu : 0 < u) (i : Fin 4) : 0 ≤ rho u i := by
  unfold rho kk
  have := Int.floor_le (bpt u i / u)
  have h := mul_le_mul_of_nonneg_right this hu.le
  rw [div_mul_cancel₀ _ hu.ne'] at h
  linarith

theorem rho_lt {u : ℝ} (hu : 0 < u) (i : Fin 4) : rho u i < u := by
  unfold rho kk
  have := Int.lt_floor_add_one (bpt u i / u)
  have h := mul_lt_mul_of_pos_right this hu
  rw [div_mul_cancel₀ _ hu.ne'] at h
  linarith

theorem ge_iff_int {u x r : ℝ} (hx0 : 0 ≤ x) (hxu : x < u) (hr0 : 0 ≤ r) (hru : r < u) (j : ℤ) :
    r + j * u ≤ x ↔ j < 0 ∨ (j = 0 ∧ r ≤ x) := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    simp only [hj, true_or, iff_true]; nlinarith
  · subst hj; simp
  · have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    simp only [show ¬ j < 0 by omega, show j ≠ 0 by omega, false_and, or_self, iff_false, not_le]
    nlinarith

theorem le_iff_int {u x r : ℝ} (hx0 : 0 ≤ x) (hxu : x < u) (hr0 : 0 ≤ r) (hru : r < u) (j : ℤ) :
    x ≤ r + j * u ↔ 0 < j ∨ (j = 0 ∧ x ≤ r) := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    simp only [show ¬ 0 < j by omega, show j ≠ 0 by omega, false_and, or_self, iff_false, not_le]
    nlinarith
  · subst hj; simp
  · have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    simp only [hj, true_or, iff_true]; nlinarith

/-- The bit vector `β_i = 1[x < ρ_i(u)]` of a position. -/
noncomputable def bits (u x : ℝ) : Fin 4 → Bool := fun i => decide (x < rho u i)

/-- The nodes, in terms of the integer data `k` and the bits `β`. -/
def tauN (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : Set ℤ :=
  {m | (k 0 < m ∨ (m = k 0 ∧ β 0 = false)) ∧ (m < k 1 ∨ (m = k 1 ∧ β 1 = true))}

/-- The zeros, in terms of `k` and `β`. -/
def tauZ (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : Set ℤ :=
  {m | (k 2 < m ∨ (m = k 2 ∧ β 2 = false)) ∧ (m < k 3 ∨ (m = k 3 ∧ β 3 = true))}

/-- The `hs`-nodes, in terms of `k` and `β`. -/
def tauH (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : Set ℤ :=
  {m | m ∈ tauN k β ∧ ((k 2 < m ∨ (m = k 2 ∧ β 2 = false)) ∨
    (m + 1 < k 2 ∨ (m + 1 = k 2 ∧ β 2 = true)))}

/-- The combinatorial type determined by `k` and `β`. -/
noncomputable def tau (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : CType :=
  ((tauN k β).ncard, (tauZ k β).ncard, (tauH k β).ncard)

/-- **The type of a position is a function of the integer data `k(u)` and of the bits.** -/
theorem ctype_eq_tau {u x : ℝ} (hu : 0 < u) (hx0 : 0 ≤ x) (hxu : x < u)
    (hne : ∀ i, x ≠ rho u i) : ctype u x = tau (kk u) (bits u x) := by
  have A : ∀ i (j : ℤ), rho u i + j * u ≤ x ↔ j < 0 ∨ (j = 0 ∧ bits u x i = false) := by
    intro i j
    rw [ge_iff_int hx0 hxu (rho_nonneg hu i) (rho_lt hu i) j]
    simp [bits, not_lt]
  have Bq : ∀ i (j : ℤ), x ≤ rho u i + j * u ↔ 0 < j ∨ (j = 0 ∧ bits u x i = true) := by
    intro i j
    rw [le_iff_int hx0 hxu (rho_nonneg hu i) (rho_lt hu i) j]
    simp only [bits, decide_eq_true_eq]
    have := hne i
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, lt_of_le_of_ne h2 this⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2.le⟩
  have e : ∀ i (m : ℤ), rho u i + ((kk u i - m : ℤ) : ℝ) * u = bpt u i - m * u := by
    intro i m; rw [bpt_eq_rho]; push_cast; ring
  have b0 : bpt u 0 = -1 := rfl
  have b1 : bpt u 1 = 2 := rfl
  have b2 : bpt u 2 = u / 2 := rfl
  have b3 : bpt u 3 = u / 2 + 1 := rfl
  have c1 : ∀ m : ℤ, -1 ≤ x + m * u ↔ (kk u 0 < m ∨ (m = kk u 0 ∧ bits u x 0 = false)) := by
    intro m
    have := A 0 (kk u 0 - m); rw [e, b0] at this
    rw [show (-1 ≤ x + m * u) ↔ (-1 - m * u ≤ x) from ⟨fun h => by linarith, fun h => by linarith⟩,
      this]
    cases bits u x 0 <;> simp <;> omega
  have c2 : ∀ m : ℤ, x + m * u ≤ 2 ↔ (m < kk u 1 ∨ (m = kk u 1 ∧ bits u x 1 = true)) := by
    intro m
    have := Bq 1 (kk u 1 - m); rw [e, b1] at this
    rw [show (x + m * u ≤ 2) ↔ (x ≤ 2 - m * u) from ⟨fun h => by linarith, fun h => by linarith⟩,
      this]
    cases bits u x 1 <;> simp <;> omega
  have c3 : ∀ m : ℤ, u / 2 ≤ x + m * u ↔ (kk u 2 < m ∨ (m = kk u 2 ∧ bits u x 2 = false)) := by
    intro m
    have := A 2 (kk u 2 - m); rw [e, b2] at this
    rw [show (u / 2 ≤ x + m * u) ↔ (u / 2 - m * u ≤ x) from
      ⟨fun h => by linarith, fun h => by linarith⟩, this]
    cases bits u x 2 <;> simp <;> omega
  have c4 : ∀ m : ℤ, x - u / 2 + m * u < 1 ↔ (m < kk u 3 ∨ (m = kk u 3 ∧ bits u x 3 = true)) := by
    intro m
    have := A 3 (kk u 3 - m); rw [e, b3] at this
    rw [show (x - u / 2 + m * u < 1) ↔ ¬ (u / 2 + 1 - m * u ≤ x) from
      ⟨fun h h' => by linarith, fun h => by push_neg at h; linarith⟩, this]
    cases bits u x 3 <;> simp <;> omega
  have c5 : ∀ m : ℤ, x + m * u ≤ -(u / 2) ↔
      (m + 1 < kk u 2 ∨ (m + 1 = kk u 2 ∧ bits u x 2 = true)) := by
    intro m
    have := Bq 2 (kk u 2 - (m + 1)); rw [e, b2] at this
    rw [show (x + m * u ≤ -(u / 2)) ↔ (x ≤ u / 2 - ((m + 1 : ℤ) : ℝ) * u) from
      ⟨fun h => by push_cast; linarith, fun h => by push_cast at h; linarith⟩, this]
    cases bits u x 2 <;> simp <;> omega
  have hN : nodeSet u x = tauN (kk u) (bits u x) := by
    ext m; simp only [nodeSet, tauN, mem_setOf_eq, c1, c2]
  have hZ : zSet u x = tauZ (kk u) (bits u x) := by
    ext m
    simp only [zSet, tauZ, mem_setOf_eq, ← c3, c4]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  have hH : hsSet u x = tauH (kk u) (bits u x) := by
    ext m
    simp only [hsSet, tauH, mem_setOf_eq, hN, le_abs', ← c3, ← c5]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inr (by linarith)⟩
      · exact ⟨h1, Or.inl h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inr h2⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
  simp only [ctype, tau, hN, hZ, hH]


/-! ### The measure of a type as a sum of gap lengths -/

/-- The positions `x ∈ [0, u)` with bit vector `β`. -/
def Ibeta (u : ℝ) (β : Fin 4 → Bool) : Set ℝ :=
  {x | x ∈ Ico 0 u ∧ ∀ i, (x < rho u i ↔ β i = true)}

/-- The lower end of the gap with bit vector `β`: `max(0, max_{β_i = 0} ρ_i)`. -/
noncomputable def lowF (u : ℝ) (β : Fin 4 → Bool) (i : Fin 4) : ℝ := if β i then 0 else rho u i

/-- The upper end of the gap with bit vector `β`: `min(u, min_{β_i = 1} ρ_i)`. -/
noncomputable def upF (u : ℝ) (β : Fin 4 → Bool) (i : Fin 4) : ℝ := if β i then rho u i else u

noncomputable def Lbeta (u : ℝ) (β : Fin 4 → Bool) : ℝ :=
  max (max (max (lowF u β 0) (lowF u β 1)) (lowF u β 2)) (lowF u β 3)

noncomputable def Rbeta (u : ℝ) (β : Fin 4 → Bool) : ℝ :=
  min (min (min (upF u β 0) (upF u β 1)) (upF u β 2)) (upF u β 3)

theorem forall_fin4 {P : Fin 4 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> assumption

theorem Ibeta_eq {u : ℝ} (hu : 0 < u) (β : Fin 4 → Bool) :
    Ibeta u β = Ico (Lbeta u β) (Rbeta u β) := by
  ext x
  have hL : Lbeta u β ≤ x ↔ ∀ i, lowF u β i ≤ x := by
    simp only [Lbeta, max_le_iff, forall_fin4, and_assoc]
  have hR : x < Rbeta u β ↔ ∀ i, x < upF u β i := by
    simp only [Rbeta, lt_min_iff, forall_fin4, and_assoc]
  simp only [Ibeta, mem_setOf_eq, mem_Ico, hL, hR, lowF, upF]
  constructor
  · rintro ⟨⟨h0, hu'⟩, h⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h i; split_ifs with hb
      · exact h0
      · simp only [hb, Bool.false_eq_true, iff_false, not_lt] at this; exact this
    · have := h i; split_ifs with hb
      · exact this.2 hb
      · exact hu'
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x := by
      have := h1 0; split_ifs at this with hb
      · exact this
      · exact (rho_nonneg hu 0).trans this
    have hxu : x < u := by
      have := h2 0; split_ifs at this with hb
      · exact this.trans (rho_lt hu 0)
      · exact this
    refine ⟨⟨hx0, hxu⟩, fun i => ?_⟩
    have a1 := h1 i; have a2 := h2 i
    by_cases hb : β i = true
    · simp only [hb, if_true] at a2; simp only [hb, iff_true]; exact a2
    · simp only [hb, if_false, Bool.false_eq_true] at a1 ⊢
      simp only [iff_false, not_lt]; exact a1

theorem measurableSet_Ibeta {u : ℝ} (hu : 0 < u) (β : Fin 4 → Bool) : MeasurableSet (Ibeta u β) := by
  rw [Ibeta_eq hu]; exact measurableSet_Ico

theorem volume_Ibeta {u : ℝ} (hu : 0 < u) (β : Fin 4 → Bool) :
    (volume (Ibeta u β)).toReal = max (Rbeta u β - Lbeta u β) 0 := by
  rw [Ibeta_eq hu, Real.volume_Ico, ENNReal.toReal_ofReal']

theorem bits_eq_of_mem {u x : ℝ} {β : Fin 4 → Bool} (hx : x ∈ Ibeta u β) : bits u x = β := by
  funext i
  have := hx.2 i
  simp only [bits]
  by_cases h : x < rho u i
  · rw [decide_eq_true h]; exact (this.1 h).symm
  · rw [decide_eq_false h]
    cases hb : β i
    · rfl
    · exact absurd (this.2 hb) h

theorem mem_Ibeta_bits {u x : ℝ} (hx : x ∈ Ico 0 u) : x ∈ Ibeta u (bits u x) :=
  ⟨hx, fun i => by simp [bits]⟩

/-- **`meas_t(u)` is a sum of gap lengths**: for every `u > 0`,
`meas_t(u) = ∑_{β : τ(k(u), β) = t} max(R_β(u) − L_β(u), 0)`. -/
theorem meas_eq_sum {u : ℝ} (hu : 0 < u) (t : CType) :
    meas u t = ∑ β ∈ Finset.univ.filter (fun β => tau (kk u) β = t),
      max (Rbeta u β - Lbeta u β) 0 := by
  classical
  set S := Finset.univ.filter (fun β : Fin 4 → Bool => tau (kk u) β = t)
  set A := {x ∈ Ico 0 u | ctype u x = t}
  set F := range (rho u)
  set U := ⋃ β ∈ S, Ibeta u β
  have hF : volume F = 0 := (Set.finite_range _).measure_zero _
  have hAU : A \ F = U \ F := by
    ext x
    simp only [A, U, F, mem_diff, mem_setOf_eq, mem_iUnion, mem_range, not_exists, exists_prop]
    constructor
    · rintro ⟨⟨hx, ht⟩, hne⟩
      refine ⟨⟨bits u x, ?_, mem_Ibeta_bits hx⟩, hne⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ht, ctype_eq_tau hu hx.1 hx.2 fun i h => hne i h.symm]
    · rintro ⟨⟨β, hβ, hx⟩, hne⟩
      refine ⟨⟨hx.1, ?_⟩, hne⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hβ
      rw [ctype_eq_tau hu hx.1.1 hx.1.2 fun i h => hne i h.symm, bits_eq_of_mem hx, hβ]
  have hA : volume A = volume U := by
    rw [← measure_diff_null hF, hAU, measure_diff_null hF]
  have hdisj : Set.PairwiseDisjoint (↑S) (fun β => Ibeta u β) := by
    intro β _ β' _ hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    rw [← bits_eq_of_mem hx, ← bits_eq_of_mem hx']
  have hU : volume U = ∑ β ∈ S, volume (Ibeta u β) :=
    measure_biUnion_finset hdisj fun β _ => measurableSet_Ibeta hu β
  unfold meas
  rw [hA, hU, ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl fun β _ => volume_Ibeta hu β
  · intro β _
    rw [Ibeta_eq hu, Real.volume_Ico]; exact ENNReal.ofReal_ne_top

/-! ### The set `𝓑` and the cells -/

theorem memB1 {u : ℝ} (hu : 0 < u) {c : ℕ} (hc : c ∈ ({1, 2, 3} : Finset ℕ)) {m : ℤ}
    (h : (c : ℝ) / u = m) : u ∈ Bset := by
  have hc0 : (0 : ℝ) < c := by
    have : 1 ≤ c := by simp at hc; omega
    exact_mod_cast this
  have hm : (0 : ℝ) < m := by rw [← h]; positivity
  have hm' : 1 ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hm)
  refine ⟨c, hc, m.toNat, by omega, Or.inl ?_⟩
  have : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [this, ← h]; field_simp

theorem memB2 {u : ℝ} (hu : 0 < u) {c : ℕ} (hc : c ∈ ({1, 2, 3} : Finset ℕ)) {m : ℤ}
    (h : (c : ℝ) / u + 1 / 2 = m) : u ∈ Bset := by
  have hc0 : (0 : ℝ) < c := by
    have : 1 ≤ c := by simp at hc; omega
    exact_mod_cast this
  have hcu : 0 < (c : ℝ) / u := by positivity
  have hm : (1 / 2 : ℝ) < m := by rw [← h]; linarith
  have hm' : 1 ≤ m := by
    by_contra hcon
    have : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    linarith
  refine ⟨c, hc, m.toNat, by omega, Or.inr ?_⟩
  have : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [this, ← h]; field_simp; ring

theorem fin4_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i; fin_cases i <;> assumption

theorem bpt0 (u : ℝ) : bpt u 0 = -1 := rfl
theorem bpt1 (u : ℝ) : bpt u 1 = 2 := rfl
theorem bpt2 (u : ℝ) : bpt u 2 = u / 2 := rfl
theorem bpt3 (u : ℝ) : bpt u 3 = u / 2 + 1 := rfl

theorem bpt_div_ne_int {u : ℝ} (hu : 0 < u) (hB : u ∉ Bset) (i : Fin 4) (m : ℤ) :
    bpt u i / u ≠ m := by
  revert i
  refine fin4_cases ?_ ?_ ?_ ?_ <;> intro h <;> simp only [bpt0, bpt1, bpt2, bpt3] at h
  · exact hB (memB1 hu (c := 1) (by simp) (m := -m) (by push_cast; rw [← h]; ring))
  · exact hB (memB1 hu (c := 2) (by simp) (m := m) (by push_cast; rw [← h]))
  · have : (u / 2) / u = 1 / 2 := by field_simp
    rw [this] at h
    have h2 : (2 : ℝ) * m = 1 := by rw [← h]; ring
    have : (2 : ℤ) * m = 1 := by exact_mod_cast h2
    omega
  · exact hB (memB2 hu (c := 1) (by simp) (m := m) (by push_cast; rw [← h]; field_simp; ring))

/-- For `u ∉ 𝓑`, no boundary point is `≡ 0 (mod u)`. -/
theorem rho_ne_zero {u : ℝ} (hu : 0 < u) (hB : u ∉ Bset) (i : Fin 4) : rho u i ≠ 0 := by
  intro h
  apply bpt_div_ne_int hu hB i (kk u i)
  have : bpt u i = kk u i * u := by rw [bpt_eq_rho, h, zero_add]
  rw [this]; field_simp

/-- For `u ∉ 𝓑`, the four boundary points are distinct modulo `u`. -/
theorem rho_ne {u : ℝ} (hu : 0 < u) (hB : u ∉ Bset) {i j : Fin 4} (hij : i ≠ j) :
    rho u i ≠ rho u j := by
  intro h
  set d := kk u i - kk u j
  have hd : (bpt u i - bpt u j) / u = d := by
    rw [bpt_eq_rho u i, bpt_eq_rho u j, h]; simp only [d]; push_cast; field_simp; ring
  have key : ∀ i j : Fin 4, i ≠ j → ∀ d : ℤ, (bpt u i - bpt u j) / u = d → False := by
    refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> intro hij d hd <;>
      simp only [bpt0, bpt1, bpt2, bpt3, ne_eq, not_true_eq_false] at hd hij
    · exact hB (memB1 hu (c := 3) (by simp) (m := -d) (by push_cast; rw [← hd]; ring))
    · exact hB (memB2 hu (c := 1) (by simp) (m := -d) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 2) (by simp) (m := -d) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB1 hu (c := 3) (by simp) (m := d) (by push_cast; rw [← hd]; ring))
    · exact hB (memB2 hu (c := 2) (by simp) (m := d + 1) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 1) (by simp) (m := d + 1) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 1) (by simp) (m := d) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 2) (by simp) (m := -d + 1) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB1 hu (c := 1) (by simp) (m := -d) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 2) (by simp) (m := d) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB2 hu (c := 1) (by simp) (m := -d + 1) (by push_cast; rw [← hd]; field_simp; ring))
    · exact hB (memB1 hu (c := 1) (by simp) (m := d) (by push_cast; rw [← hd]; field_simp; ring))
  exact key i j hij d hd

theorem continuousOn_bpt_div {J : Set ℝ} (hJ0 : J ⊆ Ioi 0) (i : Fin 4) :
    ContinuousOn (fun v => bpt v i / v) J := by
  have hc : Continuous (fun v : ℝ => bpt v i) := by
    revert i
    refine fin4_cases ?_ ?_ ?_ ?_
    · simp only [bpt0]; exact continuous_const
    · simp only [bpt1]; exact continuous_const
    · simp only [bpt2]; fun_prop
    · simp only [bpt3]; fun_prop
  exact hc.continuousOn.div continuousOn_id fun v hv => (hJ0 hv).ne'

/-- **On a cell the integer data `k(u)` is constant.** -/
theorem kk_const {J : Set ℝ} (hJ : J.OrdConnected) (hJ0 : J ⊆ Ioi 0) (hJB : ∀ u ∈ J, u ∉ Bset)
    {u u' : ℝ} (hu : u ∈ J) (hu' : u' ∈ J) (i : Fin 4) : kk u i = kk u' i := by
  have key : ∀ v ∈ J, ∀ v' ∈ J, ¬ (kk v i < kk v' i) := by
    intro v hv v' hv' hlt
    set m := kk v' i
    have h1 : bpt v i / v < m := by
      have := Int.lt_floor_add_one (bpt v i / v)
      have h : (kk v i : ℝ) + 1 ≤ m := by exact_mod_cast hlt
      simp only [kk] at h; linarith
    have h2 : (m : ℝ) ≤ bpt v' i / v' := Int.floor_le _
    have hsub : uIcc v v' ⊆ J := hJ.uIcc_subset hv hv'
    obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc ((continuousOn_bpt_div hJ0 i).mono hsub)
      (show (m : ℝ) ∈ uIcc (bpt v i / v) (bpt v' i / v') from
        Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2⟩))
    exact bpt_div_ne_int (hJ0 (hsub hc)) (hJB c (hsub hc)) i m hfc
  rcases lt_trichotomy (kk u i) (kk u' i) with h | h | h
  · exact absurd h (key u hu u' hu')
  · exact h
  · exact absurd h (key u' hu' u hu)

/-! ### Affine functions and comparability on an interval -/

/-- Two functions are comparable on `J` if one is `≤` the other throughout `J`. -/
def Cmp (J : Set ℝ) (f g : ℝ → ℝ) : Prop := (∀ u ∈ J, f u ≤ g u) ∨ (∀ u ∈ J, g u ≤ f u)

theorem Cmp.symm {J : Set ℝ} {f g : ℝ → ℝ} (h : Cmp J f g) : Cmp J g f := Or.symm h

theorem cmp_refl (J : Set ℝ) (f : ℝ → ℝ) : Cmp J f f := Or.inl fun _ _ => le_rfl

/-- Two affine functions without coincidence on an interval are comparable there. -/
theorem cmp_of_ne {J : Set ℝ} (hJ : J.OrdConnected) {f g : ℝ → ℝ} (hf : AffOn f J)
    (hg : AffOn g J) (hne : ∀ u ∈ J, f u ≠ g u) : Cmp J f g := by
  by_contra hc
  simp only [Cmp, not_or, not_forall, not_le] at hc
  obtain ⟨⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩ := hc
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨a', b', hab'⟩ := hg
  have hconv : Convex ℝ J := hJ.convex
  set d1 := f u1 - g u1
  set d2 := f u2 - g u2
  have hd1 : 0 < d1 := by simp only [d1]; linarith
  have hd2 : d2 < 0 := by simp only [d2]; linarith
  set t := d1 / (d1 - d2)
  have ht0 : 0 ≤ t := div_nonneg hd1.le (by linarith)
  have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hc : (1 - t) • u1 + t • u2 ∈ J := hconv hu1 hu2 (by linarith) ht0 (by ring)
  apply hne _ hc
  rw [hab _ hc, hab' _ hc]
  have e1 : d1 = (a - a') + (b - b') * u1 := by simp only [d1]; rw [hab _ hu1, hab' _ hu1]; ring
  have e2 : d2 = (a - a') + (b - b') * u2 := by simp only [d2]; rw [hab _ hu2, hab' _ hu2]; ring
  have htd : t * (d1 - d2) = d1 := div_mul_cancel₀ _ (by linarith)
  simp only [smul_eq_mul]
  have : (a + b * ((1 - t) * u1 + t * u2)) - (a' + b' * ((1 - t) * u1 + t * u2)) = 0 := by
    have : (a + b * ((1 - t) * u1 + t * u2)) - (a' + b' * ((1 - t) * u1 + t * u2)) =
        d1 - t * (d1 - d2) := by rw [e1, e2]; ring
    rw [this, htd]; ring
  linarith

theorem affOn_max {J : Set ℝ} {f g : ℝ → ℝ} (hf : AffOn f J) (hg : AffOn g J) (h : Cmp J f g) :
    AffOn (fun u => max (f u) (g u)) J := by
  rcases h with h | h
  · obtain ⟨a, b, hab⟩ := hg; exact ⟨a, b, fun u hu => by beta_reduce; rw [max_eq_right (h u hu), hab u hu]⟩
  · obtain ⟨a, b, hab⟩ := hf; exact ⟨a, b, fun u hu => by beta_reduce; rw [max_eq_left (h u hu), hab u hu]⟩

theorem affOn_min {J : Set ℝ} {f g : ℝ → ℝ} (hf : AffOn f J) (hg : AffOn g J) (h : Cmp J f g) :
    AffOn (fun u => min (f u) (g u)) J := by
  rcases h with h | h
  · obtain ⟨a, b, hab⟩ := hf; exact ⟨a, b, fun u hu => by beta_reduce; rw [min_eq_left (h u hu), hab u hu]⟩
  · obtain ⟨a, b, hab⟩ := hg; exact ⟨a, b, fun u hu => by beta_reduce; rw [min_eq_right (h u hu), hab u hu]⟩

theorem cmp_max {J : Set ℝ} {f g h : ℝ → ℝ} (hf : Cmp J f h) (hg : Cmp J g h) :
    Cmp J (fun u => max (f u) (g u)) h := by
  rcases hf with hf | hf
  · rcases hg with hg | hg
    · exact Or.inl fun u hu => max_le (hf u hu) (hg u hu)
    · exact Or.inr fun u hu => (hg u hu).trans (le_max_right _ _)
  · exact Or.inr fun u hu => (hf u hu).trans (le_max_left _ _)

theorem cmp_min {J : Set ℝ} {f g h : ℝ → ℝ} (hf : Cmp J f h) (hg : Cmp J g h) :
    Cmp J (fun u => min (f u) (g u)) h := by
  rcases hf with hf | hf
  · exact Or.inl fun u hu => (min_le_left _ _).trans (hf u hu)
  · rcases hg with hg | hg
    · exact Or.inl fun u hu => (min_le_right _ _).trans (hg u hu)
    · exact Or.inr fun u hu => le_min (hf u hu) (hg u hu)

theorem affOn_sum {ι : Type*} {J : Set ℝ} (S : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ S, AffOn (f i) J) : AffOn (fun u => ∑ i ∈ S, f i u) J := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, fun u _ => by simp⟩
  | insert a S ha ih =>
    obtain ⟨a1, b1, h1⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨a2, b2, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨a1 + a2, b1 + b2, fun u hu => by
      simp only [Finset.sum_insert ha]; rw [h1 u hu]; have := h2 u hu; simp only at this; rw [this]; ring⟩

/-! ### Lemma 8.6 -/

section Cell

variable {J : Set ℝ} (hJ : J.OrdConnected) (hJ0 : J ⊆ Ioi 0) (hJB : ∀ u ∈ J, u ∉ Bset)
include hJ hJ0 hJB

theorem affOn_rho (i : Fin 4) : AffOn (fun u => rho u i) J := by
  rcases J.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · exact ⟨0, 0, fun u hu => by simp [hE] at hu⟩
  have hk : ∀ u ∈ J, kk u i = kk u0 i := fun u hu => kk_const hJ hJ0 hJB hu hu0 i
  revert i
  refine fin4_cases ?_ ?_ ?_ ?_ <;> intro hk
  · exact ⟨-1, -(kk u0 0 : ℝ), fun u hu => by simp only [rho, bpt0, hk u hu]; ring⟩
  · exact ⟨2, -(kk u0 1 : ℝ), fun u hu => by simp only [rho, bpt1, hk u hu]; ring⟩
  · exact ⟨0, 1 / 2 - (kk u0 2 : ℝ), fun u hu => by simp only [rho, bpt2, hk u hu]; ring⟩
  · exact ⟨1, 1 / 2 - (kk u0 3 : ℝ), fun u hu => by simp only [rho, bpt3, hk u hu]; ring⟩

/-- The family `{0, u, ρ_0, …, ρ_3}` of gap endpoints. -/
def InFam (f : ℝ → ℝ) : Prop := f = (fun _ => 0) ∨ f = id ∨ ∃ i, f = fun u => rho u i

omit hJ hJ0 hJB in
theorem inFam_lowF (β : Fin 4 → Bool) (i : Fin 4) : InFam (fun u => lowF u β i) := by
  unfold lowF; cases β i
  · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · exact Or.inl rfl

omit hJ hJ0 hJB in
theorem inFam_upF (β : Fin 4 → Bool) (i : Fin 4) : InFam (fun u => upF u β i) := by
  unfold upF; cases β i
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem affOn_fam {f : ℝ → ℝ} (hf : InFam f) : AffOn f J := by
  rcases hf with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨0, 0, fun u _ => by simp⟩
  · exact ⟨0, 1, fun u _ => by simp⟩
  · exact affOn_rho hJ hJ0 hJB i

theorem cmp_fam {f g : ℝ → ℝ} (hf : InFam f) (hg : InFam g) : Cmp J f g := by
  have hne : ∀ f g : ℝ → ℝ, InFam f → InFam g → f ≠ g → ∀ u ∈ J, f u ≠ g u := by
    intro f g hf hg hfg u hu
    have hu0 : 0 < u := hJ0 hu
    rcases hf with rfl | rfl | ⟨i, rfl⟩ <;> rcases hg with rfl | rfl | ⟨j, rfl⟩
    · exact absurd rfl hfg
    · simp only [id]; exact hu0.ne
    · exact (rho_ne_zero hu0 (hJB u hu) j).symm
    · simp only [id]; exact hu0.ne'
    · exact absurd rfl hfg
    · simp only [id]; exact (rho_lt hu0 j).ne'
    · exact rho_ne_zero hu0 (hJB u hu) i
    · simp only [id]; exact (rho_lt hu0 i).ne
    · have hij : i ≠ j := by rintro rfl; exact hfg rfl
      exact rho_ne hu0 (hJB u hu) hij
  by_cases hfg : f = g
  · subst hfg; exact cmp_refl J f
  · exact cmp_of_ne hJ (affOn_fam hJ hJ0 hJB hf) (affOn_fam hJ hJ0 hJB hg) (hne f g hf hg hfg)

theorem affOn_Lbeta (β : Fin 4 → Bool) : AffOn (fun u => Lbeta u β) J := by
  have c := fun i j => cmp_fam hJ hJ0 hJB (inFam_lowF β i) (inFam_lowF β j)
  have a := fun i => affOn_fam hJ hJ0 hJB (inFam_lowF β i)
  unfold Lbeta
  exact affOn_max (affOn_max (affOn_max (a 0) (a 1) (c 0 1)) (a 2) (cmp_max (c 0 2) (c 1 2))) (a 3)
    (cmp_max (cmp_max (c 0 3) (c 1 3)) (c 2 3))

theorem affOn_Rbeta (β : Fin 4 → Bool) : AffOn (fun u => Rbeta u β) J := by
  have c := fun i j => cmp_fam hJ hJ0 hJB (inFam_upF β i) (inFam_upF β j)
  have a := fun i => affOn_fam hJ hJ0 hJB (inFam_upF β i)
  unfold Rbeta
  exact affOn_min (affOn_min (affOn_min (a 0) (a 1) (c 0 1)) (a 2) (cmp_min (c 0 2) (c 1 2))) (a 3)
    (cmp_min (cmp_min (c 0 3) (c 1 3)) (c 2 3))

omit hJ in
theorem Rbeta_ne_Lbeta (β : Fin 4 → Bool) : ∀ u ∈ J, Rbeta u β ≠ Lbeta u β := by
  intro u hu
  have hu0 : 0 < u := hJ0 hu
  have hR : ∃ i, Rbeta u β = upF u β i := by
    unfold Rbeta
    rcases min_choice (min (min (upF u β 0) (upF u β 1)) (upF u β 2)) (upF u β 3) with h | h <;>
      rw [h]
    · rcases min_choice (min (upF u β 0) (upF u β 1)) (upF u β 2) with h' | h' <;> rw [h']
      · rcases min_choice (upF u β 0) (upF u β 1) with h'' | h'' <;> rw [h'']
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hL : ∃ j, Lbeta u β = lowF u β j := by
    unfold Lbeta
    rcases max_choice (max (max (lowF u β 0) (lowF u β 1)) (lowF u β 2)) (lowF u β 3) with h | h <;>
      rw [h]
    · rcases max_choice (max (lowF u β 0) (lowF u β 1)) (lowF u β 2) with h' | h' <;> rw [h']
      · rcases max_choice (lowF u β 0) (lowF u β 1) with h'' | h'' <;> rw [h'']
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j, hj⟩ := hL
  rw [hi, hj]
  unfold upF lowF
  cases hbi : β i <;> cases hbj : β j <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact (rho_lt hu0 j).ne'
  · exact hu0.ne'
  · have hij : i ≠ j := by rintro rfl; rw [hbi] at hbj; exact Bool.noConfusion hbj
    exact rho_ne hu0 (hJB u hu) hij
  · exact rho_ne_zero hu0 (hJB u hu) i

theorem cmp_R_L (β : Fin 4 → Bool) : Cmp J (fun u => Rbeta u β) (fun u => Lbeta u β) :=
  cmp_of_ne hJ (affOn_Rbeta hJ hJ0 hJB β) (affOn_Lbeta hJ hJ0 hJB β) (Rbeta_ne_Lbeta hJ0 hJB β)

theorem affOn_gap (β : Fin 4 → Bool) :
    AffOn (fun u => max (Rbeta u β - Lbeta u β) 0) J := by
  obtain ⟨a, b, hab⟩ := affOn_Rbeta hJ hJ0 hJB β
  obtain ⟨a', b', hab'⟩ := affOn_Lbeta hJ hJ0 hJB β
  rcases cmp_R_L hJ hJ0 hJB β with h | h <;> beta_reduce at hab hab' h
  · exact ⟨0, 0, fun u hu => by beta_reduce; rw [max_eq_right (by linarith [h u hu])]; ring⟩
  · exact ⟨a - a', b - b', fun u hu => by
      beta_reduce; rw [max_eq_left (by linarith [h u hu]), hab u hu, hab' u hu]; ring⟩

/-- **Lemma 8.6 (Cells), affinity.** On every interval `J ⊆ (0, ∞)` containing no point of
`𝓑`, the measure `meas_t(u)` of the set of positions of type `t` is an affine function of `u`. -/
theorem meas_affine_on_cell (t : CType) : AffOn (fun u => meas u t) J := by
  rcases J.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · exact ⟨0, 0, fun u hu => by simp [hE] at hu⟩
  have hk : ∀ u ∈ J, kk u = kk u0 := fun u hu => funext fun i => kk_const hJ hJ0 hJB hu hu0 i
  obtain ⟨a, b, hab⟩ := affOn_sum (J := J) (Finset.univ.filter (fun β => tau (kk u0) β = t))
    (fun β u => max (Rbeta u β - Lbeta u β) 0) fun β _ => affOn_gap hJ hJ0 hJB β
  exact ⟨a, b, fun u hu => by beta_reduce; rw [meas_eq_sum (hJ0 hu), hk u hu]; exact hab u hu⟩

theorem gap_pos_iff (β : Fin 4 → Bool) {u u' : ℝ} (hu : u ∈ J) (hu' : u' ∈ J) :
    0 < max (Rbeta u β - Lbeta u β) 0 ↔ 0 < max (Rbeta u' β - Lbeta u' β) 0 := by
  have hne := Rbeta_ne_Lbeta hJ0 hJB β
  simp only [lt_max_iff, lt_irrefl, or_false, sub_pos]
  rcases cmp_R_L hJ hJ0 hJB β with h | h
  · exact ⟨fun h1 => absurd (h u hu) (not_le.2 h1), fun h1 => absurd (h u' hu') (not_le.2 h1)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (h u' hu') (hne u' hu').symm,
      fun _ => lt_of_le_of_ne (h u hu) (hne u hu).symm⟩

/-- **Lemma 8.6 (Cells), the type set.** On every interval `J ⊆ (0, ∞)` containing no point of
`𝓑`, the set of types of positive measure is the same for all `u ∈ J`. -/
theorem types_const_on_cell {u u' : ℝ} (hu : u ∈ J) (hu' : u' ∈ J) :
    {t : CType | 0 < meas u t} = {t : CType | 0 < meas u' t} := by
  have hk : kk u = kk u' := funext fun i => kk_const hJ hJ0 hJB hu hu' i
  ext t
  simp only [mem_setOf_eq, meas_eq_sum (hJ0 hu), meas_eq_sum (hJ0 hu'), hk]
  rw [Finset.sum_pos_iff_of_nonneg (fun β _ => le_max_right _ _),
    Finset.sum_pos_iff_of_nonneg (fun β _ => le_max_right _ _)]
  exact exists_congr fun β => and_congr_right fun _ => gap_pos_iff hJ hJ0 hJB β hu hu'

end Cell

end Hankel2.Circle
