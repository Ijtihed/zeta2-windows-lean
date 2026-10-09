import RequestProject.Frame.Knapsack

/-!
# The certificate of II, Prop. 7.1: data format, checker, and soundness

The certificate `certificates/cert_uniform_M96_delta0.4286.json` consists of 119 cells
`[a, b) ⊆ [1/20, 7/2]`.  Each cell carries its class types `t` (data, to be justified by the circle
model in `assembly`): an affine measure `meas_t(u) = m0 + m1·u` and the kept nodes, grouped in runs
`(N − z, hs, multiplicity)`; the weight of a kept node is `α = (N − z) + (1 + δ)·hs`
(II, Lemma 5.3).  Each cell is cut into 96 subcells `[a_i, b_i]` with an exact rational multiplier
`τ_i ≥ 0` and height `h_i`; we add, for each type, a rational dual multiplier `μ` (computed from the
file, see `scripts/gen_cert_two_adic.py`).

**The circle-model integrand** of cell `c` is
`I_c(δ, u) = min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃(α_t(δ), τ))` (`integrandT`), with the continuous
knapsack `ψ̃ = PadicWin.knap`; `cellVal` selects the cell containing `u`.

**The check** (`subOK`, over `ℚ`, by kernel evaluation): `τ ≥ 0`, `h ≥ 0`, `a < b`, and at both ends
`u ∈ {a, b}`: `meas_t(u) ≥ 0` for every type and
`τ + ∑_t meas_t(u) D_t(τ, μ_t) ≤ h`, where `D_t(τ, μ) = ∑_k (α_k(3/7) − τ − μ)⁺ + μ²/4` is the
weak-duality bound of the knapsack at `δ = 3/7`.

**Soundness** (`subOK_sound`): for `0 ≤ δ ≤ 3/7` and `u ∈ [a, b]`, `I_c(δ, u) ≤ h`.  Indeed
`ψ̃(α_t(δ), τ) ≤ D_t(δ)(τ, μ) ≤ D_t(τ, μ)` (weak duality, and monotonicity in `δ`: the weights
`α = (N − z) + (1+δ)hs` increase with `δ` while types and measures do not depend on `δ`), the
measures are non-negative on `[a, b]` and everything is affine in `u`.

**Chains** (`cells_chain_bound`): along a checked chain of cells and subcells,
`∫_a^{b} cellVal ≤ ∑ h_i (b_i − a_i)`.
-/

open Finset MeasureTheory

namespace TwoAdicWin.Cert

open PadicWin

/-- A run of kept nodes `(N − z, hs, multiplicity)`. -/
abbrev RunD := ℚ × Bool × ℕ

/-- A class type: affine measure `m0 + m1 u` on the cell and the runs of kept nodes. -/
structure TypeD where
  m0 : ℚ
  m1 : ℚ
  runs : List RunD

/-- A subcell record `(b, τ, h, [μ_t])`. -/
abbrev SubD := ℚ × ℚ × ℚ × List ℚ

/-- A cell `[a, b)` with its types and its chain of subcells. -/
structure CellD where
  a : ℚ
  b : ℚ
  types : List TypeD
  subs : List SubD

/-- `hs ∈ {0, 1}`. -/
def hsQ (r : RunD) : ℚ := if r.2.1 then 1 else 0

/-! ### The rational checker -/

/-- The dual bound at `δ = 3/7`: `D_t(τ, μ) = ∑_k (α_k − τ − μ)⁺ + μ²/4`, `α = (N − z) + (10/7) hs`. -/
def DQ (t : TypeD) (τ μ : ℚ) : ℚ :=
  (t.runs.map fun r => (r.2.2 : ℚ) * max 0 (r.1 + 10 / 7 * hsQ r - τ - μ)).sum + μ * μ / 4

/-- `meas_t(u) = m0 + m1 u`. -/
def measQ (t : TypeD) (u : ℚ) : ℚ := t.m0 + t.m1 * u

/-- `∑_t meas_t(u) D_t(τ, μ_t)`. -/
def GQ : List TypeD → List ℚ → ℚ → ℚ → ℚ
  | [], _, _, _ => 0
  | t :: ts, mus, τ, u => measQ t u * DQ t τ (mus.headD 0) + GQ ts mus.tail τ u

/-- The check at one end `u` of a subcell. -/
def endOK (ts : List TypeD) (τ h : ℚ) (mus : List ℚ) (u : ℚ) : Bool :=
  ts.all (fun t => decide (0 ≤ measQ t u)) && decide (τ + GQ ts mus τ u ≤ h)

/-- The check of one subcell `[a, b]`. -/
def subOK (ts : List TypeD) (a : ℚ) (r : SubD) : Bool :=
  decide (a < r.1) && decide (0 ≤ r.2.1) && decide (0 ≤ r.2.2.1) &&
    endOK ts r.2.1 r.2.2.1 r.2.2.2 a && endOK ts r.2.1 r.2.2.1 r.2.2.2 r.1

/-- Check of a chain of subcells starting at `a`. -/
def subsOK (ts : List TypeD) : ℚ → List SubD → Bool
  | _, [] => true
  | a, r :: rs => subOK ts a r && subsOK ts r.1 rs

/-- The right end of a chain of subcells. -/
def lastSub : ℚ → List SubD → ℚ
  | a, [] => a
  | _, r :: rs => lastSub r.1 rs

/-- `∑ h (b − a)` over a chain of subcells. -/
def stepSub : ℚ → List SubD → ℚ
  | _, [] => 0
  | a, r :: rs => r.2.2.1 * (r.1 - a) + stepSub r.1 rs

/-- Check of a cell. -/
def cellOK (c : CellD) : Bool := subsOK c.types c.a c.subs && decide (lastSub c.a c.subs = c.b)

/-- Check of a chain of cells starting at `a`. -/
def cellsOK : ℚ → List CellD → Bool
  | _, [] => true
  | a, c :: cs => decide (c.a = a) && cellOK c && cellsOK c.b cs

/-- The right end of a chain of cells. -/
def lastCell : ℚ → List CellD → ℚ
  | a, [] => a
  | _, c :: cs => lastCell c.b cs

/-- The step sum of a chain of cells. -/
def stepCells : ℚ → List CellD → ℚ
  | _, [] => 0
  | _, c :: cs => stepSub c.a c.subs + stepCells c.b cs

/-! ### The real objects -/

/-- The weight `α = (N − z) + (1 + δ) hs` of a run. -/
noncomputable def alphaR (δ : ℝ) (r : RunD) : ℝ := (r.1 : ℝ) + (1 + δ) * (hsQ r : ℝ)

/-- The list of weights of the kept nodes of a type. -/
noncomputable def alphasR (t : TypeD) (δ : ℝ) : List ℝ :=
  t.runs.flatMap fun r => List.replicate r.2.2 (alphaR δ r)

/-- `meas_t(u)` over `ℝ`. -/
noncomputable def measR (t : TypeD) (u : ℝ) : ℝ := (t.m0 : ℝ) + (t.m1 : ℝ) * u

/-- **The circle-model integrand** `min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ))` for a list of types. -/
noncomputable def integrandT (ts : List TypeD) (δ u : ℝ) : ℝ :=
  ⨅ τ : Set.Ici (0 : ℝ), ((τ : ℝ) + (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum)

/-- The integrand on a chain of cells: the first cell with `u < b`. -/
noncomputable def cellVal : List CellD → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, δ, u => if u < (c.b : ℝ) then integrandT c.types δ u else cellVal cs δ u

/-! ### Soundness -/

theorem dualB_alphasR (t : TypeD) (δ τ μ : ℝ) :
    dualB (alphasR t δ) τ μ =
      (t.runs.map fun r => (r.2.2 : ℝ) * max 0 (alphaR δ r - τ - μ)).sum + μ ^ 2 / 4 := by
  unfold dualB alphasR
  congr 1
  induction t.runs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

theorem hsQ_nonneg (r : RunD) : 0 ≤ hsQ r := by unfold hsQ; split_ifs <;> norm_num

theorem DQ_cast (t : TypeD) (τ μ : ℚ) : ((DQ t τ μ : ℚ) : ℝ) =
    (t.runs.map fun r => (r.2.2 : ℝ) * max 0 ((r.1 : ℝ) + 10 / 7 * (hsQ r : ℝ) - τ - μ)).sum +
      (μ : ℝ) ^ 2 / 4 := by
  rw [DQ, Rat.cast_add, Rat.cast_list_sum, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply]
    push_cast
    rfl
  · push_cast; ring

theorem knap_le_DQ (t : TypeD) {δ : ℝ} (hδ : δ ≤ 3 / 7) (τ μ : ℚ) :
    knap (alphasR t δ) τ ≤ (DQ t τ μ : ℝ) := by
  refine (knap_le_dual _ _ μ).trans (le_of_eq_of_le (dualB_alphasR t δ τ μ) ?_)
  rw [DQ_cast]
  gcongr ?_ + _
  refine List.sum_le_sum fun r _ => ?_
  have h0 : (0 : ℝ) ≤ hsQ r := by exact_mod_cast hsQ_nonneg r
  have : alphaR δ r ≤ (r.1 : ℝ) + 10 / 7 * (hsQ r : ℝ) := by
    unfold alphaR; nlinarith
  gcongr

/-- `∑_t meas_t(u) D_t(τ, μ_t)` over `ℝ`. -/
noncomputable def GR : List TypeD → List ℚ → ℚ → ℝ → ℝ
  | [], _, _, _ => 0
  | t :: ts, mus, τ, u => measR t u * (DQ t τ (mus.headD 0) : ℝ) + GR ts mus.tail τ u

theorem GR_cast (ts : List TypeD) (mus : List ℚ) (τ u : ℚ) :
    ((GQ ts mus τ u : ℚ) : ℝ) = GR ts mus τ (u : ℝ) := by
  induction ts generalizing mus with
  | nil => simp [GQ, GR]
  | cons t ts ih => simp [GQ, GR, ih, measQ, measR]

theorem GR_affine (ts : List TypeD) (mus : List ℚ) (τ : ℚ) (u : ℝ) :
    GR ts mus τ u = GR ts mus τ 0 + (GR ts mus τ 1 - GR ts mus τ 0) * u := by
  induction ts generalizing mus with
  | nil => simp [GR]
  | cons t ts ih =>
    simp only [GR]
    rw [ih mus.tail]
    simp only [measR]
    ring

/-- An affine function bounded above at both ends is bounded above in between. -/
theorem affine_le' {f : ℝ → ℝ} (hf : ∀ u, f u = f 0 + (f 1 - f 0) * u) {a b u M : ℝ}
    (ha : a ≤ u) (hb : u ≤ b) (h1 : f a ≤ M) (h2 : f b ≤ M) : f u ≤ M := by
  rw [hf] at h1 h2 ⊢
  rcases le_total 0 (f 1 - f 0) with h | h
  · have := mul_le_mul_of_nonneg_left hb h; linarith
  · have := mul_le_mul_of_nonpos_left ha h; linarith

theorem measR_nonneg_of_ends (t : TypeD) {a b : ℚ} {u : ℝ} (ha : (a : ℝ) ≤ u) (hb : u ≤ b)
    (h1 : 0 ≤ measQ t a) (h2 : 0 ≤ measQ t b) : 0 ≤ measR t u := by
  have := affine_le' (f := fun u => -measR t u) (fun u => by simp only [measR]; ring) ha hb
    (M := 0) (by simp only [measR]; have : ((measQ t a : ℚ) : ℝ) ≥ 0 := by exact_mod_cast h1
                 simp only [measQ] at this; push_cast at this; linarith)
    (by simp only [measR]; have : ((measQ t b : ℚ) : ℝ) ≥ 0 := by exact_mod_cast h2
        simp only [measQ] at this; push_cast at this; linarith)
  simp only at this; linarith

theorem sum_meas_knap_le (ts : List TypeD) (mus : List ℚ) {δ : ℝ} (hδ : δ ≤ 3 / 7) (τ : ℚ)
    (u : ℝ) (hm : ∀ t ∈ ts, 0 ≤ measR t u) :
    (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum ≤ GR ts mus τ u := by
  induction ts generalizing mus with
  | nil => simp [GR]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, GR]
    have h1 := mul_le_mul_of_nonneg_left (knap_le_DQ t hδ τ (mus.headD 0))
      (hm t (by simp))
    have h2 := ih mus.tail (fun t' ht' => hm t' (by simp [ht']))
    linarith

/-- **Soundness of the subcell check**: for `0 ≤ δ ≤ 3/7`, the circle-model integrand is at most
`h` on `[a, b]`. -/
theorem subOK_sound {ts : List TypeD} {a : ℚ} {r : SubD} (h : subOK ts a r = true) {δ : ℝ}
    (hδ : δ ≤ 3 / 7) {u : ℝ} (hu1 : (a : ℝ) ≤ u) (hu2 : u ≤ (r.1 : ℝ)) :
    integrandT ts δ u ≤ (r.2.2.1 : ℝ) := by
  simp only [subOK, endOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hab, hτ⟩, hh⟩, hma, hGa⟩, hmb, hGb⟩ := h
  have hm : ∀ t ∈ ts, 0 ≤ measR t u := fun t ht =>
    measR_nonneg_of_ends t hu1 hu2 (hma t ht) (hmb t ht)
  have hG : (r.2.1 : ℝ) + GR ts r.2.2.2 r.2.1 u ≤ r.2.2.1 := by
    have h1 : GR ts r.2.2.2 r.2.1 a ≤ r.2.2.1 - r.2.1 := by
      rw [← GR_cast]; have := (Rat.cast_le (K := ℝ)).2 hGa; push_cast at this ⊢; linarith
    have h2 : GR ts r.2.2.2 r.2.1 r.1 ≤ r.2.2.1 - r.2.1 := by
      rw [← GR_cast]; have := (Rat.cast_le (K := ℝ)).2 hGb; push_cast at this ⊢; linarith
    have := affine_le' (GR_affine ts r.2.2.2 r.2.1) hu1 hu2 h1 h2
    linarith
  have hval : (r.2.1 : ℝ) + (ts.map fun t => measR t u * knap (alphasR t δ) (r.2.1 : ℝ)).sum ≤
      r.2.2.1 := by
    have := sum_meas_knap_le ts r.2.2.2 hδ r.2.1 u hm
    linarith
  have hτ' : (0 : ℝ) ≤ r.2.1 := by exact_mod_cast hτ
  unfold integrandT
  by_cases hbdd : BddBelow (Set.range fun τ : Set.Ici (0 : ℝ) =>
      ((τ : ℝ) + (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum))
  · exact (ciInf_le hbdd ⟨(r.2.1 : ℝ), hτ'⟩).trans hval
  · rw [Real.iInf_of_not_bddBelow hbdd]; exact_mod_cast hh

/-! ### Chains and the integral -/

theorem lt_of_subOK {ts : List TypeD} {a : ℚ} {r : SubD} (h : subOK ts a r = true) : a < r.1 := by
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem h_nonneg_of_subOK {ts : List TypeD} {a : ℚ} {r : SubD} (h : subOK ts a r = true) :
    0 ≤ r.2.2.1 := by
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem le_lastSub {ts : List TypeD} {a : ℚ} {l : List SubD} (h : subsOK ts a l = true) :
    a ≤ lastSub a l := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons r rs ih =>
    simp only [subsOK, Bool.and_eq_true] at h
    exact (lt_of_subOK h.1).le.trans (ih h.2)

theorem intervalIntegrable_split {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hg : IntervalIntegrable g volume a c) :
    IntervalIntegrable g volume a b ∧ IntervalIntegrable g volume b c := by
  constructor
  · refine hg.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (hab.trans hbc)]
    exact Set.Icc_subset_Icc le_rfl hbc
  · refine hg.mono_set ?_
    rw [Set.uIcc_of_le hbc, Set.uIcc_of_le (hab.trans hbc)]
    exact Set.Icc_subset_Icc hab le_rfl

/-- **The chain bound inside a cell.** -/
theorem sub_chain_bound (ts : List TypeD) {δ : ℝ} (hδ : δ ≤ 3 / 7) :
    ∀ (l : List SubD) (a : ℚ) (g : ℝ → ℝ), subsOK ts a l = true →
      (∀ u ∈ Set.Ioo (a : ℝ) (lastSub a l), g u ≤ integrandT ts δ u) →
      IntervalIntegrable g volume (a : ℝ) (lastSub a l) →
      ∫ u in (a : ℝ)..(lastSub a l), g u ≤ (stepSub a l : ℝ) := by
  intro l
  induction l with
  | nil => intro a g _ _ _; simp [lastSub, stepSub]
  | cons r rs ih =>
    intro a g h hg hint
    simp only [subsOK, Bool.and_eq_true] at h
    simp only [lastSub, stepSub] at hg hint ⊢
    have hab : (a : ℝ) ≤ r.1 := by exact_mod_cast (lt_of_subOK h.1).le
    have hbl : (r.1 : ℝ) ≤ lastSub r.1 rs := by exact_mod_cast le_lastSub h.2
    obtain ⟨hi1, hi2⟩ := intervalIntegrable_split hab hbl hint
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hh := h_nonneg_of_subOK h.1
    have h1 : ∫ u in (a : ℝ)..(r.1 : ℝ), g u ≤ ∫ u in (a : ℝ)..(r.1 : ℝ), (r.2.2.1 : ℝ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hab hi1 intervalIntegrable_const
        fun u hu => ?_
      exact (hg u ⟨hu.1, hu.2.trans_le hbl⟩).trans (subOK_sound h.1 hδ hu.1.le hu.2.le)
    have h2 := ih r.1 g h.2 (fun u hu => hg u ⟨hab.trans_lt hu.1, hu.2⟩) hi2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    push_cast
    linarith

theorem le_lastCell {a : ℚ} {l : List CellD} (h : cellsOK a l = true) : a ≤ lastCell a l := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons c cs ih =>
    simp only [cellsOK, cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca, hsub, hlast⟩, hrest⟩ := h
    have := le_lastSub hsub
    rw [hlast, hca] at this
    exact this.trans (ih hrest)

/-- **The chain bound over cells**: `∫_a^{last} g ≤ ∑ h (b − a)` if `g ≤ cellVal` on the chain. -/
theorem cells_chain_bound {δ : ℝ} (hδ : δ ≤ 3 / 7) :
    ∀ (l : List CellD) (a : ℚ) (g : ℝ → ℝ), cellsOK a l = true →
      (∀ u ∈ Set.Ioo (a : ℝ) (lastCell a l), g u ≤ cellVal l δ u) →
      IntervalIntegrable g volume (a : ℝ) (lastCell a l) →
      ∫ u in (a : ℝ)..(lastCell a l), g u ≤ (stepCells a l : ℝ) := by
  intro l
  induction l with
  | nil => intro a g _ _ _; simp [lastCell, stepCells]
  | cons c cs ih =>
    intro a g h hg hint
    simp only [cellsOK, cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca, hsub, hlast⟩, hrest⟩ := h
    simp only [lastCell, stepCells] at hg hint ⊢
    have hab : (a : ℝ) ≤ c.b := by
      have := le_lastSub hsub; rw [hlast, hca] at this; exact_mod_cast this
    have hbl : (c.b : ℝ) ≤ lastCell c.b cs := by exact_mod_cast le_lastCell hrest
    obtain ⟨hi1, hi2⟩ := intervalIntegrable_split hab hbl hint
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have h1 : ∫ u in (a : ℝ)..(c.b : ℝ), g u ≤ (stepSub c.a c.subs : ℝ) := by
      have e1 : (a : ℝ) = (c.a : ℝ) := by rw [hca]
      have e2 : (c.b : ℝ) = (lastSub c.a c.subs : ℝ) := by rw [hlast]
      rw [e1, e2] at hi1 ⊢
      refine sub_chain_bound c.types hδ c.subs c.a g hsub (fun u hu => ?_) hi1
      have hu' : u ∈ Set.Ioo (a : ℝ) (lastCell c.b cs) := by
        refine ⟨by rw [e1]; exact hu.1, ?_⟩
        have := hu.2; rw [← e2] at this; exact this.trans_le hbl
      have := hg u hu'
      have hlt : u < (c.b : ℝ) := by rw [e2]; exact hu.2
      simp only [cellVal, if_pos hlt] at this
      exact this
    have h2 := ih c.b g hrest (fun u hu => by
      have := hg u ⟨hab.trans_lt hu.1, hu.2⟩
      simp only [cellVal, if_neg (not_lt.2 hu.1.le)] at this
      exact this) hi2
    push_cast
    linarith

/-- **The integral bound**: on a checked chain of cells whose step sum is non-negative,
`∫_a^{last} cellVal ≤ ∑ h (b − a)` (if `cellVal` is not integrable the integral is `0`). -/
theorem integral_cellVal_le {δ : ℝ} (hδ : δ ≤ 3 / 7) {l : List CellD} {a : ℚ}
    (h : cellsOK a l = true) (h0 : 0 ≤ stepCells a l) :
    ∫ u in (a : ℝ)..(lastCell a l), cellVal l δ u ≤ (stepCells a l : ℝ) := by
  by_cases hint : IntervalIntegrable (cellVal l δ) volume (a : ℝ) (lastCell a l)
  · exact cells_chain_bound hδ l a _ h (fun u _ => le_rfl) hint
  · rw [intervalIntegral.integral_undef hint]; exact_mod_cast h0

/-! ### Blocks -/

/-- A block of the certificate: a checked chain of cells, its end, and a bound on its step sum. -/
def Blk (a : ℚ) (l : List CellD) (c S : ℚ) : Prop :=
  cellsOK a l = true ∧ lastCell a l = c ∧ stepCells a l ≤ S

theorem cellsOK_append (a : ℚ) (l₁ l₂ : List CellD) :
    cellsOK a (l₁ ++ l₂) = (cellsOK a l₁ && cellsOK (lastCell a l₁) l₂) := by
  induction l₁ generalizing a with
  | nil => simp [cellsOK, lastCell]
  | cons c cs ih => simp [cellsOK, lastCell, ih, Bool.and_assoc]

theorem lastCell_append (a : ℚ) (l₁ l₂ : List CellD) :
    lastCell a (l₁ ++ l₂) = lastCell (lastCell a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem stepCells_append (a : ℚ) (l₁ l₂ : List CellD) :
    stepCells a (l₁ ++ l₂) = stepCells a l₁ + stepCells (lastCell a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [stepCells, lastCell]
  | cons c cs ih => simp [stepCells, lastCell, ih]; ring

theorem blk_app {a b c S₁ S₂ : ℚ} {l r : List CellD} (hl : Blk a l b S₁) (hr : Blk b r c S₂) :
    Blk a (l ++ r) c (S₁ + S₂) := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h4, h5, h6⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [cellsOK_append, h1, h2, h4]; rfl
  · rw [lastCell_append, h2, h5]
  · rw [stepCells_append, h2]; linarith

end TwoAdicWin.Cert
