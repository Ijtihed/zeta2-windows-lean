import RequestProject.TwoAdic.AsmKnap
import RequestProject.TwoAdic.CertCheck

/-!
# Regularity of the circle-model integrand

For a list of types `ts` whose measures are `≥ 0` on `[a, b]`, the integrand
`g(u) = inf_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ))` (`integrandT`) is `≥ 0`, it is bounded by every
`τ + ∑_t meas_t(u) ψ̃_t(τ)` and bounded below by every common lower bound of these, and it is
`L`-Lipschitz on `[a, b]` with `L = ∑_t |m1_t| ψ̃_t(0)` (`integrandT_lipschitz`), hence interval
integrable there (`integrandT_intervalIntegrable`).
-/

open Finset MeasureTheory

namespace TwoAdicWin.Asm

open PadicWin Cert

/-- `τ + ∑_t meas_t(u) ψ̃_t(τ)`. -/
noncomputable def fTau (ts : List TypeD) (δ u τ : ℝ) : ℝ :=
  τ + (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum

/-- The Lipschitz constant `∑_t |m1_t| ψ̃_t(0)`. -/
noncomputable def Lc (ts : List TypeD) (δ : ℝ) : ℝ :=
  (ts.map fun t => |(t.m1 : ℝ)| * knap (alphasR t δ) 0).sum

theorem Lc_nonneg (ts : List TypeD) (δ : ℝ) : 0 ≤ Lc ts δ := by
  unfold Lc
  refine List.sum_nonneg ?_
  simp only [List.mem_map]
  rintro x ⟨t, _, rfl⟩
  exact mul_nonneg (abs_nonneg _) (knap_nonneg _ _)

theorem sum_meas_nonneg (ts : List TypeD) (δ u τ : ℝ) (h : ∀ t ∈ ts, 0 ≤ measR t u) :
    0 ≤ (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum := by
  refine List.sum_nonneg ?_
  simp only [List.mem_map]
  rintro x ⟨t, ht, rfl⟩
  exact mul_nonneg (h t ht) (knap_nonneg _ _)

theorem list_lip (δ τ u v : ℝ) (hτ : 0 ≤ τ) : ∀ ts : List TypeD,
    (ts.map fun t => measR t u * knap (alphasR t δ) τ).sum ≤
      (ts.map fun t => measR t v * knap (alphasR t δ) τ).sum + Lc ts δ * |u - v|
  | [] => by simp [Lc]
  | t :: ts => by
    have ih := list_lip δ τ u v hτ ts
    simp only [Lc, List.map_cons, List.sum_cons] at ih ⊢
    have hk0 := knap_nonneg (alphasR t δ) τ
    have hk1 := knap_anti (alphasR t δ) hτ
    have e : measR t u * knap (alphasR t δ) τ - measR t v * knap (alphasR t δ) τ =
        (t.m1 : ℝ) * (u - v) * knap (alphasR t δ) τ := by unfold measR; ring
    have h1 : (t.m1 : ℝ) * (u - v) * knap (alphasR t δ) τ ≤
        |(t.m1 : ℝ)| * knap (alphasR t δ) 0 * |u - v| := by
      calc (t.m1 : ℝ) * (u - v) * knap (alphasR t δ) τ
          ≤ |(t.m1 : ℝ) * (u - v)| * knap (alphasR t δ) τ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hk0
        _ = |(t.m1 : ℝ)| * |u - v| * knap (alphasR t δ) τ := by rw [abs_mul]
        _ ≤ |(t.m1 : ℝ)| * |u - v| * knap (alphasR t δ) 0 :=
            mul_le_mul_of_nonneg_left hk1 (by positivity)
        _ = |(t.m1 : ℝ)| * knap (alphasR t δ) 0 * |u - v| := by ring
    nlinarith

theorem bddBelow_fTau (ts : List TypeD) (δ u : ℝ) (h : ∀ t ∈ ts, 0 ≤ measR t u) :
    BddBelow (Set.range fun τ : Set.Ici (0 : ℝ) => fTau ts δ u τ) := by
  refine ⟨0, ?_⟩
  rintro x ⟨τ, rfl⟩
  have := sum_meas_nonneg ts δ u τ h
  have h0 : (0 : ℝ) ≤ τ := τ.2
  unfold fTau; linarith

theorem integrandT_eq (ts : List TypeD) (δ u : ℝ) :
    integrandT ts δ u = ⨅ τ : Set.Ici (0 : ℝ), fTau ts δ u τ := rfl

theorem integrandT_le (ts : List TypeD) (δ u : ℝ) (h : ∀ t ∈ ts, 0 ≤ measR t u) {τ : ℝ}
    (hτ : 0 ≤ τ) : integrandT ts δ u ≤ fTau ts δ u τ := by
  rw [integrandT_eq]
  exact ciInf_le (bddBelow_fTau ts δ u h) ⟨τ, hτ⟩

theorem le_integrandT (ts : List TypeD) (δ u : ℝ) {x : ℝ} (h : ∀ τ : ℝ, 0 ≤ τ → x ≤ fTau ts δ u τ) :
    x ≤ integrandT ts δ u := by
  rw [integrandT_eq]
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  exact le_ciInf fun τ => h τ τ.2

theorem integrandT_nonneg (ts : List TypeD) (δ u : ℝ) (h : ∀ t ∈ ts, 0 ≤ measR t u) :
    0 ≤ integrandT ts δ u :=
  le_integrandT ts δ u fun τ hτ => by
    have := sum_meas_nonneg ts δ u τ h
    unfold fTau; linarith

theorem integrandT_lip_le (ts : List TypeD) (δ u v : ℝ) (hu : ∀ t ∈ ts, 0 ≤ measR t u) :
    integrandT ts δ u ≤ integrandT ts δ v + Lc ts δ * |u - v| := by
  have : integrandT ts δ u - Lc ts δ * |u - v| ≤ integrandT ts δ v :=
    le_integrandT ts δ v fun τ hτ => by
      have h1 := integrandT_le ts δ u hu hτ
      have h2 := list_lip δ τ u v hτ ts
      unfold fTau at h1 ⊢
      linarith
  linarith

/-- **The integrand is Lipschitz** where the measures are nonnegative. -/
theorem integrandT_lipschitz (ts : List TypeD) (δ u v : ℝ) (hu : ∀ t ∈ ts, 0 ≤ measR t u)
    (hv : ∀ t ∈ ts, 0 ≤ measR t v) :
    |integrandT ts δ u - integrandT ts δ v| ≤ Lc ts δ * |u - v| := by
  have h1 := integrandT_lip_le ts δ u v hu
  have h2 := integrandT_lip_le ts δ v u hv
  rw [abs_sub_comm v u] at h2
  rw [abs_le]; constructor <;> linarith

theorem integrandT_continuousOn (ts : List TypeD) (δ : ℝ) {s : Set ℝ}
    (h : ∀ t ∈ ts, ∀ u ∈ s, 0 ≤ measR t u) : ContinuousOn (integrandT ts δ) s := by
  have hL : LipschitzOnWith ⟨Lc ts δ, Lc_nonneg ts δ⟩ (integrandT ts δ) s := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [Real.dist_eq, Real.dist_eq]
    exact integrandT_lipschitz ts δ u v (fun t ht => h t ht u hu) (fun t ht => h t ht v hv)
  exact hL.continuousOn

theorem integrandT_intervalIntegrable (ts : List TypeD) (δ : ℝ) {a b : ℝ}
    (h : ∀ t ∈ ts, ∀ u ∈ Set.uIcc a b, 0 ≤ measR t u) :
    IntervalIntegrable (integrandT ts δ) volume a b :=
  (integrandT_continuousOn ts δ h).intervalIntegrable

end TwoAdicWin.Asm
