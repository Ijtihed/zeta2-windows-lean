import RequestProject.TwoAdic.CertAll
import RequestProject.TwoAdic.InputDefs
import RequestProject.Zeta7.Hankel2.EulerGamma
import RequestProject.Zeta7.Hankel2.CertBound

/-!
# II, Prop. 7.1: `C̃(δ) ≤ 4.3892` for `0 ≤ δ ≤ 3/7` (fields `circ` and `certificate`)

`circCert δ = ∫_{1/20}^{7/2} min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ)) du` is the circle-model integral
of II, Cor. 5.4, with the class types and measures of the certificate file (data; they are to be
justified by the circle model in the field `assembly`), the weights `α = (N − z) + (1 + δ) hs` and the
continuous knapsack `ψ̃ = PadicWin.knap`.

* `circCert_le`: for `δ ≤ 3/7`, `circCert δ ≤ stepBound ≈ 7.2355265721204` (the kernel-checked step
  sum of the certificate, `Cert.certCells_blk`), by the soundness of the checker
  (`Cert.integral_cellVal_le`); monotonicity in `δ` is built into the check.
* **`certificate_field`**: field (iii-c) `certificate` of `TwoAdicInputsOpen`, verbatim, with
  `circ = circCert`, using `γ ≥ 0.5772` (`Hankel2.EulerGamma.eulerMascheroni_bounds`), `ln 20 > 2.9957`
  (`Hankel2.CertC.log_twenty_gt`) and `ln 2 > 0.6931471803` (Mathlib).
-/

namespace TwoAdicWin

open Cert

/-- **The circle-model integral of II, Cor. 5.4**, with the class types and measures of the
certificate `certificates/cert_uniform_M96_delta0.4286.json` (119 cells covering `[1/20, 7/2]`):
`I(δ) = ∫_{1/20}^{7/2} min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ)) du`. -/
noncomputable def circCert (δ : ℝ) : ℝ :=
  ∫ u in (1 / 20 : ℝ)..(7 / 2), cellVal certCells δ u

theorem stepBound_nonneg : (0 : ℚ) ≤ stepBound := by unfold stepBound; norm_num

theorem stepSub_nonneg (ts : List TypeD) :
    ∀ (l : List SubD) (a : ℚ), subsOK ts a l = true → 0 ≤ stepSub a l
  | [], _, _ => by simp [stepSub]
  | r :: rs, a, h => by
    simp only [subsOK, Bool.and_eq_true] at h
    simp only [stepSub]
    have h1 := h_nonneg_of_subOK h.1
    have h2 := lt_of_subOK h.1
    have h3 := stepSub_nonneg ts rs _ h.2
    have : 0 ≤ r.2.2.1 * (r.1 - a) := mul_nonneg h1 (by linarith)
    linarith

theorem stepCells_nonneg : ∀ (l : List CellD) (a : ℚ), cellsOK a l = true → 0 ≤ stepCells a l
  | [], _, _ => by simp [stepCells]
  | c :: cs, a, h => by
    simp only [cellsOK, cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [stepCells]
    have := stepSub_nonneg c.types c.subs c.a h.1.2.1
    have := stepCells_nonneg cs c.b h.2
    linarith

/-- `I(δ) ≤ ∑ h (b − a) ≤ stepBound` for `δ ≤ 3/7`. -/
theorem circCert_le {δ : ℝ} (hδ : δ ≤ 3 / 7) : circCert δ ≤ (stepBound : ℝ) := by
  obtain ⟨hok, hlast, hstep⟩ := certCells_blk
  have h0 : (0 : ℚ) ≤ stepCells (1 / 20) certCells := stepCells_nonneg _ _ hok
  have key := integral_cellVal_le hδ hok h0
  rw [hlast] at key
  have e1 : ((1 / 20 : ℚ) : ℝ) = 1 / 20 := by norm_num
  have e2 : ((7 / 2 : ℚ) : ℝ) = 7 / 2 := by norm_num
  rw [e1, e2] at key
  unfold circCert
  exact key.trans (by exact_mod_cast hstep)

/-- **Field (iii-c) `certificate` of `TwoAdicInputsOpen`, discharged** (II, Prop. 7.1, relaxed from
`4.388838` to `4.3892`), with `circ = circCert`. -/
theorem certificate_field : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 3 / 7 → Ctil mertensOddConst circCert δ ≤ 4.3892 := by
  intro δ hδ0 hδ
  have hc := circCert_le hδ
  have hS : (stepBound : ℝ) ≤ 7.2355265722 := by unfold stepBound; norm_num
  have hγ := (Hankel2.EulerGamma.eulerMascheroni_bounds).1
  have h20 := Hankel2.CertC.log_twenty_gt
  have h2 := Real.log_two_gt_d9
  have hl2 : 0 < Real.log 2 := by linarith
  unfold Ctil mertensOddConst epsC
  rw [div_le_iff₀ hl2]
  nlinarith

end TwoAdicWin
