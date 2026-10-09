import RequestProject.Zeta7.Hankel2.PolyProfile

/-!
# The analytic core of II, Theorem 3.1 with `d` derivatives

Generalisation of `Hankel2.exists_hasVolkenborn_iteratedDeriv_three` (three derivatives,
the ζ₂(7) formalization) to any number `d` of derivatives: for a
polynomial `Q` of degree `≤ D` with profile `M` and an admissible `Φ` (a product of powers of
`(u + 2t)^{-1}`, `u` odd), the function `t ↦ (Q Φ)^{(d)}(t + a)` (translated) has a Volkenborn
integral of norm at most `M · D^d · (D + 1)` (`exists_hasVolkenborn_iteratedDeriv`).

The proof keeps the `j`-th derivative as a finite sum `∑ P(u) Ψ(u)` of products of a polynomial of
degree `≤ D` with profile `M D^j` and an admissible function (`termSum`, `GoodList`); one derivative
replaces each term `P Ψ` by `P' Ψ + P Ψ'`.
-/

open Filter Finset Topology Polynomial

namespace TwoAdicWin

open Hankel2

/-- `∑_{(P, Ψ) ∈ l} P(u) Ψ(u)`. -/
noncomputable def termSum (l : List (ℚ_[2][X] × (ℚ_[2] → ℚ_[2]))) (u : ℚ_[2]) : ℚ_[2] :=
  (l.map fun pr => pr.1.eval u * pr.2 u).sum

/-- Every term has a polynomial of degree `≤ D` with profile `M` and an admissible factor. -/
def GoodList (M : ℝ) (D : ℕ) (l : List (ℚ_[2][X] × (ℚ_[2] → ℚ_[2]))) : Prop :=
  ∀ pr ∈ l, pr.1.natDegree ≤ D ∧ Prof (polyW M D) (fun y => pr.1.eval y) ∧ Adm pr.2

theorem termSum_nil (u : ℚ_[2]) : termSum [] u = 0 := rfl

theorem termSum_cons (pr : ℚ_[2][X] × (ℚ_[2] → ℚ_[2])) (l : List (ℚ_[2][X] × (ℚ_[2] → ℚ_[2])))
    (u : ℚ_[2]) : termSum (pr :: l) u = pr.1.eval u * pr.2 u + termSum l u := by
  simp [termSum]

/-- One derivative of a good list. -/
theorem exists_deriv_goodList {M : ℝ} {D : ℕ} (hD : 1 ≤ D) (hM : 0 ≤ M) :
    ∀ l : List (ℚ_[2][X] × (ℚ_[2] → ℚ_[2])), GoodList M D l →
      ∃ l', GoodList (M * D) D l' ∧
        ∀ u ∈ Metric.ball (0 : ℚ_[2]) 2, HasDerivAt (termSum l) (termSum l' u) u := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hMD : M ≤ M * D := le_mul_of_one_le_right hM hD1
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], fun _ h => absurd h (by simp), fun u _ => by
      simpa [termSum] using hasDerivAt_const u (0 : ℚ_[2])⟩
  | cons pr l ih =>
    intro hl
    obtain ⟨hdeg, hprof, hadm⟩ := hl pr (by simp)
    obtain ⟨l', hl', hd'⟩ := ih fun pr' h => hl pr' (by simp [h])
    obtain ⟨Ψ', hΨ', hdΨ⟩ := hadm.hasDerivAt
    refine ⟨(derivative pr.1, pr.2) :: (pr.1, Ψ') :: l', ?_, fun u hu => ?_⟩
    · intro pr' h
      simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact ⟨(natDegree_derivative_le _).trans (by omega), hprof.polyDeriv hdeg hM, hadm⟩
      · exact ⟨hdeg, hprof.mono fun j => polyW_mono hMD D j, hΨ'⟩
      · exact hl' pr' h
    · have h1 := ((pr.1.hasDerivAt u).mul (hdΨ u hu)).add (hd' u hu)
      have e : termSum (pr :: l) = fun u => pr.1.eval u * pr.2 u + termSum l u := by
        funext u; exact termSum_cons _ _ _
      rw [e]
      convert h1 using 1
      simp only [termSum_cons]
      ring

/-- The profile of a good list (times admissible factors). -/
theorem prof_termSum {M : ℝ} {D : ℕ} (hM : 0 ≤ M) :
    ∀ l : List (ℚ_[2][X] × (ℚ_[2] → ℚ_[2])), GoodList M D l →
      Prof (fun j => M * geo (j - D)) (termSum l) := by
  intro l
  induction l with
  | nil =>
    intro _
    have h := Prof.finset_sum (∅ : Finset ℕ) (w := fun j => M * geo (j - D))
      (fun j => mul_nonneg hM (geo_nonneg _)) (f := fun _ => termSum []) (by simp)
    simpa [termSum] using h
  | cons pr l ih =>
    intro hl
    obtain ⟨_, hprof, hadm⟩ := hl pr (by simp)
    have h1 := hprof.polyW_mul_geo hM hadm.prof
    have h2 := ih fun pr' h => hl pr' (by simp [h])
    have e : termSum (pr :: l) = ((fun y => pr.1.eval y) * pr.2) + termSum l := by
      funext u; simp [termSum_cons]
    rw [e]
    exact h1.add h2

/-- **The analytic core of II, Theorem 3.1**: `d` derivatives cost `D^d`, the integral `D + 1`. -/
theorem exists_hasVolkenborn_iteratedDeriv (Q : ℚ_[2][X]) {D : ℕ} (hD : 1 ≤ D)
    (hQ : Q.natDegree ≤ D) {M : ℝ} (hM : 0 ≤ M) (hp : Prof (polyW M D) fun y => Q.eval y)
    {Φ : ℚ_[2] → ℚ_[2]} (hΦ : Adm Φ) (a : ℚ_[2]) (d : ℕ) :
    ∃ I, HasVolkenborn 2
        (fun t => iteratedDeriv d (fun s => Q.eval (s - a) * Φ (s - a)) (t + a)) I ∧
      ‖I‖ ≤ M * (D : ℝ) ^ d * ((D : ℝ) + 1) := by
  set V := Metric.ball (0 : ℚ_[2]) 2
  set U : Set ℚ_[2] := (fun s => s - a) ⁻¹' V
  have hU : IsOpen U := Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  -- the `j`-th derivative is a good list
  have key : ∀ j : ℕ, ∃ l, GoodList (M * (D : ℝ) ^ j) D l ∧
      ∀ s ∈ U, iteratedDeriv j (fun s => Q.eval (s - a) * Φ (s - a)) s = termSum l (s - a) := by
    intro j
    induction j with
    | zero =>
      refine ⟨[(Q, Φ)], ?_, fun s _ => ?_⟩
      · intro pr h
        simp only [List.mem_singleton] at h
        subst h
        exact ⟨hQ, by simpa using hp, hΦ⟩
      · simp [termSum]
    | succ j ih =>
      obtain ⟨l, hl, hit⟩ := ih
      obtain ⟨l', hl', hd'⟩ := exists_deriv_goodList hD (by positivity) l hl
      refine ⟨l', by rwa [pow_succ, ← mul_assoc], fun s hs => ?_⟩
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun s => Q.eval (s - a) * Φ (s - a)) =ᶠ[𝓝 s]
          fun s => termSum l (s - a) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hs) hit
      rw [hev.deriv_eq]
      exact ((hd' (s - a) hs).comp_sub_const s a).deriv
  obtain ⟨l, hl, hit⟩ := key d
  have hMd : 0 ≤ M * (D : ℝ) ^ d := by positivity
  obtain ⟨I, hI, hIn⟩ := exists_hasVolkenborn_of_prof hMd (prof_termSum hMd l hl)
  refine ⟨I, ?_, hIn⟩
  have hint : ∀ t : ℕ, termSum l t =
      iteratedDeriv d (fun s => Q.eval (s - a) * Φ (s - a)) ((t : ℚ_[2]) + a) := by
    intro t
    have hmem : (t : ℚ_[2]) + a ∈ U := by
      show (t : ℚ_[2]) + a - a ∈ V
      rw [add_sub_cancel_right, Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_natCast_le_one _ _) (by norm_num)
    rw [hit _ hmem, add_sub_cancel_right]
  have hvs : volkSum 2 (termSum l) = volkSum 2
      (fun t => iteratedDeriv d (fun s => Q.eval (s - a) * Φ (s - a)) (t + a)) := by
    funext N; simp only [volkSum, hint]
  rwa [HasVolkenborn, ← hvs]

end TwoAdicWin
