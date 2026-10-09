import RequestProject.Zeta7.Hankel2.Volkenborn

/-!
# `d` derivatives of sums of simple fractions on `ℚ_p`

For a finite set `S ⊆ ℤ` of poles, coefficients `c : ℤ → ℕ → ℚ` and `q ≥ 1`, put
`G_j(s) = ∑_{k ∈ S} ∑_{i=1}^{q} c_{k,i} d(i,j) (s + k)^{−(i+j)}` with
`d(i,j) = (−1)^j i(i+1)⋯(i+j−1)` (`dco`).  If `f = G_0` on the open set of non-poles, then
`f^{(j)} = G_j` there (`iteratedDeriv_eq_Gsum`).  This generalises `Hankel2.Fam3.iteratedDeriv_FW`
(`p = 2`, `q = 4`, three derivatives).
-/

open Filter Topology Finset

namespace PadicWin

variable {p : ℕ} [Fact p.Prime]

/-- `d(i, j) = (−1)^j i(i+1)⋯(i+j−1)`, so that `(d/dt)^j (t+k)^{-i} = d(i,j) (t+k)^{-(i+j)}`. -/
def dco (i j : ℕ) : ℚ := (-1) ^ j * ∏ l ∈ range j, ((i : ℚ) + l)

theorem dco_succ (i j : ℕ) : dco i (j + 1) = -((i : ℚ) + j) * dco i j := by
  simp only [dco, pow_succ, Finset.prod_range_succ]; ring

theorem dco_zero (i : ℕ) : dco i 0 = 1 := by simp [dco]

/-- The non-poles `{s : s + k ≠ 0 for all k ∈ S}`. -/
def nonPolesS (p : ℕ) [Fact p.Prime] (S : Finset ℤ) : Set ℚ_[p] := {s | ∀ k ∈ S, s + (k : ℚ_[p]) ≠ 0}

theorem isOpen_nonPolesS (S : Finset ℤ) : IsOpen (nonPolesS p S) := by
  have : nonPolesS p S = ⋂ k ∈ S, {s : ℚ_[p] | s + (k : ℚ_[p]) ≠ 0} := by
    ext s; simp [nonPolesS]
  rw [this]
  exact isOpen_biInter_finset fun k _ =>
    isOpen_ne_fun (continuous_id.add continuous_const) continuous_const

/-- `G_j(s) = ∑_{k ∈ S} ∑_{i=1}^{q} c_{k,i} d(i,j) (s+k)^{−(i+j)}`. -/
noncomputable def Gsum (S : Finset ℤ) (c : ℤ → ℕ → ℚ) (q j : ℕ) (s : ℚ_[p]) : ℚ_[p] :=
  ∑ k ∈ S, ∑ i ∈ Icc 1 q, ((c k i * dco i j : ℚ) : ℚ_[p]) * ((s + k) ^ (i + j))⁻¹

theorem hasDerivAt_inv_pow_add (a s : ℚ_[p]) (hs : s + a ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    HasDerivAt (fun y => ((y + a) ^ m)⁻¹) (-(m : ℚ_[p]) * ((s + a) ^ (m + 1))⁻¹) s := by
  have h1 := (hasDerivAt_pow m (s + a)).comp s ((hasDerivAt_id s).add_const a)
  have h : HasDerivAt (fun y => ((y + a) ^ m)⁻¹)
      (-((m : ℚ_[p]) * (s + a) ^ (m - 1) * 1) / ((s + a) ^ m) ^ 2) s :=
    h1.inv (by simpa [Function.comp] using pow_ne_zero m hs)
  refine h.congr_deriv ?_
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_one]
  field_simp
  ring

theorem hasDerivAt_Gsum (S : Finset ℤ) (c : ℤ → ℕ → ℚ) (q j : ℕ) {s : ℚ_[p]}
    (hs : s ∈ nonPolesS p S) :
    HasDerivAt (Gsum S c q j) (Gsum S c q (j + 1) s) s := by
  unfold Gsum
  refine HasDerivAt.fun_sum fun k hk => HasDerivAt.fun_sum fun i hi => ?_
  obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
  have h := (hasDerivAt_inv_pow_add (k : ℚ_[p]) s (hs k hk) (m := i + j) (by omega)).const_mul
    (((c k i * dco i j : ℚ) : ℚ_[p]))
  convert h using 1
  rw [dco_succ]
  push_cast
  ring_nf

/-- **`d` derivatives of a sum of simple fractions**: if `f = G_0` on the non-poles, then
`f^{(j)} = G_j` on the non-poles. -/
theorem iteratedDeriv_eq_Gsum (S : Finset ℤ) (c : ℤ → ℕ → ℚ) (q : ℕ) (f : ℚ_[p] → ℚ_[p])
    (hf : ∀ s ∈ nonPolesS p S, f s = Gsum S c q 0 s) (j : ℕ) :
    ∀ s ∈ nonPolesS p S, iteratedDeriv j f s = Gsum S c q j s := by
  induction j with
  | zero => intro s hs; rw [iteratedDeriv_zero, hf s hs]
  | succ j ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j f =ᶠ[𝓝 s] Gsum S c q j :=
        Filter.eventuallyEq_of_mem ((isOpen_nonPolesS S).mem_nhds hs) fun y hy => ih y hy
      rw [hev.deriv_eq, (hasDerivAt_Gsum S c q j hs).deriv]

theorem Gsum_zero (S : Finset ℤ) (c : ℤ → ℕ → ℚ) (q : ℕ) (s : ℚ_[p]) :
    Gsum S c q 0 s = ∑ k ∈ S, ∑ i ∈ Icc 1 q, ((c k i : ℚ) : ℚ_[p]) * ((s + k) ^ i)⁻¹ := by
  simp [Gsum, dco_zero]

end PadicWin
