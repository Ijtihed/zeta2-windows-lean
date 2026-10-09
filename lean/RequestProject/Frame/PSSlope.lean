import RequestProject.Frame.PSVal

/-!
# Power series with a valuation slope

`PSL ℓ c L f`: `v_ℓ([u^m] f) ≥ c − m L` for all `m`.  (`PSW ℓ c = PSL ℓ c 1`.)

* products add the constants (`PSL.mul`, `PSL.prod`);
* `(a + u)^q` with `v(a) ≥ e`, `e ≤ L`: `PSL (q e) L` (`PSL_C_add_X_pow`);
* `(c + u)^{−1}` with `v(c^{−1}) ≥ −f`, `f ≤ L`: `PSL (−f) L` (`PSL_inv_C_add_X`).

The coefficient of `u^b` in `(1 − u/ρ)^e` is an integer times `ρ^{−b}`, and
`v(ρ) ≤ L`.
-/

open Finset

namespace PadicWin

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `v_ℓ([u^m] f) ≥ c − m L`. -/
def PSL (ℓ : ℕ) (c L : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, VB ℓ (PowerSeries.coeff m f) (c - m * L)

theorem PSL.mono {c c' L : ℤ} {f : PowerSeries ℚ} (h : PSL ℓ c L f) (hc : c' ≤ c) : PSL ℓ c' L f :=
  fun m => (h m).mono (by omega)

theorem PSL.mul {c c' L : ℤ} {f g : PowerSeries ℚ} (hf : PSL ℓ c L f) (hg : PSL ℓ c' L g) :
    PSL ℓ (c + c') L (f * g) := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine VB.sum _ _ fun x hx => ((hf x.1).mul (hg x.2)).mono ?_
  rw [mem_antidiagonal] at hx
  have : (x.1 : ℤ) + x.2 = m := by exact_mod_cast hx
  have : ((x.1 : ℤ) + x.2) * L = m * L := by rw [this]
  linarith

theorem PSL_one (L : ℤ) : PSL ℓ 0 L 1 := by
  intro m
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simpa using (VB_one (ℓ := ℓ))
  · exact VB_zero _

theorem PSL.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (c : ι → ℤ) {L : ℤ}
    (h : ∀ i ∈ s, PSL ℓ (c i) L (f i)) :
    PSL ℓ (∑ i ∈ s, c i) L (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSL_one (ℓ := ℓ) L
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem PSL.pow {c L : ℤ} {f : PowerSeries ℚ} (hf : PSL ℓ c L f) (q : ℕ) :
    PSL ℓ (q * c) L (f ^ q) := by
  induction q with
  | zero => simpa using PSL_one (ℓ := ℓ) L
  | succ q ih =>
    rw [pow_succ]
    have := ih.mul hf
    rwa [show ((q + 1 : ℕ) : ℤ) * c = q * c + c by push_cast; ring]

/-- `(a + u)^q` with `v(a) ≥ e` and `e ≤ L`. -/
theorem PSL_C_add_X_pow {a : ℚ} {e L : ℤ} (ha : VB ℓ a e) (heL : e ≤ L) (q : ℕ) :
    PSL ℓ (q * e) L ((PowerSeries.C a + PowerSeries.X) ^ q) := by
  intro m
  rw [coeff_C_add_X_pow]
  split_ifs with h
  · refine ((VB_natCast (ℓ := ℓ) (q.choose m)).mul (ha.pow (q - m))).mono ?_
    push_cast [Nat.cast_sub h]
    have : (0 : ℤ) ≤ m * (L - e) := mul_nonneg (by positivity) (by omega)
    nlinarith
  · exact VB_zero _

/-- `(c + u)^{−1}` with `v(c^{−1}) ≥ −f` and `f ≤ L`. -/
theorem PSL_inv_C_add_X {c : ℚ} (hc : c ≠ 0) {f L : ℤ} (hc' : VB ℓ c⁻¹ (-f)) (hfL : f ≤ L) :
    PSL ℓ (-f) L (PowerSeries.C c + PowerSeries.X)⁻¹ := by
  intro m
  rw [inv_C_add_X hc, PowerSeries.coeff_mk]
  have h1 : VB ℓ ((-1 : ℚ) ^ m) 0 := by
    simpa using ((VB_one (ℓ := ℓ)).neg).pow m
  refine (h1.mul (hc'.pow (m + 1))).mono ?_
  push_cast
  have : (0 : ℤ) ≤ m * (L - f) := mul_nonneg (by positivity) (by omega)
  nlinarith

end PadicWin
