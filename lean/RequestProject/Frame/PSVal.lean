import RequestProject.Frame.VB

/-!
# Weighted `ℓ`-adic valuations of power series (II, Lemmas 6.1–6.2)

For a power series `f ∈ ℚ⟦u⟧`:
* `PSInt ℓ f`: all coefficients are `ℓ`-integral;
* `PSW ℓ c f`: `v_ℓ([u^m] f) ≥ c − m` for all `m` (substituting `u = ℓ w` gives an integral series
  times `ℓ^c`).

Products: `PSW c · PSW c' ⊆ PSW (c + c')`, `PSInt · PSW c ⊆ PSW c`, `PSInt · PSInt ⊆ PSInt`.
Factors: `(a + u)^q` is `PSInt` for `ℓ`-integral `a`, and `PSW q` if `ℓ ∣ a`; `(c + u)^{-1}` is `PSInt`
for a unit `c`, and `PSW (−1)` if `v_ℓ(c) = 1` (more precisely if `v_ℓ(c^{-1}) ≥ −1`).
-/

open Finset

namespace PadicWin

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- All coefficients are `ℓ`-integral. -/
def PSInt (ℓ : ℕ) (f : PowerSeries ℚ) : Prop := ∀ m, VB ℓ (PowerSeries.coeff m f) 0

/-- `v_ℓ([u^m] f) ≥ c − m`. -/
def PSW (ℓ : ℕ) (c : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, VB ℓ (PowerSeries.coeff m f) (c - m)

theorem PSInt.psw {f : PowerSeries ℚ} (h : PSInt ℓ f) : PSW ℓ 0 f :=
  fun m => (h m).mono (by omega)

theorem PSW.mono {c c' : ℤ} {f : PowerSeries ℚ} (h : PSW ℓ c f) (hc : c' ≤ c) : PSW ℓ c' f :=
  fun m => (h m).mono (by omega)

theorem PSW.mul {c c' : ℤ} {f g : PowerSeries ℚ} (hf : PSW ℓ c f) (hg : PSW ℓ c' g) :
    PSW ℓ (c + c') (f * g) := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine VB.sum _ _ fun x hx => ((hf x.1).mul (hg x.2)).mono ?_
  rw [mem_antidiagonal] at hx
  have : (x.1 : ℤ) + x.2 = m := by exact_mod_cast hx
  omega

theorem PSInt.mul {f g : PowerSeries ℚ} (hf : PSInt ℓ f) (hg : PSInt ℓ g) : PSInt ℓ (f * g) := by
  intro m
  rw [PowerSeries.coeff_mul]
  exact VB.sum _ _ fun x _ => ((hf x.1).mul (hg x.2)).mono (by omega)

theorem PSInt.mul_psw {c : ℤ} {f g : PowerSeries ℚ} (hf : PSInt ℓ f) (hg : PSW ℓ c g) :
    PSW ℓ c (f * g) := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine VB.sum _ _ fun x hx => ((hf x.1).mul (hg x.2)).mono ?_
  rw [mem_antidiagonal] at hx
  have : (x.1 : ℤ) + x.2 = m := by exact_mod_cast hx
  omega

theorem PSInt_one : PSInt ℓ 1 := by
  intro m
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact VB_one
  · exact VB_zero _

theorem PSInt.pow {f : PowerSeries ℚ} (hf : PSInt ℓ f) (q : ℕ) : PSInt ℓ (f ^ q) := by
  induction q with
  | zero => simpa using (PSInt_one (ℓ := ℓ))
  | succ q ih => rw [pow_succ]; exact ih.mul hf

theorem PSW.pow {c : ℤ} {f : PowerSeries ℚ} (hf : PSW ℓ c f) (q : ℕ) : PSW ℓ (q * c) (f ^ q) := by
  induction q with
  | zero => simpa using (PSInt_one (ℓ := ℓ)).psw
  | succ q ih =>
    rw [pow_succ]
    have := ih.mul hf
    rwa [show ((q + 1 : ℕ) : ℤ) * c = q * c + c by push_cast; ring]

theorem PSInt.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (h : ∀ i ∈ s, PSInt ℓ (f i)) :
    PSInt ℓ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (PSInt_one (ℓ := ℓ))
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-! ### The factors -/

theorem coeff_C_add_X_pow (a : ℚ) (q m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.C a + PowerSeries.X) ^ q) =
      if m ≤ q then (q.choose m : ℚ) * a ^ (q - m) else 0 := by
  rw [add_comm, add_pow, map_sum]
  have : ∀ k ∈ range (q+1), PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℚ) ^ k *
      PowerSeries.C a ^ (q - k) * (q.choose k : PowerSeries ℚ)) =
      if m = k then (q.choose k : ℚ) * a ^ (q - k) else 0 := by
    intro k _
    rw [← map_pow, ← map_natCast (PowerSeries.C (R := ℚ)), mul_assoc, ← map_mul, mul_comm,
      PowerSeries.coeff_C_mul_X_pow]
    split_ifs <;> ring
  rw [sum_congr rfl this, sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

/-- `(a + u)^q` is integral for `ℓ`-integral `a`. -/
theorem PSInt_C_add_X_pow {a : ℚ} (ha : VB ℓ a 0) (q : ℕ) :
    PSInt ℓ ((PowerSeries.C a + PowerSeries.X) ^ q) := by
  intro m
  rw [coeff_C_add_X_pow]
  split_ifs
  · simpa using (VB_natCast (ℓ := ℓ) (q.choose m)).mul (ha.pow (q - m))
  · exact VB_zero _

/-- `(a + u)^q` is `PSW q` if `ℓ ∣ a`. -/
theorem PSW_C_add_X_pow {a : ℚ} (ha : VB ℓ a 1) (q : ℕ) :
    PSW ℓ q ((PowerSeries.C a + PowerSeries.X) ^ q) := by
  intro m
  rw [coeff_C_add_X_pow]
  split_ifs with h
  · refine ((VB_natCast (ℓ := ℓ) (q.choose m)).mul (ha.pow (q - m))).mono ?_
    push_cast [Nat.cast_sub h]; omega
  · exact VB_zero _

/-- `(c + u)^{-1} = ∑_m (−1)^m c^{−m−1} u^m`. -/
theorem inv_C_add_X {c : ℚ} (hc : c ≠ 0) :
    (PowerSeries.C c + PowerSeries.X)⁻¹ = PowerSeries.mk fun m => (-1) ^ m * c⁻¹ ^ (m + 1) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simpa using hc)]
  ext m
  rw [mul_add, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_one]
  rcases m with _ | m
  · simp [PowerSeries.coeff_zero_mul_X, hc]
  · rw [PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]
    have : c * c⁻¹ ^ 2 = c⁻¹ := by field_simp
    simp only [pow_succ] at *
    field_simp
    ring

theorem PSInt_inv_C_add_X {c : ℚ} (hc : c ≠ 0) (hc' : VB ℓ c⁻¹ 0) :
    PSInt ℓ (PowerSeries.C c + PowerSeries.X)⁻¹ := by
  intro m
  rw [inv_C_add_X hc, PowerSeries.coeff_mk]
  have h1 : VB ℓ ((-1 : ℚ) ^ m) 0 := by
    simpa using ((VB_one (ℓ := ℓ)).neg).pow m
  simpa using h1.mul (hc'.pow (m + 1))

theorem PSW_inv_C_add_X {c : ℚ} (hc : c ≠ 0) (hc' : VB ℓ c⁻¹ (-1)) :
    PSW ℓ (-1) (PowerSeries.C c + PowerSeries.X)⁻¹ := by
  intro m
  rw [inv_C_add_X hc, PowerSeries.coeff_mk]
  have h1 : VB ℓ ((-1 : ℚ) ^ m) 0 := by
    simpa using ((VB_one (ℓ := ℓ)).neg).pow m
  refine (h1.mul (hc'.pow (m + 1))).mono ?_
  push_cast; omega

/-- The inverse of a product is the product of the inverses. -/
theorem inv_prod_pow {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (q : ℕ) :
    (∏ i ∈ s, f i ^ q)⁻¹ = ∏ i ∈ s, (f i)⁻¹ ^ q := by
  classical
  have hpow : ∀ (g : PowerSeries ℚ) (q : ℕ), (g ^ q)⁻¹ = g⁻¹ ^ q := by
    intro g q
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, PowerSeries.mul_inv_rev, ih, pow_succ, mul_comm]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, PowerSeries.mul_inv_rev, ih, hpow, mul_comm]

end PadicWin
