import RequestProject.TwoAdic.NVStruct

/-!
# II, Lemma 6.1 (consequences): the `ℓ`-adic valuations of `H_k[b] = [u^b] u^q W(−k+u)`

With `ℓ = 2n + 1` (hypotheses `Hyp`):

* `Hk_series`: `u^q W(−k+u) = ∏_j (u + ez_j/2)^q · ∏_{k' ≠ k} (u + k' − k)^{−q}`;
* `Hk_VB_partner`: at every node with `n/2 + 1 ≤ |k|` (affected nodes and partners),
  `v_ℓ(H_k[b]) ≥ −b`: one zero factor is divisible by `ℓ` (`PSW q`) and one pole factor has
  `v = 1` (`PSW (−q)`), all others are units;
* `Hk_VB_small`: at the nodes `|k| ≤ n/2`, `H_k[b]` is `ℓ`-integral;
* `Hk_zero_norm`: at every node with `n/2 + 1 ≤ |k|`, `H_k[0]` is an `ℓ`-adic unit.
-/

open Finset Polynomial PadicWin

namespace TwoAdicWin.Dom

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

variable {q d n ℓ : ℕ}

theorem padicNorm_prod {ℓ : ℕ} [Fact ℓ.Prime] {α : Type*} (s : Finset α) (f : α → ℚ) :
    padicNorm ℓ (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

theorem padicNorm_two_eq_one {ℓ : ℕ} [hp : Fact ℓ.Prime] (h2 : ℓ ≠ 2) : padicNorm ℓ (2 : ℚ) = 1 := by
  have : padicNorm ℓ ((2 : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
  exact_mod_cast this

theorem padicNorm_int_eq_one {ℓ : ℕ} [Fact ℓ.Prime] {z : ℤ} (hz : ¬ (ℓ : ℤ) ∣ z) :
    padicNorm ℓ (z : ℚ) = 1 := by
  rw [padicNorm.int_eq_one_iff]; exact hz

theorem padicNorm_ell {ℓ : ℕ} [hp : Fact ℓ.Prime] : padicNorm ℓ (ℓ : ℚ) = (ℓ : ℚ)⁻¹ :=
  padicNorm.padicNorm_p_of_prime

theorem padicNorm_int_pm {ℓ : ℕ} [Fact ℓ.Prime] {z : ℤ} (hz : z = ℓ ∨ z = -ℓ) :
    padicNorm ℓ (z : ℚ) = (ℓ : ℚ)⁻¹ := by
  rcases hz with rfl | rfl
  · exact_mod_cast padicNorm_ell
  · push_cast; rw [padicNorm.neg]; exact padicNorm_ell

/-- `u^q W(−k+u)` as a product of power series. -/
theorem Hk_series (q n : ℕ) (k : ℤ) :
    ι (taylor (-(k : ℚ)) (numPoly q n)) * PadicWin.PF.Hser (nodes n) q k =
      (∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) *
        ∏ k' ∈ (nodes n).erase k, (PowerSeries.C (((k' - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q := by
  unfold numPoly PadicWin.PF.Hser PadicWin.PF.Ek
  rw [PF.taylor_prod, map_prod, inv_prod_pow]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  have : taylor (-(k : ℚ)) (X - C (zeroPt n j)) = X + C ((ez n j k : ℚ) / 2) := by
    rw [sub_eq_add_neg, ← C_neg, PF.taylor_X_add_C]
    congr 2
    unfold zeroPt ez; push_cast; ring
  rw [taylor_pow, this, map_pow, PF.ι_X_add_C]

/-- Products with one distinguished factor. -/
theorem PSW_prod_one [Fact ℓ.Prime] {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → PowerSeries ℚ) {i₀ : α} (hi₀ : i₀ ∈ s) {c : ℤ} (h0 : PSW ℓ c (f i₀))
    (h : ∀ i ∈ s, i ≠ i₀ → PSInt ℓ (f i)) : PSW ℓ c (∏ i ∈ s, f i) := by
  rw [← mul_prod_erase s f hi₀, mul_comm]
  exact (PSInt.prod _ _ fun i hi => h i (mem_of_mem_erase hi) (ne_of_mem_erase hi)).mul_psw h0

theorem Hk_eq_coeff (q n : ℕ) (k : ℤ) (b : ℕ) :
    Hk q n k b = PowerSeries.coeff b
      ((∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) *
        ∏ k' ∈ (nodes n).erase k, (PowerSeries.C (((k' - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q) := by
  rw [← Hk_series]; rfl

theorem padicNorm_inv' [Fact ℓ.Prime] (x : ℚ) : padicNorm ℓ x⁻¹ = (padicNorm ℓ x)⁻¹ := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]

theorem VB_ez_half [hp : Fact ℓ.Prime] (h2 : ℓ ≠ 2) (n j : ℕ) (k : ℤ) :
    VB ℓ ((ez n j k : ℚ) / 2) 0 := by
  unfold VB
  rw [padicNorm.div, padicNorm_two_eq_one h2, div_one]
  simpa using padicNorm.of_int (p := ℓ) (ez n j k)

theorem VB_ez_half_one [hp : Fact ℓ.Prime] (h2 : ℓ ≠ 2) {n j : ℕ} {k : ℤ}
    (hd : (ℓ : ℤ) ∣ ez n j k) : VB ℓ ((ez n j k : ℚ) / 2) 1 := by
  unfold VB
  rw [padicNorm.div, padicNorm_two_eq_one h2, div_one]
  have := (padicNorm.dvd_iff_norm_le (p := ℓ) (n := 1) (z := ez n j k)).1 (by simpa using hd)
  simpa using this

theorem VB_inv_int [hp : Fact ℓ.Prime] {z : ℤ} (hz : ¬ (ℓ : ℤ) ∣ z) : VB ℓ ((z : ℚ))⁻¹ 0 := by
  unfold VB
  rw [padicNorm_inv', (padicNorm.int_eq_one_iff z).2 hz]
  simp

theorem VB_inv_int_pm [hp : Fact ℓ.Prime] {z : ℤ} (hz : z = ℓ ∨ z = -ℓ) :
    VB ℓ ((z : ℚ))⁻¹ (-1) := by
  unfold VB
  have : padicNorm ℓ (z : ℚ) = (ℓ : ℚ)⁻¹ := by
    rcases hz with rfl | rfl
    · exact_mod_cast padicNorm.padicNorm_p_of_prime
    · push_cast; rw [padicNorm.neg]; exact padicNorm.padicNorm_p_of_prime
  rw [padicNorm_inv', this]
  simp
theorem Hk_VB_partner (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs)
    (b : ℕ) : haveI := Fact.mk h.prime; VB ℓ (Hk q n k b) (-(b : ℤ)) := by
  haveI := Fact.mk h.prime
  have h2 := h.ne_two
  obtain ⟨hmn, hmne, hmd, hmu⟩ := mate_spec h hk hk1
  obtain ⟨js, hjs, hjsv, hjo⟩ := zero_spec h hk hk1
  rw [Hk_eq_coeff]
  have hA : PSW ℓ q (∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) := by
    refine PSW_prod_one _ _ (mem_range.2 hjs) (PSW_C_add_X_pow (VB_ez_half_one h2 ?_) q) ?_
    · rcases hjsv with e | e <;> simp [e]
    · intro j _ _; exact PSInt_C_add_X_pow (VB_ez_half h2 n j k) q
  have hB : PSW ℓ (q * -1) (∏ k' ∈ (nodes n).erase k,
      (PowerSeries.C (((k' - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q) := by
    have hmem : mate ℓ k ∈ (nodes n).erase k := mem_erase.2 ⟨hmne, hmn⟩
    refine PSW_prod_one _ _ hmem ((PSW_inv_C_add_X ?_ ?_).pow q) ?_
    · have : mate ℓ k - k ≠ 0 := sub_ne_zero.2 hmne
      exact_mod_cast this
    · exact VB_inv_int_pm (by omega)
    · intro k' hk' hne
      rw [mem_erase] at hk'
      refine (PSInt_inv_C_add_X ?_ (VB_inv_int fun hd => ?_)).pow q
      · have : k' - k ≠ 0 := sub_ne_zero.2 hk'.1
        exact_mod_cast this
      · rcases hmu k' hk'.2 hd with e | e
        · exact hk'.1 e
        · exact hne e
  have := hA.mul hB
  rw [show (q : ℤ) + q * -1 = 0 by ring] at this
  simpa using this b

/-- **`H_k[b]` is `ℓ`-integral** at the nodes `|k| ≤ n/2`. -/
theorem Hk_VB_small (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : k.natAbs ≤ n / 2)
    (b : ℕ) : haveI := Fact.mk h.prime; VB ℓ (Hk q n k b) 0 := by
  haveI := Fact.mk h.prime
  have h2 := h.ne_two
  rw [Hk_eq_coeff]
  have hA : PSInt ℓ (∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) :=
    PSInt.prod _ _ fun j _ => PSInt_C_add_X_pow (VB_ez_half h2 n j k) q
  have hB : PSInt ℓ (∏ k' ∈ (nodes n).erase k,
      (PowerSeries.C (((k' - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q) := by
    refine PSInt.prod _ _ fun k' hk' => ?_
    rw [mem_erase] at hk'
    refine (PSInt_inv_C_add_X ?_ (VB_inv_int fun hd => hk'.1 ?_)).pow q
    · have : k' - k ≠ 0 := sub_ne_zero.2 hk'.1
      exact_mod_cast this
    · exact small_no_mate h hk hk1 k' hk'.2 hd
  exact hA.mul hB b

/-- **`H_k[0]` is an `ℓ`-adic unit** at the affected nodes and the partners. -/
theorem Hk_zero_norm (h : Hyp q d n ℓ) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs) :
    haveI := Fact.mk h.prime; padicNorm ℓ (Hk q n k 0) = 1 := by
  haveI := Fact.mk h.prime
  have h2 := h.ne_two
  obtain ⟨hmn, hmne, hmd, hmu⟩ := mate_spec h hk hk1
  obtain ⟨js, hjs, hjsv, hjo⟩ := zero_spec h hk hk1
  have hpow : ∀ (x : ℚ) (m : ℕ), padicNorm ℓ (x ^ m) = padicNorm ℓ x ^ m := by
    intro x m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]
  rw [Hk_eq_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_prod, map_prod]
  simp only [map_pow, PowerSeries.constantCoeff_inv, map_add, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero]
  rw [padicNorm.mul, padicNorm_prod, padicNorm_prod]
  simp only [hpow, padicNorm_inv']
  have hez : ∀ j, padicNorm ℓ ((ez n j k : ℚ) / 2) = padicNorm ℓ (ez n j k : ℚ) := by
    intro j; rw [padicNorm.div, padicNorm_two_eq_one h2, div_one]
  simp only [hez]
  rw [← mul_prod_erase _ _ (mem_range.2 hjs),
    ← mul_prod_erase _ _ (mem_erase.2 ⟨hmne, hmn⟩ : mate ℓ k ∈ (nodes n).erase k)]
  rw [prod_eq_one, prod_eq_one]
  · rw [padicNorm_int_pm hjsv, padicNorm_int_pm (z := mate ℓ k - k) (by omega)]
    have : (ℓ : ℚ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
    rw [inv_inv, mul_one, mul_one, ← mul_pow, inv_mul_cancel₀ this, one_pow]
  · intro k' hk'
    have hk'1 := mem_erase.1 hk'
    have hk'2 := mem_erase.1 hk'1.2
    rw [padicNorm_int_eq_one fun hd => ?_]
    · simp
    · rcases hmu k' hk'2.2 hd with e | e
      · exact hk'2.1 e
      · exact hk'1.1 e
  · intro j hj
    have hj1 := mem_erase.1 hj
    rw [padicNorm_int_eq_one (hjo j (mem_range.1 hj1.2) hj1.1)]
    simp

end TwoAdicWin.Dom
