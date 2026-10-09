import RequestProject.Zeta7.Hankel2.HermiteBasis

/-!
# Partial fractions for `∏_{k ∈ S} (t+k)^{-q}`, general exponent `q` (II, Lemma 2.2)

A generalisation of `Zeta35.PF` (`RequestProject/Zeta35/PartialFrac.lean`, exponent `4`) to an
arbitrary exponent `q`.  For a finite set `S ⊆ ℤ` of nodes and `k ∈ S` put

* `E_k(u) = ∏_{k' ∈ S, k' ≠ k} (u + k' − k)^q` (`Ek`), a power series with nonzero constant term;
* `Hser = E_k(u)^{-1}` and `H_k[b] = [u^b] E_k(u)^{-1}` (`Hk`);
* `P_a(k) = [u^a] P(−k + u)` (the Hasse derivative of `P` at `−k`, `Pjet`);
* `r_{k,i}(P) = ∑_{a+b = q−i} P_a(k) H_k[b]` (`resCoef`), the coefficient of `(t+k)^{-i}` in
  `P / ∏_{k'} (t+k')^q`.

Then (`eq_sum`) for `deg P ≤ q|S| − 1`,
`P = ∑_{k ∈ S} ∑_{i=1}^{q} r_{k,i}(P) (t+k)^{q−i} ∏_{k' ≠ k} (t+k')^q`, and
(`sum_resCoef_one_eq_zero`, the residue theorem) for `deg P ≤ q|S| − 2`, `∑_k r_{k,1}(P) = 0`.
-/

open Polynomial

namespace PadicWin.PF

variable (S : Finset ℤ) (q : ℕ)

/-- `E_k(u) = ∏_{k' ≠ k} (u + k' − k)^q`. -/
noncomputable def Ek (k : ℤ) : PowerSeries ℚ :=
  ∏ k' ∈ S.erase k, (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ q

/-- `E_k(u)^{-1}`. -/
noncomputable def Hser (k : ℤ) : PowerSeries ℚ := (Ek S q k)⁻¹

/-- `H_k[b] = [u^b] E_k(u)^{-1}`. -/
noncomputable def Hk (k : ℤ) (b : ℕ) : ℚ := PowerSeries.coeff b (Hser S q k)

/-- `P_a(k) = [u^a] P(−k + u)`. -/
noncomputable def Pjet (P : ℚ[X]) (k : ℤ) (a : ℕ) : ℚ := (hasseDeriv a P).eval (-(k : ℚ))

/-- `r_{k,i}(P) = ∑_{a + b = q − i} P_a(k) H_k[b]`. -/
noncomputable def resCoef (P : ℚ[X]) (k : ℤ) (i : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (q + 1 - i), Pjet P k a * Hk S q k (q - i - a)

/-- `(t+k)^{q−i} ∏_{k' ≠ k} (t+k')^q`. -/
noncomputable def Dki (k : ℤ) (i : ℕ) : ℚ[X] :=
  (X + C (k : ℚ)) ^ (q - i) * ∏ k' ∈ S.erase k, (X + C (k' : ℚ)) ^ q

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

theorem constantCoeff_Ek (k : ℤ) : PowerSeries.constantCoeff (Ek S q k) ≠ 0 := by
  rw [Ek, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k' hk' => ?_
  have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
  simp only [map_pow, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
  exact pow_ne_zero _ (by exact_mod_cast sub_ne_zero.mpr hne)

theorem Hser_mul_Ek (k : ℤ) : Hser S q k * Ek S q k = 1 := by
  rw [Hser, mul_comm]
  exact PowerSeries.mul_inv_cancel _ (constantCoeff_Ek S q k)

theorem ι_X_add_C (a : ℚ) : ι (X + C a) = PowerSeries.C a + PowerSeries.X := by
  rw [map_add, add_comm]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

/-- A truncation identity modulo `u^q`. -/
theorem coeff_mul_eq_sum_trunc (G E : PowerSeries ℚ) {j : ℕ} (hj : j < q) :
    PowerSeries.coeff j (G * E) =
      ∑ i ∈ Finset.Icc 1 q, PowerSeries.coeff (q - i) G *
        PowerSeries.coeff j (PowerSeries.X ^ (q - i) * E) := by
  have h1 : ∑ i ∈ Finset.Icc 1 q, PowerSeries.coeff (q - i) G *
        PowerSeries.coeff j (PowerSeries.X ^ (q - i) * E) =
      ∑ a ∈ Finset.range q, PowerSeries.coeff a G *
        (if a ≤ j then PowerSeries.coeff (j - a) E else 0) := by
    refine Finset.sum_nbij' (fun i => q - i) (fun a => q - a) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc]; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
    · intro a ha; simp only [Finset.mem_range] at ha; dsimp only; omega
    · intro i _
      rw [PowerSeries.coeff_X_pow_mul']
  rw [h1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.range (j + 1)) (s₂ := Finset.range q)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_range] at ha
    rw [if_pos (by omega)]
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a _ ha
    simp only [Finset.mem_range] at ha
    rw [if_neg (by omega), mul_zero]

theorem resCoef_eq_coeff (P : ℚ[X]) (k : ℤ) {i : ℕ} (hiq : i ≤ q) :
    resCoef S q P k i = PowerSeries.coeff (q - i) (ι (taylor (-(k : ℚ)) P) * Hser S q k) := by
  rw [resCoef, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h5 : q + 1 - i = q - i + 1 := by omega
  rw [h5]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, taylor_coeff, Pjet,
    Hk]

theorem taylor_prod {α : Type*} (r : ℚ) (s : Finset α) (f : α → ℚ[X]) :
    taylor r (∏ a ∈ s, f a) = ∏ a ∈ s, taylor r (f a) :=
  map_prod (taylorAlgHom r) f s

theorem taylor_X_add_C (r a : ℚ) : taylor r (X + C a) = X + C (a + r) := by
  simp only [map_add, taylor_X, taylor_C]
  ring

theorem ι_taylor_eq (P : ℚ[X]) (k : ℤ) :
    ι (taylor (-(k : ℚ)) P) = ι (taylor (-(k : ℚ)) P) * Hser S q k * Ek S q k := by
  rw [mul_assoc, Hser_mul_Ek, mul_one]

theorem X_pow_dvd_taylor_Dki {k k' : ℤ} (hk : k ∈ S) (hne : k' ≠ k) (i : ℕ) :
    X ^ q ∣ taylor (-(k : ℚ)) (Dki S q k' i) := by
  rw [Dki, taylor_mul, taylor_prod]
  refine Dvd.dvd.mul_left ?_ _
  have hmem : k ∈ S.erase k' := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hk⟩
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  rw [taylor_pow, taylor_X_add_C]
  simp

theorem ι_taylor_Dki_self (k : ℤ) (i : ℕ) :
    ι (taylor (-(k : ℚ)) (Dki S q k i)) = PowerSeries.X ^ (q - i) * Ek S q k := by
  rw [Dki, taylor_mul, taylor_prod, map_mul, map_prod, taylor_pow, taylor_X_add_C, map_pow, Ek]
  congr 1
  · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  · refine Finset.prod_congr rfl fun k' _ => ?_
    rw [taylor_pow, taylor_X_add_C, map_pow, ι_X_add_C]
    congr 3
    push_cast; ring

/-- The remainder of the partial-fraction expansion. -/
noncomputable def pfRem (P : ℚ[X]) : ℚ[X] :=
  P - ∑ k ∈ S, ∑ i ∈ Finset.Icc 1 q, C (resCoef S q P k i) * Dki S q k i

theorem coeff_eq_ι_coeff (P : ℚ[X]) (j : ℕ) : P.coeff j = PowerSeries.coeff j (ι P) := by
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]

theorem hasse_pfRem_eq_zero (P : ℚ[X]) {k : ℤ} (hk : k ∈ S) {j : ℕ} (hj : j < q) :
    (hasseDeriv j (pfRem S q P)).eval (-(k : ℚ)) = 0 := by
  rw [← taylor_coeff, pfRem, map_sub, map_sum, coeff_sub, finset_sum_coeff,
    Finset.sum_eq_single k]
  · rw [map_sum, finset_sum_coeff, coeff_eq_ι_coeff, ι_taylor_eq S q P k,
      coeff_mul_eq_sum_trunc q _ _ hj, sub_eq_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.mp hi
    rw [taylor_mul, taylor_C, coeff_C_mul, coeff_eq_ι_coeff, ι_taylor_Dki_self,
      resCoef_eq_coeff S q P k hiq]
  · intro k' _ hne
    rw [map_sum, finset_sum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [taylor_mul, taylor_C, coeff_C_mul]
    have := (Polynomial.X_pow_dvd_iff.mp (X_pow_dvd_taylor_Dki S q hk hne i)) j hj
    rw [this, mul_zero]
  · intro h; exact absurd hk h

theorem natDegree_prod_X_add_C_pow_le {α : Type*} (s : Finset α) (a : α → ℚ) (e : ℕ) :
    (∏ x ∈ s, (X + C (a x)) ^ e).natDegree ≤ e * s.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ x ∈ s, ((X + C (a x)) ^ e).natDegree ≤ ∑ _x ∈ s, e := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine natDegree_pow_le.trans ?_
        rw [natDegree_X_add_C, mul_one]
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem natDegree_Dki_le {k : ℤ} (hk : k ∈ S) (i : ℕ) :
    (Dki S q k i).natDegree ≤ (q - i) + q * (S.card - 1) := by
  rw [Dki]
  refine natDegree_mul_le.trans ?_
  have h1 : ((X + C (k : ℚ)) ^ (q - i)).natDegree ≤ q - i := by
    refine natDegree_pow_le.trans ?_; rw [natDegree_X_add_C, mul_one]
  have h2 := natDegree_prod_X_add_C_pow_le (S.erase k) (fun k' => (k' : ℚ)) q
  rw [Finset.card_erase_of_mem hk] at h2
  omega

theorem mul_card_sub_one_add {c : ℕ} (hc : 1 ≤ c) : q * (c - 1) + q = q * c := by
  rw [← Nat.mul_succ]; congr 1; omega

theorem natDegree_pfRem_le (P : ℚ[X]) (hS : S.Nonempty) (hP : P.natDegree + 1 ≤ q * S.card) :
    (pfRem S q P).natDegree + 1 ≤ q * S.card := by
  have hc : 1 ≤ S.card := Finset.card_pos.mpr hS
  have : (pfRem S q P).natDegree ≤ q * S.card - 1 := by
    rw [pfRem]
    refine (natDegree_sub_le _ _).trans (max_le (by omega) ?_)
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    have h1 := natDegree_Dki_le S q hk i
    obtain ⟨h2, h2'⟩ := Finset.mem_Icc.mp hi
    have h3 := mul_card_sub_one_add q hc
    generalize q * S.card = Y at *
    generalize q * (S.card - 1) = Z at *
    omega
  omega

/-- **The partial-fraction identity**: for `deg P ≤ q|S| − 1`,
`P = ∑_{k ∈ S} ∑_{i=1}^{q} r_{k,i}(P) (t+k)^{q−i} ∏_{k' ≠ k} (t+k')^q`. -/
theorem eq_sum (P : ℚ[X]) (hP : P.natDegree + 1 ≤ q * S.card) :
    P = ∑ k ∈ S, ∑ i ∈ Finset.Icc 1 q, C (resCoef S q P k i) * Dki S q k i := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp at hP
  rw [← sub_eq_zero]
  change pfRem S q P = 0
  have hinj : Function.Injective (fun k : S => -((k : ℤ) : ℚ)) := by
    intro a b h
    simp only [neg_inj, Int.cast_inj] at h
    exact Subtype.ext h
  refine Hankel2.eq_zero_of_hermite_conditions (fun k : S => -((k : ℤ) : ℚ)) hinj (fun _ => q)
    (pfRem S q P) ?_ ?_
  · have hsum : (∑ _i : S, q : ℕ) = q * S.card := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]; ring
    rw [hsum]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    have := natDegree_pfRem_le S q P hS hP
    exact_mod_cast (show (pfRem S q P).natDegree < q * S.card by omega)
  · intro k j hj
    exact hasse_pfRem_eq_zero S q P k.2 hj

theorem Dki_one_monic (k : ℤ) : (Dki S q k 1).Monic := by
  rw [Dki]
  refine ((monic_X_add_C _).pow _).mul (monic_prod_of_monic _ _ fun k' _ => ?_)
  exact (monic_X_add_C _).pow _

theorem natDegree_Dki_one {k : ℤ} (hk : k ∈ S) (hq : 1 ≤ q) :
    (Dki S q k 1).natDegree = q * S.card - 1 := by
  have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨k, hk⟩
  rw [Dki, Monic.natDegree_mul ((monic_X_add_C _).pow _)
    (monic_prod_of_monic _ _ fun k' _ => (monic_X_add_C _).pow _),
    natDegree_prod_of_monic _ _ fun k' _ => (monic_X_add_C _).pow _]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_erase_of_mem hk]
  have h3 := mul_card_sub_one_add q hc
  rw [mul_comm (S.card - 1) q]
  omega

/-- **The residue theorem**: for `deg P ≤ q|S| − 2`, `∑_k r_{k,1}(P) = 0`. -/
theorem sum_resCoef_one_eq_zero (P : ℚ[X]) (hP : P.natDegree + 2 ≤ q * S.card) :
    ∑ k ∈ S, resCoef S q P k 1 = 0 := by
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hP
    · exact h
  have h := congrArg (fun Q : ℚ[X] => Q.coeff (q * S.card - 1)) (eq_sum S q P (by omega))
  simp only [finset_sum_coeff, coeff_C_mul] at h
  have hl : P.coeff (q * S.card - 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hl] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hI : Finset.Icc 1 q = insert 1 (Finset.Icc 2 q) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp)]
  have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨k, hk⟩
  have h1 : (Dki S q k 1).coeff (q * S.card - 1) = 1 := by
    have := (Dki_one_monic S q k).coeff_natDegree
    rwa [natDegree_Dki_one S q hk hq] at this
  have h0 : ∀ i ∈ Finset.Icc 2 q, (Dki S q k i).coeff (q * S.card - 1) = 0 := by
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    have h5 := natDegree_Dki_le S q hk i
    obtain ⟨h6, h6'⟩ := Finset.mem_Icc.mp hi
    have h3 := mul_card_sub_one_add q hc
    generalize q * S.card = Y at *
    generalize q * (S.card - 1) = Z at *
    omega
  rw [h1, mul_one, Finset.sum_eq_zero fun i hi => by rw [h0 i hi, mul_zero], add_zero]

end PadicWin.PF
