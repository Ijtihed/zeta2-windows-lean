import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# Theorem A from its analytic entry bound (paper §4)

`Hankel2.Lemma42` is the statement of paper Lemma 4.3 (v4.1 numbering; the analytic step of
Theorem 4.1 = Theorem A; Lemma 4.2 of v4.1 is the Bhargava/algebraic step): for odd
`n`, `K ≤ 3n+1` and every integer-valued polynomial `B(τ)` of degree `≤ 2K−2`,
`v₂ L(B) ≥ A₃ − 3 log₂ D − log₂(D+1)`, where `τ = x − (n+1)/2` (so `L(B)` is `L` applied to the
`x`-polynomial `B(x − (n+1)/2)`).

* `Hankel2.thmA_norm_le` — **Theorem A** (algebraic half = paper Lemma 4.2, + Lemma 4.3):
  `‖Δ_K(ζ₂(7))‖₂ ≤ (2^{−(A₃ − 3log₂D − log₂(D+1))})^K ∏_{i<K} ‖i!‖₂²`, i.e.
  `v₂ Δ_K(ζ₂(7)) ≥ 2∑_{i<K} v₂(i!) + K(A₃ − 3log₂D − log₂(D+1))`.
* `Hankel2.thmA_logb_le` — the explicit asymptotic form:
  `log₂ ‖Δ_K(ζ₂(7))‖₂ ≤ −(K² + 18nK) + 100 n (1 + log₂ n)` for `1 ≤ n`, `K ≤ 3n+1`
  (so `v₂ Δ_K(ζ₂(7)) ≥ (κ² + 18κ) n² − O(n log n)`).
-/

open Polynomial Finset

namespace Hankel2

open Fam3

/-- **Paper Lemma 4.3** (v4.1 numbering; the analytic step of Theorem 4.1), as a statement.
The name `Lemma42` is kept from round 1.  It is proved for `K ≥ 1` (the only case covered by the
paper) in the ζ₂(7) formalization. -/
def Lemma42 : Prop :=
  ∀ n K : ℕ, n % 2 = 1 → K ≤ 3 * n + 1 → ∀ B : ℚ[X], IntValued B → B.natDegree ≤ 2 * K - 2 →
    ‖Fam3.famL n (B.comp (X - C (((n : ℚ) + 1) / 2)))‖ ≤ (2 : ℝ) ^ (-entryBound n K)

section ThmAAux

/-- The binomial polynomial `C_i = x(x−1)⋯(x−i+1)/i!` over `ℚ`. -/
noncomputable def binomQ (i : ℕ) : ℚ[X] := C ((i.factorial : ℚ)⁻¹) * descPochhammer ℚ i

theorem binomPoly_eq_map (i : ℕ) : binomPoly 2 i = (binomQ i).map (algebraMap ℚ ℚ_[2]) := by
  simp [binomPoly, binomQ, Polynomial.map_mul, descPochhammer_map]

theorem natDegree_binomQ (i : ℕ) : (binomQ i).natDegree = i := by
  unfold binomQ
  rw [natDegree_C_mul (inv_ne_zero (by exact_mod_cast (Nat.factorial_pos i).ne')),
    descPochhammer_natDegree]

theorem factorial_dvd_descPochhammer_eval (i : ℕ) (z : ℤ) :
    (i.factorial : ℤ) ∣ (descPochhammer ℤ i).eval z := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose z i
  have e : (descPochhammer ℤ i).smeval z = (descPochhammer ℤ i).eval z := by
    rw [← eval₂_smulOneHom_eq_smeval, Subsingleton.elim (RingHom.smulOneHom : ℤ →+* ℤ)
      (RingHom.id ℤ)]; rfl
  rw [e] at h
  rw [h, nsmul_eq_mul]
  exact dvd_mul_right _ _

theorem intValued_binomQ (i : ℕ) : IntValued (binomQ i) := by
  intro z
  obtain ⟨m, hm⟩ := factorial_dvd_descPochhammer_eval i z
  refine ⟨m, ?_⟩
  rw [binomQ, eval_mul, eval_C, ← descPochhammer_eval_cast, hm]
  have : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  push_cast
  field_simp

theorem IntValued.mul {A B : ℚ[X]} (hA : IntValued A) (hB : IntValued B) : IntValued (A * B) := by
  intro z
  obtain ⟨a, ha⟩ := hA z
  obtain ⟨b, hb⟩ := hB z
  exact ⟨a * b, by rw [eval_mul, ha, hb]; push_cast; ring⟩

theorem aL_add (n : ℕ) (P Q : ℚ[X]) : aL n (P + Q) = aL n P + aL n Q := by
  simp only [aL, Pjet, map_add, eval_add, mul_add, Finset.sum_add_distrib]

theorem bL_add (n : ℕ) (P Q : ℚ[X]) : bL n (P + Q) = bL n P + bL n Q := by
  simp only [bL, Pjet, map_add, eval_add, mul_add, Finset.sum_add_distrib]

theorem aL_smul (n : ℕ) (a : ℚ) (P : ℚ[X]) : aL n (a • P) = a * aL n P := by
  simp only [aL, Pjet, map_smul, eval_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bL_smul (n : ℕ) (a : ℚ) (P : ℚ[X]) : bL n (a • P) = a * bL n P := by
  simp only [bL, Pjet, map_smul, eval_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The shift `τ = x − (n+1)/2`. -/
noncomputable def cShift (n : ℕ) : ℚ := ((n : ℚ) + 1) / 2

/-- The functional in the variable `τ`, `M(G) = a(G(x−c)) ζ₂(7) + b(G(x−c))`. -/
noncomputable def Mtau (n : ℕ) (G : ℚ[X]) : ℚ_[2] :=
  (aL n (G.comp (X - C (cShift n))) : ℚ_[2]) * zeta2 7 + (bL n (G.comp (X - C (cShift n))) : ℚ_[2])

theorem Mtau_add (n : ℕ) (G H : ℚ[X]) : Mtau n (G + H) = Mtau n G + Mtau n H := by
  simp only [Mtau, add_comp, aL_add, bL_add]; push_cast; ring

theorem Mtau_smul (n : ℕ) (a : ℚ) (G : ℚ[X]) : Mtau n (a • G) = (a : ℚ_[2]) * Mtau n G := by
  simp only [Mtau, smul_comp, aL_smul, bL_smul]; push_cast; ring

theorem Mtau_eq_famL (n : ℕ) (G : ℚ[X]) (hG : G.natDegree ≤ 6 * n + 1) :
    Mtau n G = famL n (G.comp (X - C (cShift n))) := by
  have hdeg : (G.comp (X - C (cShift n))).natDegree ≤ 6 * n + 1 := by
    rw [natDegree_comp, natDegree_X_sub_C, mul_one]; exact hG
  rw [(lemma_2_1 n _ hdeg).2.2, Mtau]

/-- The `ℚ₂`-linear extension of `M` to `ℚ₂[τ]`. -/
noncomputable def Lam (n : ℕ) : ℚ_[2][X] →ₗ[ℚ_[2]] ℚ_[2] :=
  Polynomial.lsum fun e => LinearMap.smulRight LinearMap.id (Mtau n (X ^ e))

theorem Lam_monomial (n e : ℕ) (b : ℚ_[2]) : Lam n (monomial e b) = b * Mtau n (X ^ e) := by
  simp [Lam, lsum_apply, sum_monomial_index]

theorem Lam_map (n : ℕ) (G : ℚ[X]) : Lam n (G.map (algebraMap ℚ ℚ_[2])) = Mtau n G := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, hp, hq, Mtau_add]
  | monomial e a =>
    rw [map_monomial, Lam_monomial, ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, Mtau_smul]
    rfl

end ThmAAux

/-- **Theorem A**, `p`-adic norm form, from the entry bound for the fixed `n, K`
(only needed when `K ≥ 1`). -/
theorem thmA_norm_le_of {n K : ℕ} (hK : K ≤ 3 * n + 1)
    (hent : ∀ B : ℚ[X], IntValued B → B.natDegree ≤ 2 * K - 2 → 1 ≤ K →
      ‖Fam3.famL n (B.comp (X - C (((n : ℚ) + 1) / 2)))‖ ≤ (2 : ℝ) ^ (-entryBound n K)) :
    ‖aeval (zeta2 7) (Fam3.hankelPoly n K)‖ ≤
      ((2 : ℝ) ^ (-entryBound n K)) ^ K * ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2 := by
  rw [aeval_zeta_hankelPoly n K hK]
  have h1 : (Matrix.of fun i j : Fin K => famL n (X ^ ((i : ℕ) + j))).det =
      (Matrix.of fun i j : Fin K => Lam n (X ^ ((i : ℕ) + j))).det := by
    rw [← hankel_det_shift (Lam n) ((cShift n : ℚ) : ℚ_[2]) K]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    have e1 : (X + C ((cShift n : ℚ) : ℚ_[2])) ^ ((i : ℕ) + j) =
        ((X + C (cShift n)) ^ ((i : ℕ) + j)).map (algebraMap ℚ ℚ_[2]) := by
      simp [Polynomial.map_pow, Polynomial.map_add]
    have hdeg : ((X + C (cShift n)) ^ ((i : ℕ) + j)).natDegree ≤ 6 * n + 1 := by
      rw [natDegree_pow_X_add_C]; omega
    rw [e1, Lam_map, Mtau_eq_famL n _ hdeg]
    congr 1
    simp [pow_comp]
  rw [h1]
  refine norm_hankel_det_le_of_binom K (Lam n) _ (by positivity) fun i k hi hk => ?_
  rw [binomPoly_eq_map, binomPoly_eq_map, ← Polynomial.map_mul, Lam_map]
  have hdeg : (binomQ i * binomQ k).natDegree ≤ 2 * K - 2 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_binomQ, natDegree_binomQ]; omega
  rw [Mtau_eq_famL n _ (by omega)]
  exact hent _ ((intValued_binomQ i).mul (intValued_binomQ k)) hdeg (by omega)

/-- **Theorem A**, `p`-adic norm form. -/
theorem thmA_norm_le (h42 : Lemma42) {n K : ℕ} (hn : n % 2 = 1) (hK : K ≤ 3 * n + 1) :
    ‖aeval (zeta2 7) (Fam3.hankelPoly n K)‖ ≤
      ((2 : ℝ) ^ (-entryBound n K)) ^ K * ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2 :=
  thmA_norm_le_of hK fun B hB hd _ => h42 n K hn hK B hB hd

/-- `v₂(m!) ≥ m − 1 − log₂ m` (Legendre). -/
theorem padicValNat_factorial_ge (m : ℕ) :
    (m : ℝ) - 1 - Real.logb 2 m ≤ (padicValNat 2 m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  simp only [show 2 - 1 = 1 from rfl, one_mul] at h
  have hlen := Nat.digits_len 2 m (by norm_num) hm.ne'
  have hsum : (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
    have := List.sum_le_card_nsmul (Nat.digits 2 m) 1
      (fun x hx => Nat.lt_succ_iff.1 (Nat.digits_lt_base (by norm_num) hx))
    rw [hlen] at this; simpa using this
  have hle : (Nat.digits 2 m).sum ≤ m := Nat.digit_sum_le 2 m
  have hlog : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by exact_mod_cast Real.natLog_le_logb m 2
  have h2 : ((padicValNat 2 m.factorial : ℕ) : ℝ) = (m : ℝ) - ((Nat.digits 2 m).sum : ℕ) := by
    rw [h, Nat.cast_sub hle]
  rw [h2]
  have : (((Nat.digits 2 m).sum : ℕ) : ℝ) ≤ (Nat.log 2 m : ℝ) + 1 := by exact_mod_cast hsum
  linarith

/-- `‖m!‖₂ = 2^{−v₂(m!)}`. -/
theorem padicNorm_factorial (m : ℕ) :
    ‖((m.factorial : ℕ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(padicValNat 2 m.factorial : ℤ)) := by
  have h0 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have := Padic.eq_padicNorm (p := 2) (m.factorial : ℚ)
  push_cast at this
  rw [this, padicNorm.eq_zpow_of_nonzero h0]
  push_cast
  rw [padicValRat.of_nat]

/-- `2 ∑_{i<K} v₂(i!) ≥ K² − 3K − 2K log₂ K`. -/
theorem sum_factorial_bound (K : ℕ) :
    (K : ℝ) ^ 2 - 3 * K - 2 * K * Real.logb 2 K ≤
      2 * ∑ i : Fin K, (padicValNat 2 (i : ℕ).factorial : ℝ) := by
  have hL : ∀ i : Fin K, (i : ℝ) - 1 - Real.logb 2 K ≤ (padicValNat 2 (i : ℕ).factorial : ℝ) := by
    intro i
    refine le_trans ?_ (padicValNat_factorial_ge i)
    have : Real.logb 2 (i : ℕ) ≤ Real.logb 2 K := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · rw [h, Nat.cast_zero, Real.logb_zero]
        exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.one_le_iff_ne_zero.2
          (by have := i.isLt; omega)))
      · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
          (by exact_mod_cast i.isLt.le)
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hL i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hsum : ∑ i : Fin K, ((i : ℕ) : ℝ) = ((K : ℝ) * (K - 1)) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) K]
    have := Finset.sum_range_id_mul_two K
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp
    have h' : ((∑ i ∈ Finset.range K, i : ℕ) : ℝ) * 2 = (K : ℝ) * ((K - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'
    linarith
  rw [hsum] at hs
  nlinarith

/-- `A₃ − 3log₂D − log₂(D+1) ≥ 18n − 17 − 10 log₂ n`. -/
theorem entryBound_ge {n K : ℕ} (hn : 1 ≤ n) (hK : K ≤ 3 * n + 1) :
    18 * (n : ℝ) - 17 - 10 * Real.logb 2 n ≤ entryBound n K := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD1 : ((Dth n K : ℕ) : ℝ) + 1 ≤ 16 * n := by
    have : Dth n K + 1 ≤ 16 * n := by unfold Dth; omega
    exact_mod_cast this
  have hD0 : (0 : ℝ) < (Dth n K : ℕ) := by
    have : 0 < Dth n K := by unfold Dth; omega
    exact_mod_cast this
  have h16 : Real.logb 2 (16 * (n : ℝ)) = 4 + Real.logb 2 n := by
    rw [Real.logb_mul (by norm_num) (by positivity)]
    congr 1
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hl1 : Real.logb 2 ((Dth n K : ℝ) + 1) ≤ 4 + Real.logb 2 n := by
    rw [← h16]; exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hD1
  have hl2 : Real.logb 2 (Dth n K : ℝ) ≤ 4 + Real.logb 2 n := by
    rw [← h16]; exact Real.logb_le_logb_of_le (by norm_num) hD0 (by linarith)
  have hv := padicValNat_factorial_ge n
  unfold entryBound A3
  linarith
/-- From the norm form of Theorem A to its logarithmic form. -/
theorem thmA_logb_of_norm {n K : ℕ} (hn1 : 1 ≤ n) (hK : K ≤ 3 * n + 1) {x : ℝ} (hx : 0 < x)
    (hnorm : x ≤ ((2 : ℝ) ^ (-entryBound n K)) ^ K *
      ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2) :
    Real.logb 2 x ≤ -((K : ℝ) ^ 2 + 18 * n * K) + 100 * n * (1 + Real.logb 2 n) := by
  have hfac : ∀ i : Fin K, ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2 =
      (2 : ℝ) ^ (-(2 * (padicValNat 2 (i : ℕ).factorial : ℤ))) := by
    intro i
    rw [padicNorm_factorial, ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring
  simp only [hfac] at hnorm
  have hRpos : 0 < ((2 : ℝ) ^ (-entryBound n K)) ^ K *
      ∏ i : Fin K, (2 : ℝ) ^ (-(2 * (padicValNat 2 (i : ℕ).factorial : ℤ))) := by positivity
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hx hnorm
  have hR : Real.logb 2 (((2 : ℝ) ^ (-entryBound n K)) ^ K *
      ∏ i : Fin K, (2 : ℝ) ^ (-(2 * (padicValNat 2 (i : ℕ).factorial : ℤ)))) =
      -(K * entryBound n K) - 2 * ∑ i : Fin K, (padicValNat 2 (i : ℕ).factorial : ℝ) := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
      Real.logb_prod _ _ (fun i _ => by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
    simp only [← Real.rpow_intCast, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1), Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
    ring
  rw [hR] at hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hL0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hnR
  have hK4 : (K : ℝ) ≤ 4 * n := by
    have : K ≤ 4 * n := by omega
    exact_mod_cast this
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hlogK : Real.logb 2 K ≤ 2 + Real.logb 2 n := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, Nat.cast_zero, Real.logb_zero]; linarith
    · have h4 : Real.logb 2 (4 * (n : ℝ)) = 2 + Real.logb 2 n := by
        rw [Real.logb_mul (by norm_num) (by positivity)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        norm_num
      rw [← h4]; exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h) hK4
  have hA := entryBound_ge (K := K) hn1 hK
  have hS := sum_factorial_bound K
  have h1 := mul_le_mul_of_nonneg_left hA hK0
  have h2 := mul_le_mul_of_nonneg_left hlogK hK0
  have h3 := mul_le_mul_of_nonneg_right hK4 (by linarith : (0 : ℝ) ≤ 24 + 12 * Real.logb 2 n)
  nlinarith

/-- **Theorem A**, explicit logarithmic form. -/
theorem thmA_logb_le (h42 : Lemma42) {n K : ℕ} (hn : n % 2 = 1) (hK : K ≤ 3 * n + 1)
    (hne : aeval (zeta2 7) (Fam3.hankelPoly n K) ≠ 0) :
    Real.logb 2 ‖aeval (zeta2 7) (Fam3.hankelPoly n K)‖ ≤
      -((K : ℝ) ^ 2 + 18 * n * K) + 100 * n * (1 + Real.logb 2 n) :=
  thmA_logb_of_norm (by omega) hK (norm_pos_iff.2 hne) (thmA_norm_le h42 hn hK)

end Hankel2
