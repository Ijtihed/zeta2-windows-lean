import RequestProject.TwoAdic.PurityPF

/-!
# Purity (II, Lemma 2.2)

For even `q`, odd `d`, even `n` and `P` with `deg(P W) ≤ −2` (i.e. `deg P + qn + 2 ≤ q(3n+1)`):

* `hasVolkenborn_L`: the Volkenborn integral defining `L(P)` exists and equals
  `∑_k ∑_{i=1}^{q} r_{k,i} (−1)^d (i)_d (I_{i+d} + T_k(i+d))`, `I_M = M 2^{M+1} ζ₂(M+1)`;
* `IM_odd`: `I_M = 0` for odd `M` (`ζ₂` vanishes at even arguments);
* `L_eq_purity`: **purity**, `L(P) = b(P) + ∑_j ζ₂(d + 2j + 2) a_j(P)`, i.e.
  `L(P) = ∑_k ∑_{a<q} c_{k,a} P_a(k)` with `c_{k,a} = β_{k,a} + ∑_j X_j α^{(j)}_{k,a}` at
  `X_j = ζ₂(d+2j+2)`;
* `aeval_zeta_hankelPoly`: for `2K ≤ q(2n+1)` (properness, `deg(x^{2K−2} W) ≤ −2`; `K = qn` qualifies),
  `Δ_K(ζ₂(d+4), …, ζ₂(d+q)) = det[L(x^{i+j})]_{i,j<K}`.

Remark on the properness range: with the `n` zeros of order `q`, `deg(x^{2K−2} W) = 2K − 2 + qn − q(3n+1)`,
so properness is `2K ≤ q(2n+1)`; the bound `K ≤ q(3n+1)/2` is the one for
the zero-free family (a).
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

/-- `I_M = ∫_{ℤ₂} (t + 1/2)^{-M} dt = M 2^{M+1} ζ₂(M+1)`. -/
noncomputable def Ival (M : ℕ) : ℚ_[2] := (M : ℚ_[2]) * 2 ^ (M + 1) * zeta2 (M + 1)

/-- `I_M = 0` for odd `M` (`ζ₂` vanishes at even arguments). -/
theorem IM_odd {M : ℕ} (hM : Odd M) : Ival M = 0 := by
  have hz : zeta2 (M + 1) = 0 := by
    obtain ⟨m, rfl⟩ := hM
    refine zeta2_even_eq_zero (2 * m + 1 + 1) ⟨m + 1, by ring⟩ (by omega)
      (exists_hasVolkenborn_half _) (exists_hasVolkenborn_half _)
  rw [Ival, hz, mul_zero]

theorem nat_add_half_mem_nonPolesS (S : Finset ℤ) (t : ℕ) :
    (t : ℚ_[2]) + 1 / 2 ∈ PadicWin.nonPolesS 2 S := by
  intro k _
  have h := add_ne_zero_of_norm_lt (c := (1 / 2 : ℚ_[2])) (x := (t : ℚ_[2]) + k)
    (by simpa using Padic.norm_int_le_one (p := 2) ((t : ℤ) + k)) norm_half_2
  intro h0; apply h; linear_combination h0

theorem hasVolkenborn_congr_nat {f g : ℚ_[2] → ℚ_[2]} {I : ℚ_[2]}
    (h : ∀ t : ℕ, f t = g t) (hf : HasVolkenborn 2 f I) : HasVolkenborn 2 g I := by
  have : volkSum 2 f = volkSum 2 g := by
    funext N; simp only [volkSum, h]
  rwa [HasVolkenborn, ← this]

/-- **The Volkenborn integral of `L(P)` exists, with its node expansion.** -/
theorem hasVolkenborn_L (q d n : ℕ) (P : ℚ[X])
    (hP : (P * numPoly q n).natDegree + 1 ≤ q * (nodes n).card) :
    HasVolkenborn 2 (fun t => iteratedDeriv d (fun s => aeval s P * W q n s) (t + 1 / 2))
      (∑ k ∈ nodes n, ∑ i ∈ Icc 1 q, ((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) *
        (Ival (i + d) + ((Tk k (i + d) : ℚ) : ℚ_[2]))) := by
  have hterm : ∀ k ∈ nodes n, ∀ i ∈ Icc 1 q,
      HasVolkenborn 2 (fun t => ((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) *
          ((t + 1 / 2 + (k : ℚ_[2])) ^ (i + d))⁻¹)
        (((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) *
          (Ival (i + d) + ((Tk k (i + d) : ℚ) : ℚ_[2]))) := by
    intro k _ i hi
    obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
    have hM : ((i + d : ℕ) : ℚ_[2]) ≠ 0 := by exact_mod_cast (show i + d ≠ 0 by omega)
    have h := hasVolkenborn_half_shift_int (i + d) hM k
    refine HasVolkenborn.const_mul _ ?_
    have hfun : (fun t : ℚ_[2] => ((t + 1 / 2 + (k : ℚ_[2])) ^ (i + d))⁻¹) =
        fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ (i + d))⁻¹ := by
      funext t; ring_nf
    rw [hfun]
    convert h using 1
    rw [Ival, Tk_eq_neg_HS]
    push_cast
    ring
  have hsum := HasVolkenborn.sum (nodes n) _ _ fun k hk =>
    HasVolkenborn.sum (Icc 1 q) _ _ (hterm k hk)
  refine hasVolkenborn_congr_nat (fun t => ?_) hsum
  have hmem := nat_add_half_mem_nonPolesS (nodes n) t
  rw [PadicWin.iteratedDeriv_eq_Gsum (nodes n) (rco q n P) q _
    (fun s hs => PW_eq_Gsum q n P hP hs) d _ hmem]
  rfl

/-! ### The algebra of purity -/

theorem sum_Icc_range_swap {M : Type*} [AddCommMonoid M] (q : ℕ) (f : ℕ → ℕ → M) :
    ∑ i ∈ Icc 1 q, ∑ a ∈ range (q + 1 - i), f i a =
      ∑ a ∈ range q, ∑ i ∈ Icc 1 (q - a), f i a := by
  refine Finset.sum_comm' fun i a => ?_
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

theorem dco_eq (i d : ℕ) : PadicWin.dco i d = (-1) ^ d * rising i d := rfl

/-- The `T`-part of the node expansion is `b(P)`. -/
theorem Tpart_eq_bL (q d n : ℕ) (P : ℚ[X]) :
    ∑ k ∈ nodes n, ∑ i ∈ Icc 1 q, rco q n P k i * PadicWin.dco i d * Tk k (i + d) = bL q d n P := by
  unfold bL betaC
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∀ i ∈ Icc 1 q, rco q n P k i * PadicWin.dco i d * Tk k (i + d) =
      ∑ a ∈ range (q + 1 - i), Pjet P k a * Hk q n k (q - i - a) * PadicWin.dco i d * Tk k (i + d) := by
    intro i hi
    rw [resCoef_mul_numPoly q n P k (Finset.mem_Icc.mp hi).2, Finset.sum_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl h1, sum_Icc_range_swap]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dco_eq]; ring

/-- The coefficient of `ζ₂(d + 2(j+1) + 2)`: `∑_k r_{k,i_j} (−1)^d (i_j)_d M 2^{M+1} = a_j(P)`,
`i_j = 2j+3`, `M = i_j + d`. -/
theorem Ipart_coeff_eq_aL (q d n j : ℕ) (P : ℚ[X]) (hj : 2 * j + 3 ≤ q) :
    ∑ k ∈ nodes n, rco q n P k (2 * j + 3) * PadicWin.dco (2 * j + 3) d *
        (((2 * j + 3 + d : ℕ) : ℚ) * 2 ^ (2 * j + 3 + d + 1)) = aL q d n j P := by
  unfold aL alphaC
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resCoef_mul_numPoly q n P k hj, Finset.sum_mul, Finset.sum_mul]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilt : (range q).filter (fun a => 2 * j + 3 + a ≤ q) = range (q + 1 - (2 * j + 3)) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dco_eq]; ring

/-- **Purity (II, Lemma 2.2).**  For even `q`, odd `d`, even `n` and `deg P + qn + 2 ≤ q(3n+1)`,
the Volkenborn integral defining `L(P)` exists and
`L(P) = b(P) + ∑_j ζ₂(d + 2(j+1) + 2) a_j(P) = ∑_k ∑_{a<q} c_{k,a} P_a(k)`. -/
theorem L_eq_purity {q d n : ℕ} (hq : Even q) (hd : Odd d) (hn : Even n) (P : ℚ[X])
    (hP : P.natDegree + q * n + 2 ≤ q * (3 * n + 1)) :
    L q d n P = ((bL q d n P : ℚ) : ℚ_[2]) +
      ∑ j : Fin (rr q), zetaVec q d j * ((aL q d n j P : ℚ) : ℚ_[2]) := by
  have hcard := card_nodes_of_even hn
  have hdeg : (P * numPoly q n).natDegree + 2 ≤ q * (nodes n).card := by
    rw [hcard]
    have := natDegree_mul_le (p := P) (q := numPoly q n)
    have := natDegree_numPoly_le q n
    omega
  have hV := hasVolkenborn_L q d n P (by omega)
  rw [L, hV.volkInt_eq]
  -- split into the `T`-part and the `I`-part
  have hsplit : ∀ k ∈ nodes n, ∑ i ∈ Icc 1 q, ((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) *
        (Ival (i + d) + ((Tk k (i + d) : ℚ) : ℚ_[2])) =
      ((∑ i ∈ Icc 1 q, rco q n P k i * PadicWin.dco i d * Tk k (i + d) : ℚ) : ℚ_[2]) +
        ∑ i ∈ Icc 1 q, ((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) * Ival (i + d) := by
    intro k _
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Rat.cast_sum, Tpart_eq_bL]
  congr 1
  -- the `I`-part
  rw [Finset.sum_comm]
  have hres : ∑ k ∈ nodes n, rco q n P k 1 = 0 :=
    PadicWin.PF.sum_resCoef_one_eq_zero (nodes n) q (P * numPoly q n) hdeg
  set g : ℕ → ℚ_[2] := fun i => ∑ k ∈ nodes n,
    ((rco q n P k i * PadicWin.dco i d : ℚ) : ℚ_[2]) * Ival (i + d) with hg
  have hg0 : ∀ i ∈ Icc 1 q, i ∉ (range (rr q)).image (fun j => 2 * j + 3) → g i = 0 := by
    intro i hi hni
    obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.mp hi
    rcases Nat.even_or_odd i with he | ho
    · -- `i` even: `I_{i+d} = 0`
      have : Odd (i + d) := Even.add_odd he hd
      simp only [hg, IM_odd this, mul_zero, Finset.sum_const_zero]
    · -- `i` odd and not of the form `2j+3`: then `i = 1`, killed by the residue theorem
      have hi1' : i = 1 := by
        by_contra hne
        apply hni
        obtain ⟨m, rfl⟩ := ho
        obtain ⟨t, rfl⟩ := hq
        refine Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr ?_, by omega⟩
        unfold rr; omega
      subst hi1'
      simp only [hg]
      rw [← Finset.sum_mul]
      have : ∑ k ∈ nodes n, ((rco q n P k 1 * PadicWin.dco 1 d : ℚ) : ℚ_[2]) = 0 := by
        rw [← Rat.cast_sum, ← Finset.sum_mul, hres, zero_mul, Rat.cast_zero]
      rw [this, zero_mul]
  have hsub : (range (rr q)).image (fun j => 2 * j + 3) ⊆ Icc 1 q := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_range] at hj
    obtain ⟨t, rfl⟩ := hq
    unfold rr at hj
    simp only [Finset.mem_Icc]; omega
  change ∑ i ∈ Icc 1 q, g i = _
  rw [← Finset.sum_subset hsub hg0, Finset.sum_image (fun a _ b _ h => by omega)]
  rw [show (∑ j : Fin (rr q), zetaVec q d j * ((aL q d n j P : ℚ) : ℚ_[2])) =
      ∑ m ∈ range (rr q), zeta2 (d + 2 * (m + 1) + 2) * ((aL q d n m P : ℚ) : ℚ_[2])
      from Fin.sum_univ_eq_sum_range
        (fun m : ℕ => zeta2 (d + 2 * (m + 1) + 2) * ((aL q d n m P : ℚ) : ℚ_[2])) (rr q)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hj : 2 * x + 3 ≤ q := by
    rw [Finset.mem_range] at hx
    obtain ⟨t, rfl⟩ := hq
    unfold rr at hx; omega
  have hA := congrArg (fun y : ℚ => (y : ℚ_[2])) (Ipart_coeff_eq_aL q d n x P hj)
  simp only at hA
  rw [← hA, show d + 2 * (x + 1) + 2 = 2 * x + 3 + d + 1 by ring]
  simp only [hg, Ival]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end TwoAdicWin

namespace TwoAdicWin

theorem natDegree_X_pow_le_of_proper {q n K : ℕ} (hK : 2 * K ≤ q * (2 * n + 1)) (i j : Fin K) :
    (X ^ ((i : ℕ) + j) : ℚ[X]).natDegree + q * n + 2 ≤ q * (3 * n + 1) := by
  rw [natDegree_X_pow]
  have hi := i.2
  have hj := j.2
  have h1 : q * (3 * n + 1) = q * (2 * n + 1) + q * n := by ring
  omega

/-- **The node functional evaluates the Hankel polynomial (II, Lemma 2.2)**: for even `q`, odd `d`,
even `n` and `2K ≤ q(2n+1)` (properness; in particular `K = qn`),
`Δ_K(ζ₂(d+4), …, ζ₂(d+q)) = det[L(x^{i+j})]_{i,j<K}`. -/
theorem aeval_zeta_hankelPoly {q d n K : ℕ} (hq : Even q) (hd : Odd d) (hn : Even n)
    (hK : 2 * K ≤ q * (2 * n + 1)) :
    MvPolynomial.aeval (zetaVec q d) (hankelPoly q d n K) = (hankelL q d n K).det := by
  unfold hankelPoly hankelL
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [L_eq_purity hq hd hn _ (natDegree_X_pow_le_of_proper hK i j), LX]
  simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    eq_ratCast]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end TwoAdicWin
