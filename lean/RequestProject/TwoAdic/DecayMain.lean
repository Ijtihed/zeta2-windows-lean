import RequestProject.TwoAdic.DecayEntry
import RequestProject.TwoAdic.Purity
import RequestProject.TwoAdic.InputDefs
import RequestProject.Frame.Bhargava
import RequestProject.Zeta7.Hankel2.ThmA2adic

/-!
# II, Theorem 3.1 (2-adic decay) — proved

`decay_holds`: for even `q ≥ 1`, odd `d`, even `n ≥ 1` and `K = qn`,

  `‖det[L(x^{i+j})]_{i,j<K}‖₂ ≤ 2^{−(2 ∑_{i<K} v₂(i!) + K(q(3n+1) + q v₂(n!) − d log₂ D − log₂(D+1)))}`,

`D = 2K − 2 + qn`, i.e. field (i) `decay` of `TwoAdicInputs`.

Proof (II, proof of Theorem 3.1): on proper polynomials `L` agrees with the `ℚ`-linear functional
`Λ(P) = b(P) + ∑_j ζ₂(d+2j+2) a_j(P)` (purity, `LamL`); the Bhargava basis `C(x − 1/2, i)` gives
`‖det‖ ≤ c^K ∏ ‖i!‖²` (`PadicWin.norm_hankel_det_le_shBinom`) with the entry bound
`c = ‖2^{q(3n+1)} (n!)^q‖ D^d (D+1)` (`norm_L_le_of_intValued`).
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

theorem Pjet_add (P Q : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (P + Q) k a = Pjet P k a + Pjet Q k a := by
  simp [Pjet, PadicWin.PF.Pjet]

theorem Pjet_smul (c : ℚ) (P : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (c • P) k a = c * Pjet P k a := by
  simp [Pjet, PadicWin.PF.Pjet]

theorem bL_add (q d n : ℕ) (P Q : ℚ[X]) : bL q d n (P + Q) = bL q d n P + bL q d n Q := by
  simp only [bL, Pjet_add, mul_add, Finset.sum_add_distrib]

theorem bL_smul (q d n : ℕ) (c : ℚ) (P : ℚ[X]) : bL q d n (c • P) = c * bL q d n P := by
  simp only [bL, Pjet_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring

theorem aL_add (q d n j : ℕ) (P Q : ℚ[X]) : aL q d n j (P + Q) = aL q d n j P + aL q d n j Q := by
  simp only [aL, Pjet_add, mul_add, Finset.sum_add_distrib]

theorem aL_smul (q d n j : ℕ) (c : ℚ) (P : ℚ[X]) : aL q d n j (c • P) = c * aL q d n j P := by
  simp only [aL, Pjet_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring

/-- The `ℚ`-linear functional `Λ(P) = b(P) + ∑_j ζ₂(d + 2(j+1) + 2) a_j(P)`, equal to `L(P)` on proper
polynomials (purity). -/
noncomputable def LamL (q d n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ_[2] where
  toFun P := ((bL q d n P : ℚ) : ℚ_[2]) +
    ∑ j : Fin (rr q), zetaVec q d j * ((aL q d n j P : ℚ) : ℚ_[2])
  map_add' P Q := by
    simp only [bL_add, aL_add, Rat.cast_add, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c P := by
    simp only [bL_smul, aL_smul, Rat.cast_mul, RingHom.id_apply, Rat.smul_def, mul_add,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring

theorem LamL_apply (q d n : ℕ) (P : ℚ[X]) :
    LamL q d n P = ((bL q d n P : ℚ) : ℚ_[2]) +
      ∑ j : Fin (rr q), zetaVec q d j * ((aL q d n j P : ℚ) : ℚ_[2]) := rfl

/-- `logb₂ ‖c₀‖ = −(q(3n+1) + q v₂(n!))`. -/
theorem logb_norm_c0 (q n : ℕ) :
    Real.logb 2 ‖c0 q n‖ = -((q : ℝ) * (3 * n + 1) + q * (v2fact n : ℝ)) := by
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
    have := Padic.norm_p (p := 2); exact_mod_cast this
  rw [c0, norm_mul, norm_pow, norm_pow, h2, padicNorm_factorial]
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_inv, Real.logb_self_eq_one (by norm_num), ← Real.rpow_intCast,
    Real.logb_rpow (by norm_num) (by norm_num)]
  unfold v2fact
  push_cast
  simp only [padicValRat.of_nat, Int.cast_natCast]
  ring

/-- **II, Theorem 3.1 (2-adic decay), `K = qn` — proved.** -/
theorem decay_holds {q d n : ℕ} (hq : Even q) (hd : Odd d) (hn : Even n) (hq1 : 1 ≤ q)
    (hn0 : 0 < n) :
    ‖(hankelL q d n (q * n)).det‖ ≤ (2 : ℝ) ^ (-decayExp q d n (q * n)) := by
  set K := q * n with hK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set D := decayD q n K with hD
  have hD1 : 1 ≤ D := by
    simp only [hD, decayD]
    have : 1 ≤ q * n := hK1
    omega
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set c : ℝ := ‖c0 q n‖ * (D : ℝ) ^ d * ((D : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  -- the Hankel matrix of `L` is that of `Λ`
  have hprop : 2 * K ≤ q * (2 * n + 1) := by rw [hK]; nlinarith
  have hHL : hankelL q d n K = Matrix.of fun i j : Fin K => LamL q d n (X ^ ((i : ℕ) + (j : ℕ))) := by
    ext i j
    simp only [hankelL, Matrix.of_apply]
    rw [L_eq_purity hq hd hn _ (natDegree_X_pow_le_of_proper hprop i j)]
    rfl
  -- entries in the Bhargava basis
  have hentry : ∀ i k : ℕ, i < K → k < K →
      ‖LamL q d n (PadicWin.shBinom (1 / 2) i * PadicWin.shBinom (1 / 2) k)‖ ≤ c := by
    intro i k hi hk
    set B := PadicWin.shBinom (1 / 2) i * PadicWin.shBinom (1 / 2) k
    have hBdeg : B.natDegree ≤ i + k := by
      refine natDegree_mul_le.trans ?_
      rw [PadicWin.natDegree_shBinom, PadicWin.natDegree_shBinom]
    have hpur : B.natDegree + q * n + 2 ≤ q * (3 * n + 1) := by
      have h1 : q * (3 * n + 1) = q * (2 * n + 1) + q * n := by ring
      omega
    rw [LamL_apply, ← L_eq_purity hq hd hn B hpur]
    refine norm_L_le_of_intValued q d hn B (fun u => ?_) hD1 ?_
    · refine ⟨(u.choose i * u.choose k : ℕ), ?_⟩
      simp only [B, eval_mul, PadicWin.shBinom_eval_nat]
      push_cast; ring
    · simp only [hD, decayD]
      omega
  have hbound := PadicWin.norm_hankel_det_le_shBinom K (LamL q d n) (1 / 2) c hc0 hentry
  rw [hHL]
  refine hbound.trans (le_of_eq ?_)
  -- the constant
  have hpos : 0 < c ^ K * ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2 := by
    have hc0pos : 0 < ‖c0 q n‖ := by
      rw [norm_pos_iff, c0]
      exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
        (pow_ne_zero _ (by exact_mod_cast (Nat.factorial_pos n).ne'))
    have : 0 < c := by positivity
    refine mul_pos (pow_pos this _) (Finset.prod_pos fun i _ => pow_pos ?_ _)
    rw [norm_pos_iff]; exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hpos]
  congr 1
  have hc0pos : 0 < ‖c0 q n‖ := by
    rw [norm_pos_iff, c0]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
      (pow_ne_zero _ (by exact_mod_cast (Nat.factorial_pos n).ne'))
  have hcpos : 0 < c := by
    rw [hc]; exact mul_pos (mul_pos hc0pos (pow_pos (by linarith) _)) (by linarith)
  have hfpos : ∀ i : Fin K, 0 < ‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2 := by
    intro i
    have : 0 < ‖((i : ℕ).factorial : ℚ_[2])‖ := by
      rw [norm_pos_iff]; exact_mod_cast (Nat.factorial_pos _).ne'
    positivity
  rw [Real.logb_mul (pow_pos hcpos _).ne' (Finset.prod_pos fun i _ => hfpos i).ne',
    Real.logb_pow, Real.logb_prod _ _ (fun i _ => (hfpos i).ne')]
  have hfi : ∀ i : Fin K, Real.logb 2 (‖((i : ℕ).factorial : ℚ_[2])‖ ^ 2) = -2 * (v2fact i : ℝ) := by
    intro i
    rw [Real.logb_pow, padicNorm_factorial, ← Real.rpow_intCast,
      Real.logb_rpow (by norm_num) (by norm_num)]
    unfold v2fact; push_cast
    simp only [padicValRat.of_nat, Int.cast_natCast]
    ring
  have hc' : Real.logb 2 c = -((q : ℝ) * (3 * n + 1) + q * (v2fact n : ℝ)) +
      d * Real.logb 2 D + Real.logb 2 ((D : ℝ) + 1) := by
    rw [hc, Real.logb_mul (by positivity) (by positivity), Real.logb_mul hc0pos.ne'
      (by positivity), Real.logb_pow, logb_norm_c0]
  rw [Finset.sum_congr rfl fun i _ => hfi i, hc', decayExp, ← hD]
  have hs : ∑ i : Fin K, -2 * (v2fact (i : ℕ) : ℝ) = -2 * ∑ i ∈ range K, (v2fact i : ℝ) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (v2fact i : ℝ)) K]
  rw [hs]
  ring

end TwoAdicWin
