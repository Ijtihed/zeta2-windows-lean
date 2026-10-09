import RequestProject.TwoAdic.Defs
import RequestProject.Frame.Criterion
import RequestProject.Zeta7.Hankel2.Zeta27Defs
import RequestProject.Zeta7.PNT.MertensPrime

/-!
# Definitions for the analytic inputs of Paper II (§§3–6); all are proved in later modules

Only *definitions*: the objects in terms of which the fields of `TwoAdicWin.TwoAdicInputs`
(`Main.lean`) are stated.

* admissibility of `(q, d)` (II, Theorem 1.1): `4 ≤ q`, `q` even, `d` odd, `q ≤ d + 1`,
  `7(d+2) ≤ 10q` (`Admissible`), and `δ = (d+2)/q − 1` (`deltaOf`);
* §3 (decay, II Theorem 3.1, `A = q`): the exponent
  `2 ∑_{i<K} v₂(i!) + K(q(3n+1) + q v₂(n!) − d log₂ D − log₂(D+1))`, `D = 2K − 2 + qn` (`decayExp`);
* §4 (archimedean, II Theorem 4.1): `F = (q²/4)(6 + 8 ln 2 − 9 ln 3)` (`Fconst`);
* §5 (denominators; II Theorem 5.1 and Cor. 5.4): the tree bound `T_ℓ` for the local Hankel
  blocks `C_k = [c_{k,a+b}]_{a,b<q}`, `c_{k,m} = β_{k,m} + ∑_j X_j α^{(j)}_{k,m}` (`cMv`, `CmatQ`,
  `minorRQ`, `ellRQ`, `eP`, `lambdaP`, `fP`, `penalty`, `profiles`, `TP`, `TPplus`), exactly the tree bound of [P, Thm 7.1]
  for general `q` and several variables; Mertens' sum with `ℓ = 2` removed (`mertensOddSum`, the sum of
  `PNT.tendsto_mertens_odd`); and the constant
  `C̃(δ) = [M₀ − ln 20 + I(δ) + (1+δ)ε + ε²/2] / ln 2`, `ε = 1/20` (`Ctil`), for a Mertens constant
  `M₀` (the true one is `−γ − ln 2`) and the circle-model integral
  `I(δ) = ∫_ε^{7/2} min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ)) du` of II, Cor. 5.4.
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

/-- **Admissible parameters** (II, Theorem 1.1): `q ≥ 4` even, `d` odd, `q ≤ d + 1`,
`(d + 2)/q ≤ 10/7`. -/
def Admissible (q d : ℕ) : Prop :=
  4 ≤ q ∧ Even q ∧ Odd d ∧ q ≤ d + 1 ∧ 7 * (d + 2) ≤ 10 * q

/-- `δ = (d + 2)/q − 1`. -/
noncomputable def deltaOf (q d : ℕ) : ℝ := ((d : ℝ) + 2) / q - 1

/-! ### §3: decay -/

/-- `v₂(i!)`. -/
def v2fact (i : ℕ) : ℕ := padicValNat 2 i.factorial

/-- `D = 2K − 2 + qn` (II, Theorem 3.1 with `A = q`). -/
def decayD (q n K : ℕ) : ℕ := 2 * K - 2 + q * n

/-- **The exponent of II, Theorem 3.1** (`A = q`):
`2 ∑_{i<K} v₂(i!) + K (q(3n+1) + q v₂(n!) − d log₂ D − log₂(D+1))`, `D = 2K − 2 + qn`. -/
noncomputable def decayExp (q d n K : ℕ) : ℝ :=
  2 * ∑ i ∈ range K, (v2fact i : ℝ) +
    K * ((q : ℝ) * (3 * n + 1) + q * (v2fact n : ℝ) - d * Real.logb 2 (decayD q n K)
      - Real.logb 2 ((decayD q n K : ℝ) + 1))

/-! ### The archimedean constant -/

/-- `F = (q²/4)(6 + 8 ln 2 − 9 ln 3)`. -/
noncomputable def Fconst (q : ℕ) : ℝ := (q : ℝ) ^ 2 / 4 * (6 + 8 * Real.log 2 - 9 * Real.log 3)

/-! ### §5: the tree bound (II, Theorem A.2) -/

/-- The local constant `c_{k,m} = β_{k,m} + ∑_j X_j α^{(j)}_{k,m}` for `m < q`, and `0` for `m ≥ q`. -/
noncomputable def cMv (q d n : ℕ) (k : ℤ) (m : ℕ) : MvPolynomial (Fin (rr q)) ℚ :=
  if m < q then
    MvPolynomial.C (betaC q d n k m) +
      ∑ j : Fin (rr q), MvPolynomial.C (alphaC q d n j k m) * MvPolynomial.X j
  else 0

/-- The local Hankel block `C_k = [c_{k,a+b}]_{0 ≤ a,b < q}`. -/
noncomputable def CmatQ (q d n : ℕ) (k : ℤ) : Matrix (Fin q) (Fin q) (MvPolynomial (Fin (rr q)) ℚ) :=
  fun a b => cMv q d n k ((a : ℕ) + b)

/-- The minor `det C_k[R, {0, …, |R|−1}]`. -/
noncomputable def minorRQ (q d n : ℕ) (k : ℤ) (Rs : Finset (Fin q)) : MvPolynomial (Fin (rr q)) ℚ :=
  (Matrix.of fun i j : Fin Rs.card =>
    CmatQ q d n k (Rs.orderEmbOfFin rfl i) (Fin.castLE (by simpa using Rs.card_le_univ) j)).det

/-- `λ(R) = ∑ R − C(|R|, 2)`. -/
def ellRQ {q : ℕ} (Rs : Finset (Fin q)) : ℕ := (∑ r ∈ Rs, (r : ℕ)) - Rs.card.choose 2

/-- The unclipped `e_ℓ(k,s,λ) = max −v_ℓ(det C_k[R,{0..s−1}])` over `|R| = s`, `λ(R) = λ`
(`−∞` if there is no nonzero such minor). -/
noncomputable def eP (q d n ℓ : ℕ) (k : ℤ) (s j : ℕ) : WithBot ℤ :=
  (univ.filter fun Rs : Finset (Fin q) => Rs.card = s ∧ ellRQ Rs = j).sup
    fun Rs => negTop (PadicWin.gaussValMv ℓ (minorRQ q d n k Rs))

/-- `λ_ℓ(k) = max_{m ≠ k} v_ℓ(k − m)` over the nodes. -/
noncomputable def lambdaP (n ℓ : ℕ) (k : ℤ) : ℕ :=
  ((nodes n).erase k).sup fun m => padicValInt ℓ (k - m)

/-- `f_ℓ(k,s) = max_{0 ≤ λ ≤ s(q−s)} [e_ℓ(k,s,λ) + λ λ_ℓ(k)]` for `s ≥ 1`, `f_ℓ(k,0) = 0`. -/
noncomputable def fP (q d n ℓ : ℕ) (k : ℤ) (s : ℕ) : WithBot ℤ :=
  if s = 0 then 0 else
    (range (s * (q - s) + 1)).sup fun j =>
      eP q d n ℓ k s j + (((j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ)

/-- The node `k = i − R` indexed by `i : Fin (2R+1)`. -/
def nodeOf (n : ℕ) (i : Fin (2 * R n + 1)) : ℤ := (i : ℤ) - R n

/-- The level penalty `∑_{j ≥ 1} ∑_{c mod ℓ^j} (S_c² − ∑_{k ∈ c} s_k²)` (levels `j ≤ 2R+1` suffice:
beyond them every class contains at most one node). -/
def penalty (n ℓ : ℕ) (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ j ∈ Icc 1 (2 * R n + 1), ∑ c ∈ range (ℓ ^ j),
    (((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i : ℕ) : ℤ) ^ 2
      - ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i ^ 2 : ℕ) : ℤ))

/-- The profiles `0 ≤ s_k ≤ q` with `∑ s_k = K`. -/
def profiles (q n K : ℕ) : Finset (Fin (2 * R n + 1) → ℕ) :=
  (Fintype.piFinset fun _ => range (q + 1)).filter fun s => ∑ i, s i = K

/-- **The tree bound** `T_ℓ = max_s [∑_k f_ℓ(k, s_k) − penalty(s)]` (P, Thm 7.1). -/
noncomputable def TP (q d n ℓ K : ℕ) : WithBot ℤ :=
  (profiles q n K).sup fun s =>
    (∑ i, fP q d n ℓ (nodeOf n i) (s i)) + (((-penalty n ℓ s : ℤ)) : WithBot ℤ)

/-- `max(T_ℓ, 0)` as an integer. -/
noncomputable def TPplus (q d n ℓ K : ℕ) : ℤ := WithBot.unbotD 0 (max (TP q d n ℓ K) 0)

/-! ### §5: Mertens and the constant `C̃(δ)` -/

/-- `∑_{3 ≤ ℓ ≤ Y, ℓ prime} ln ℓ / (ℓ − 1)` (Mertens' sum with `ℓ = 2` removed; this is the sum of
`PNT.tendsto_mertens_odd`). -/
noncomputable def mertensOddSum (Y : ℝ) : ℝ :=
  ∑ ℓ ∈ Icc 3 ⌊Y⌋₊ with ℓ.Prime, Real.log ℓ / ((ℓ : ℝ) - 1)

/-- `ε = 1/20`. -/
noncomputable def epsC : ℝ := 1 / 20

/-- **The constant of II, Cor. 5.4**, for a Mertens constant `M₀` and the circle-model integral
`I(δ) = ∫_ε^{7/2} min_{τ ≥ 0} (τ + ∑_t meas_t(u) ψ̃_t(τ)) du` (passed as the function `circ`):
`C̃(δ) = [M₀ − ln 20 + I(δ) + (1+δ)ε + ε²/2] / ln 2`.  The true Mertens constant is `−γ − ln 2`. -/
noncomputable def Ctil (M₀ : ℝ) (circ : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (M₀ - Real.log 20 + circ δ + (1 + δ) * epsC + epsC ^ 2 / 2) / Real.log 2

/-- The Mertens constant with `ℓ = 2` removed: `−γ − ln 2`. -/
noncomputable def mertensOddConst : ℝ := -Real.eulerMascheroniConstant - Real.log 2

end TwoAdicWin
