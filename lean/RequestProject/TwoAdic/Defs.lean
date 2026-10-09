import RequestProject.TwoAdic.Target
import RequestProject.Frame.PartialFrac

/-!
# The construction of Paper II, §2: weight, functional, local constants, Hankel polynomial

Notation of Paper II, §2.  The parameters are `q` (even, `≥ 4`), `d` (odd),
`n` (even) and `K`; the definitions make sense for all natural numbers.

* the nodes `𝒦 = {k ∈ ℤ : |k| ≤ R}`, `R = ⌊3n/2⌋` (`nodes`, `3n+1` of them for even `n`);
* the zeros `z_j = n/2 − 1/2 − j`, `0 ≤ j < n` (`zeroPt`);
* the weight `W(t) = ∏_{j<n} (t − z_j)^q / ∏_{|k| ≤ R} (t+k)^q` on `ℚ₂` (`W`);
* the functional `L(P) = ∫_{ℤ₂} (P W)^{(d)}(t + 1/2) dt` (`L`), the Volkenborn integral of the
  `d`-th derivative;
* `H_k[b] = [u^b] u^q W(−k+u)` (`Hk`), computed as `[u^b] N(−k+u) · E_k(u)^{-1}` with
  `N(t) = ∏_j (t − z_j)^q` (`numPoly`) and `E_k(u) = ∏_{k' ≠ k}(u + k' − k)^q`;
* `P_a(k) = [u^a] P(−k+u)` (`Pjet`);
* the rising factorial `(i)_d = i(i+1)⋯(i+d−1)` (`rising`);
* the harmonic corrections `T_k(M)` of II, Lemma 2.2, for both signs of `k` (`Tk`):
  `T_k(M) = −M 2^{M+1} ∑_{0 ≤ j < k} (2j+1)^{−M−1}` for `k ≥ 0`,
  `T_k(M) = M (−1)^{M+1} 2^{M+1} ∑_{1 ≤ i ≤ |k|} (2i−1)^{−M−1}` for `k < 0`;
* the local constants (II, Lemma 2.2): `c_{k,a} = β_{k,a} + ∑_{j=1}^{r} X_j α^{(j)}_{k,a}`, `r = q/2 − 1`,
  where, with the variable `X_j` standing for `ζ₂(d + 2j + 2)` and `i_j = 2j + 1`,
  `α^{(j)}_{k,a} = (−1)^d (i_j)_d H_k[q − i_j − a] · (i_j + d) 2^{i_j + d + 1}` if `i_j ≤ q − a` (else `0`),
  `β_{k,a} = ∑_{i=1}^{q−a} (−1)^d (i)_d H_k[q−i−a] T_k(i+d)`.
  In Lean the variables are indexed by `j : Fin r` (0-based), so `X_j` is `ζ₂(d + 2(j+1) + 2)` and
  `i_j = 2j + 3` (`alphaC`, `betaC`).  The contributions `I_{i+d}` with `i` even vanish (`I_M = 0` for odd
  `M`) and the one with `i = 1` cancels in `L` by the residue theorem; this is why they do not occur in
  `β`.
* `a_j(P) = ∑_k ∑_{a<q} α^{(j)}_{k,a} P_a(k)` (`aL`), `b(P) = ∑_k ∑_{a<q} β_{k,a} P_a(k)` (`bL`);
* **the Hankel polynomial**
  `Δ_K(X) = det[b(x^{i+j}) + ∑_j X_j a_j(x^{i+j})]_{i,j<K} ∈ ℚ[X_0, …, X_{r-1}]` (`hankelPoly`).
-/

open Polynomial Finset

namespace TwoAdicWin

open Hankel2

/-- `R = ⌊3n/2⌋` (exactly `3n/2` for even `n`). -/
def R (n : ℕ) : ℕ := 3 * n / 2

/-- The nodes `k ∈ ℤ` with `|k| ≤ R`. -/
def nodes (n : ℕ) : Finset ℤ := Finset.Icc (-(R n : ℤ)) (R n)

theorem card_nodes (n : ℕ) : (nodes n).card = 2 * R n + 1 := by
  rw [nodes, Int.card_Icc]; omega

theorem R_of_even {n : ℕ} (hn : Even n) : 2 * R n = 3 * n := by
  obtain ⟨m, rfl⟩ := hn; unfold R; omega

theorem card_nodes_of_even {n : ℕ} (hn : Even n) : (nodes n).card = 3 * n + 1 := by
  rw [card_nodes, R_of_even hn]

/-- The zeros `z_j = n/2 − 1/2 − j` (`0 ≤ j < n`). -/
noncomputable def zeroPt (n j : ℕ) : ℚ := (n : ℚ) / 2 - 1 / 2 - j

/-- **The weight of II, §2**: `W(t) = ∏_{j<n} (t − z_j)^q / ∏_{|k| ≤ R} (t+k)^q` on `ℚ₂`. -/
noncomputable def W (q n : ℕ) (t : ℚ_[2]) : ℚ_[2] :=
  (∏ j ∈ range n, (t - ((zeroPt n j : ℚ) : ℚ_[2])) ^ q) / ∏ k ∈ nodes n, (t + (k : ℚ_[2])) ^ q

/-- **The functional of II, §2**: `L(P) = ∫_{ℤ₂} (P W)^{(d)}(t + 1/2) dt`. -/
noncomputable def L (q d n : ℕ) (P : ℚ[X]) : ℚ_[2] :=
  volkInt 2 (fun t => iteratedDeriv d (fun s => aeval s P * W q n s) (t + 1 / 2))

/-- The numerator `N(t) = ∏_{j<n} (t − z_j)^q` of `W`. -/
noncomputable def numPoly (q n : ℕ) : ℚ[X] := ∏ j ∈ range n, (X - C (zeroPt n j)) ^ q

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

/-- `H_k[b] = [u^b] u^q W(−k + u) = [u^b] N(−k+u) E_k(u)^{-1}`. -/
noncomputable def Hk (q n : ℕ) (k : ℤ) (b : ℕ) : ℚ :=
  PowerSeries.coeff b (ι (taylor (-(k : ℚ)) (numPoly q n)) * PadicWin.PF.Hser (nodes n) q k)

/-- `P_a(k) = [u^a] P(−k + u)`. -/
noncomputable def Pjet (P : ℚ[X]) (k : ℤ) (a : ℕ) : ℚ := PadicWin.PF.Pjet P k a

/-- The rising factorial `(i)_d = i (i+1) ⋯ (i+d−1)`. -/
def rising (i d : ℕ) : ℚ := ∏ l ∈ range d, ((i : ℚ) + l)

/-- **The harmonic corrections `T_k(M)` of II, Lemma 2.2**, for every `k ∈ ℤ`. -/
noncomputable def Tk (k : ℤ) (M : ℕ) : ℚ :=
  if 0 ≤ k then -(M : ℚ) * 2 ^ (M + 1) * ∑ j ∈ range k.natAbs, (((2 * j + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹
  else (M : ℚ) * (-1) ^ (M + 1) * 2 ^ (M + 1) *
    ∑ i ∈ Icc 1 k.natAbs, (((2 * i - 1 : ℕ) : ℚ) ^ (M + 1))⁻¹

/-- The number of zeta variables `r = q/2 − 1`. -/
def rr (q : ℕ) : ℕ := q / 2 - 1

/-- `α^{(j)}_{k,a}` (0-based `j`, `i_j = 2j+3`): the coefficient of `X_j = ζ₂(d + 2(j+1) + 2)` in
`c_{k,a}`. -/
noncomputable def alphaC (q d n : ℕ) (j : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  if 2 * j + 3 + a ≤ q then
    (-1) ^ d * rising (2 * j + 3) d * Hk q n k (q - (2 * j + 3) - a) *
      (((2 * j + 3 + d : ℕ) : ℚ) * 2 ^ (2 * j + 3 + d + 1))
  else 0

/-- `β_{k,a}`, the rational part of `c_{k,a}`. -/
noncomputable def betaC (q d n : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  ∑ i ∈ Icc 1 (q - a), (-1) ^ d * rising i d * Hk q n k (q - i - a) * Tk k (i + d)

/-- `a_j(P) = ∑_k ∑_{a<q} α^{(j)}_{k,a} P_a(k)`. -/
noncomputable def aL (q d n j : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range q, alphaC q d n j k a * Pjet P k a

/-- `b(P) = ∑_k ∑_{a<q} β_{k,a} P_a(k)`. -/
noncomputable def bL (q d n : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range q, betaC q d n k a * Pjet P k a

/-- The entries `b(P) + ∑_j X_j a_j(P)` of the Hankel matrix, in `ℚ[X_0, …, X_{r-1}]`. -/
noncomputable def LX (q d n : ℕ) (P : ℚ[X]) : MvPolynomial (Fin (rr q)) ℚ :=
  MvPolynomial.C (bL q d n P) +
    ∑ j : Fin (rr q), MvPolynomial.C (aL q d n j P) * MvPolynomial.X j

/-- **The Hankel polynomial of II, §2**:
`Δ_K(X) = det[b(x^{i+j}) + ∑_j X_j a_j(x^{i+j})]_{i,j<K} ∈ ℚ[X_0, …, X_{r−1}]`. -/
noncomputable def hankelPoly (q d n K : ℕ) : MvPolynomial (Fin (rr q)) ℚ :=
  (Matrix.of fun i j : Fin K => LX q d n (X ^ ((i : ℕ) + j))).det

/-- The zeta values `X_j = ζ₂(d + 2(j+1) + 2)`, `j < r`. -/
noncomputable def zetaVec (q d : ℕ) : Fin (rr q) → ℚ_[2] := fun j => zeta2 (d + 2 * ((j : ℕ) + 1) + 2)

/-- The Hankel matrix `[L(x^{i+j})]_{i,j<K}` of the functional itself. -/
noncomputable def hankelL (q d n K : ℕ) : Matrix (Fin K) (Fin K) ℚ_[2] :=
  Matrix.of fun i j : Fin K => L q d n (X ^ ((i : ℕ) + j))

end TwoAdicWin
