import RequestProject.TwoAdic.LeafBound
import RequestProject.TwoAdic.TreeBound

/-!
# Single-level leaf values, `A = q`

Let `ℓ` be an odd prime with `4n < ℓ²` (a *single-level* prime: every node difference and every
doubled node–zero difference has `ℓ`-adic valuation `≤ 1`).  For a node `k` put

* `N_c = Ncl n ℓ k`: the nodes `m ≡ k (mod ℓ)` (including `k`);
* `z_c = Zcl n ℓ k`: the zeros `z_j` with `ℓ ∣ 2(−k − z_j)`;
* `μ_k = muI n ℓ k = 1` iff `N_c ≥ 2` or `z_c ≥ 1`;
* `hs_k = hsI ℓ k = 1` iff `ℓ ≤ 2|k| − 1` (some harmonic denominator `2j + 1`, `j < |k|`, is divisible
  by `ℓ`);
* `c_k = q + d + 1` if `hs_k = 1` and `c_k = q − 1` otherwise (`cK`).

**`fP_le_single`**: `f_ℓ(k, s) ≤ s(D_k + c_k) − s(s − 1)` if `μ_k = 1` or `hs_k = 1`,
and `f_ℓ(k, s) ≤ 0` otherwise; here `D_k = q(N_c − 1 − z_c)` (`Dk_single`).

The proof: `v(H_k[b]) ≥ −D_k − b μ_k` (`Hk_VB_single`), `v(T_k(M)) ≥ −(M+1) hs_k`
(`Tk_VB_single`), hence `v(c_{k,a}) ≥ −D_k − (c_k − a)` (`nvMv_cMv_single`), and the minor bound with
the row/column-dependent entry bound (`fP_le_gen`).
-/

open Finset Polynomial PadicWin

namespace TwoAdicWin.Asm

open Dom Leaf

/-- `N_c`: the nodes congruent to `k` modulo `ℓ` (including `k`). -/
def Ncl (n ℓ : ℕ) (k : ℤ) : ℕ := ((nodes n).filter fun m => (ℓ : ℤ) ∣ m - k).card

/-- `z_c`: the zeros `z_j` with `ℓ ∣ 2(−k − z_j)`. -/
def Zcl (n ℓ : ℕ) (k : ℤ) : ℕ := ((range n).filter fun j => (ℓ : ℤ) ∣ ez n j k).card

/-- `μ_k = 1` iff the class of `k` has another node or a zero. -/
def muI (n ℓ : ℕ) (k : ℤ) : ℕ := if 2 ≤ Ncl n ℓ k ∨ 1 ≤ Zcl n ℓ k then 1 else 0

/-- `hs_k = 1` iff `ℓ ≤ 2|k| − 1`. -/
def hsI (ℓ : ℕ) (k : ℤ) : ℕ := if (ℓ : ℤ) ≤ 2 * |k| - 1 then 1 else 0

/-- `c_k = q + d + 1` (hs) or `q − 1` (non-hs). -/
def cK (q d ℓ : ℕ) (k : ℤ) : ℤ := if hsI ℓ k = 1 then (q : ℤ) + d + 1 else (q : ℤ) - 1

/-- The single-level leaf value bound `s(D_k + c_k) − s(s−1)` (active nodes) or `0`. -/
noncomputable def gval (q d n ℓ : ℕ) (k : ℤ) (s : ℕ) : ℤ :=
  if muI n ℓ k = 1 ∨ hsI ℓ k = 1 then
    (s : ℤ) * (Dk q n ℓ k + cK q d ℓ k) - (s : ℤ) * ((s : ℤ) - 1)
  else 0

theorem muI_le_one (n ℓ : ℕ) (k : ℤ) : muI n ℓ k ≤ 1 := by unfold muI; split_ifs <;> omega
theorem hsI_le_one (ℓ : ℕ) (k : ℤ) : hsI ℓ k ≤ 1 := by unfold hsI; split_ifs <;> omega

theorem one_le_Ncl {n ℓ : ℕ} {k : ℤ} (hk : k ∈ nodes n) : 1 ≤ Ncl n ℓ k :=
  card_pos.2 ⟨k, mem_filter.2 ⟨hk, by simp⟩⟩

variable {q d n ℓ : ℕ} [hp : Fact ℓ.Prime]

/-- Valuations of integers of absolute value `< ℓ²` are `≤ 1`. -/
theorem padicValInt_le_one_of_lt {x : ℤ} (hx : x ≠ 0) (h : x.natAbs < ℓ ^ 2) :
    padicValInt ℓ x ≤ 1 := by
  have h1 : ℓ ^ padicValInt ℓ x ∣ x.natAbs := by unfold padicValInt; exact pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hx) h1
  by_contra hc
  have : ℓ ^ 2 ≤ ℓ ^ padicValInt ℓ x := Nat.pow_le_pow_right hp.out.pos (by omega)
  omega

theorem one_le_padicValInt_of_dvd {x : ℤ} (hx : x ≠ 0) (h : (ℓ : ℤ) ∣ x) : 1 ≤ padicValInt ℓ x := by
  have := (padicValInt_dvd_iff (p := ℓ) 1 x).1 (by simpa using h)
  rcases this with h0 | h1
  · exact absurd h0 hx
  · exact h1

theorem dvd_of_one_le_padicValInt {x : ℤ} (h : 1 ≤ padicValInt ℓ x) : (ℓ : ℤ) ∣ x := by
  have := (padicValInt_dvd_iff (p := ℓ) 1 x).2 (Or.inr h)
  simpa using this

/-- `v_ℓ(x) = [ℓ ∣ x]` for `0 < |x| < ℓ²`. -/
theorem padicValInt_eq_ind {x : ℤ} (hx : x ≠ 0) (h : x.natAbs < ℓ ^ 2) :
    (padicValInt ℓ x : ℤ) = if (ℓ : ℤ) ∣ x then 1 else 0 := by
  have h1 := padicValInt_le_one_of_lt hx h
  split_ifs with hd
  · have := one_le_padicValInt_of_dvd hx hd; omega
  · have : padicValInt ℓ x = 0 := by
      by_contra h0; exact hd (dvd_of_one_le_padicValInt (by omega))
    simp [this]

omit hp in
theorem sq_gt_of_four (hsl : 4 * n < ℓ ^ 2) {x : ℤ} (hx : x.natAbs ≤ 4 * n - 1) : x.natAbs < ℓ ^ 2 := by
  omega

/-- **`D_k` at a single-level prime**: `D_k = q(N_c − 1 − z_c)`. -/
theorem Dk_single (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2) {k : ℤ} (hk : k ∈ nodes n) :
    Dk q n ℓ k = q * ((Ncl n ℓ k : ℤ) - 1 - Zcl n ℓ k) := by
  unfold Dk
  have h1 : ∑ m ∈ (nodes n).erase k, (padicValInt ℓ (m - k) : ℤ) = (Ncl n ℓ k : ℤ) - 1 := by
    rw [sum_congr rfl fun m hm => padicValInt_eq_ind (sub_ne_zero.2 (mem_erase.1 hm).1)
      (sq_gt_of_four hsl (nodes_diff_natAbs (mem_erase.1 hm).2 hk hn1))]
    rw [sum_boole]
    have : (nodes n).filter (fun m => (ℓ : ℤ) ∣ m - k) =
        insert k (((nodes n).erase k).filter fun m => (ℓ : ℤ) ∣ m - k) := by
      ext m
      simp only [mem_filter, mem_insert, mem_erase]
      constructor
      · rintro ⟨hm, hd⟩
        by_cases hmk : m = k
        · exact Or.inl hmk
        · exact Or.inr ⟨⟨hmk, hm⟩, hd⟩
      · rintro (rfl | ⟨⟨_, hm⟩, hd⟩)
        · exact ⟨hk, by simp⟩
        · exact ⟨hm, hd⟩
    unfold Ncl
    rw [this, card_insert_of_notMem (by simp)]
    push_cast; ring
  have h2 : ∑ j ∈ range n, (padicValInt ℓ (ez n j k) : ℤ) = (Zcl n ℓ k : ℤ) := by
    rw [sum_congr rfl fun j hj => padicValInt_eq_ind (ez_ne_zero hn j k)
      (sq_gt_of_four hsl (ez_natAbs hk (mem_range.1 hj)))]
    rw [sum_boole]; rfl
  rw [h1, h2]; ring

theorem padicValInt_ez_le_mu (hn : Even n) (hsl : 4 * n < ℓ ^ 2) {k : ℤ} (hk : k ∈ nodes n)
    {j : ℕ} (hj : j < n) : padicValInt ℓ (ez n j k) ≤ muI n ℓ k := by
  have hle := padicValInt_le_one_of_lt (ℓ := ℓ) (ez_ne_zero hn j k)
    (sq_gt_of_four hsl (ez_natAbs hk hj))
  by_cases hd : (ℓ : ℤ) ∣ ez n j k
  · have : 1 ≤ Zcl n ℓ k := card_pos.2 ⟨j, mem_filter.2 ⟨mem_range.2 hj, hd⟩⟩
    unfold muI; rw [if_pos (Or.inr this)]; exact hle
  · have : padicValInt ℓ (ez n j k) = 0 := by
      by_contra h0; exact hd (dvd_of_one_le_padicValInt (by omega))
    omega

theorem padicValInt_diff_le_mu (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2) {k m : ℤ} (hk : k ∈ nodes n)
    (hm : m ∈ nodes n) (hmk : m ≠ k) : padicValInt ℓ (m - k) ≤ muI n ℓ k := by
  have hle := padicValInt_le_one_of_lt (ℓ := ℓ) (sub_ne_zero.2 hmk)
    (sq_gt_of_four hsl (nodes_diff_natAbs hm hk hn1))
  by_cases hd : (ℓ : ℤ) ∣ m - k
  · have : 2 ≤ Ncl n ℓ k := by
      unfold Ncl
      have h2 : ({k, m} : Finset ℤ) ⊆ (nodes n).filter fun m => (ℓ : ℤ) ∣ m - k := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_filter.2 ⟨hk, by simp⟩
        · exact mem_filter.2 ⟨hm, hd⟩
      have := card_le_card h2
      rwa [card_pair (Ne.symm hmk)] at this
    unfold muI; rw [if_pos (Or.inl this)]; exact hle
  · have : padicValInt ℓ (m - k) = 0 := by
      by_contra h0; exact hd (dvd_of_one_le_padicValInt (by omega))
    omega

/-- **Single-level Taylor bound (`H_k`)**: `v_ℓ(H_k[b]) ≥ −D_k − b μ_k` at a single-level prime. -/
theorem Hk_VB_single (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) (hsl : 4 * n < ℓ ^ 2) {k : ℤ}
    (hk : k ∈ nodes n) (b : ℕ) :
    VB ℓ (Hk q n k b) (-Dk q n ℓ k - b * (muI n ℓ k : ℤ)) := by
  rw [Hk_eq_coeff]
  set L : ℤ := (muI n ℓ k : ℤ)
  have hA : PSL ℓ (∑ j ∈ range n, (q : ℤ) * padicValInt ℓ (ez n j k)) L
      (∏ j ∈ range n, (PowerSeries.C ((ez n j k : ℚ) / 2) + PowerSeries.X) ^ q) := by
    refine PSL.prod _ _ _ fun j hj => PSL_C_add_X_pow (VB_half h2 (VB_int_val _)) ?_ q
    simp only [L]; exact_mod_cast padicValInt_ez_le_mu hn hsl hk (mem_range.1 hj)
  have hB : PSL ℓ (∑ m ∈ (nodes n).erase k, (q : ℤ) * -(padicValInt ℓ (m - k) : ℤ)) L
      (∏ m ∈ (nodes n).erase k, (PowerSeries.C (((m - k : ℤ) : ℚ)) + PowerSeries.X)⁻¹ ^ q) := by
    refine PSL.prod _ _ _ fun m hm => ?_
    rw [mem_erase] at hm
    have hne : m - k ≠ 0 := sub_ne_zero.2 hm.1
    refine (PSL_inv_C_add_X (by exact_mod_cast hne) VB_int_inv_val ?_).pow q
    simp only [L]; exact_mod_cast padicValInt_diff_le_mu hn1 hsl hk hm.2 hm.1
  have := (hA.mul hB) b
  refine this.mono (le_of_eq ?_)
  unfold Dk
  rw [mul_sum, mul_sum]
  simp only [mul_neg, sum_neg_distrib]
  ring

/-- **Single-level harmonic bound (`T_k`)**: `v_ℓ(T_k(M)) ≥ −(M + 1) hs_k` at a single-level prime. -/
theorem Tk_VB_single (hsl : 4 * n < ℓ ^ 2) {k : ℤ} (hk : k ∈ nodes n) (M : ℕ) :
    VB ℓ (Tk k M) (-((M + 1 : ℕ) : ℤ) * (hsI ℓ k : ℤ)) := by
  have hkk : k.natAbs ≤ 3 * n / 2 := by
    rw [mem_nodes_iff] at hk; unfold R at hk; omega
  have hterm : ∀ j ∈ range k.natAbs,
      VB ℓ ((((2 * j + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹) (-((M + 1 : ℕ) : ℤ) * (hsI ℓ k : ℤ)) := by
    intro j hj
    rw [mem_range] at hj
    refine VB_of_padicValRat ?_
    rw [padicValRat.inv, padicValRat.pow (by positivity), padicValRat.of_nat]
    have hv : padicValNat ℓ (2 * j + 1) ≤ hsI ℓ k := by
      have hle := padicValInt_le_one_of_lt (ℓ := ℓ) (x := ((2 * j + 1 : ℕ) : ℤ)) (by omega)
        (by simp only [Int.natAbs_natCast]; omega)
      have hle' : padicValNat ℓ (2 * j + 1) ≤ 1 := by simpa [padicValInt] using hle
      by_cases h0 : padicValNat ℓ (2 * j + 1) = 0
      · omega
      · have hd : ℓ ∣ 2 * j + 1 := by
          have := dvd_of_one_le_padicValInt (ℓ := ℓ) (x := ((2 * j + 1 : ℕ) : ℤ))
            (by simp only [padicValInt, Int.natAbs_natCast]; omega)
          exact_mod_cast this
        have hle2 := Nat.le_of_dvd (by omega) hd
        have : hsI ℓ k = 1 := by
          unfold hsI; rw [if_pos]
          have : (k.natAbs : ℤ) = |k| := Int.natCast_natAbs k
          omega
        omega
    have h' : ((padicValNat ℓ (2 * j + 1) : ℕ) : ℤ) ≤ (hsI ℓ k : ℤ) := by exact_mod_cast hv
    push_cast
    nlinarith
  have hsum := VB.sum _ _ hterm
  have hM : VB ℓ (M : ℚ) 0 := VB_natCast M
  have h2 : VB ℓ ((2 : ℚ) ^ (M + 1)) 0 := by simpa using (VB_natCast (ℓ := ℓ) 2).pow (M + 1)
  unfold Tk
  split_ifs
  · have := ((hM.neg.mul h2)).mul hsum
    simpa using this
  · rw [sum_Icc_odd_eq_range]
    have hs : VB ℓ ((-1 : ℚ) ^ (M + 1)) 0 := by simpa using ((VB_one (ℓ := ℓ)).neg).pow (M + 1)
    have := ((hM.mul hs).mul h2).mul hsum
    simpa using this

/-- The entry bound `E(m) = D_k + c_k − m` (active nodes) or `0`. -/
noncomputable def Ebd (q d n ℓ : ℕ) (k : ℤ) (m : ℕ) : ℤ :=
  if muI n ℓ k = 1 ∨ hsI ℓ k = 1 then Dk q n ℓ k + cK q d ℓ k - m else 0

theorem Dk_inactive (hn : Even n) (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2) {k : ℤ} (hk : k ∈ nodes n)
    (hmu : muI n ℓ k = 0) : Dk q n ℓ k = 0 := by
  rw [Dk_single hn hn1 hsl hk]
  have h1 := one_le_Ncl (ℓ := ℓ) hk
  unfold muI at hmu
  split_ifs at hmu with h
  push_neg at h
  have : Ncl n ℓ k = 1 := by omega
  have : Zcl n ℓ k = 0 := by omega
  simp [*]

theorem betaC_VB_single (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) (hsl : 4 * n < ℓ ^ 2) {k : ℤ}
    (hk : k ∈ nodes n) {a : ℕ} (ha : a < q) :
    VB ℓ (betaC q d n k a) (-Ebd q d n ℓ k a) := by
  have hmu := muI_le_one n ℓ k
  have hhs := hsI_le_one ℓ k
  unfold Ebd
  split_ifs with hact
  · refine betaC_VB_gen k a (fun i => -Dk q n ℓ k - ((q - i - a : ℕ) : ℤ) * (muI n ℓ k : ℤ))
      (fun i => -((i + d + 1 : ℕ) : ℤ) * (hsI ℓ k : ℤ))
      (fun i _ => Hk_VB_single hn hn1 h2 hsl hk _) (fun i _ => Tk_VB_single hsl hk _) _
      (fun i hi => ?_)
    rw [mem_Icc] at hi
    dsimp only
    have e1 : ((q - i - a : ℕ) : ℤ) = q - i - a := by omega
    rw [e1]
    unfold cK
    have hmu' : (muI n ℓ k : ℤ) ≤ 1 := by exact_mod_cast hmu
    have hmu0 : (0 : ℤ) ≤ muI n ℓ k := by positivity
    have hqa : (0 : ℤ) ≤ q - i - a := by omega
    split_ifs with hh
    · rw [hh]; push_cast; nlinarith
    · have hh0 : hsI ℓ k = 0 := by omega
      have hm1 : muI n ℓ k = 1 := by omega
      rw [hh0, hm1]; push_cast; omega
  · push_neg at hact
    have hm0 : muI n ℓ k = 0 := by omega
    have hh0 : hsI ℓ k = 0 := by omega
    have hD := Dk_inactive (q := q) hn hn1 hsl hk hm0
    refine betaC_VB_gen k a (fun _ => 0) (fun _ => 0) (fun i _ => ?_) (fun i _ => ?_) _
      (fun i _ => by simp)
    · have := Hk_VB_single (q := q) hn hn1 h2 hsl hk (q - i - a)
      rw [hD, hm0] at this; simpa using this
    · have := Tk_VB_single hsl hk (i + d)
      rw [hh0] at this; simpa using this

theorem alphaC_VB_single (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) (hsl : 4 * n < ℓ ^ 2) {k : ℤ}
    (hk : k ∈ nodes n) (j : ℕ) (a : ℕ) :
    VB ℓ (alphaC q d n j k a) (-Ebd q d n ℓ k a) := by
  by_cases hq : 2 * j + 3 + a ≤ q
  · refine alphaC_VB_gen k j a _ ((Hk_VB_single hn hn1 h2 hsl hk _).mono ?_)
    have hmu := muI_le_one n ℓ k
    have hmu' : (muI n ℓ k : ℤ) ≤ 1 := by exact_mod_cast hmu
    have hmu0 : (0 : ℤ) ≤ muI n ℓ k := by positivity
    have e1 : ((q - (2 * j + 3) - a : ℕ) : ℤ) = q - (2 * j + 3) - a := by omega
    rw [e1]
    unfold Ebd
    split_ifs with hact
    · unfold cK
      have hqa : (0 : ℤ) ≤ q - (2 * j + 3) - a := by omega
      split_ifs <;> nlinarith
    · push_neg at hact
      have hm0 : muI n ℓ k = 0 := by omega
      rw [Dk_inactive (q := q) hn hn1 hsl hk hm0, hm0]; simp
  · unfold alphaC; rw [if_neg hq]; exact VB_zero _

/-- The Gauss valuation of `c_{k,m}` at a single-level prime: `−v ≤ E(m)`. -/
theorem nvMv_cMv_single (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) (hsl : 4 * n < ℓ ^ 2) {k : ℤ}
    (hk : k ∈ nodes n) (m : ℕ) :
    nvMv ℓ (cMv q d n k m) ≤ ((Ebd q d n ℓ k m : ℤ) : WithBot ℤ) := by
  unfold cMv
  split_ifs with hm
  · set B : ℤ := Ebd q d n ℓ k m
    have hcoef : ∀ c : ℚ, VB ℓ c (-B) →
        nvMv ℓ (MvPolynomial.C c : MvPolynomial (Fin (rr q)) ℚ) ≤ (B : WithBot ℤ) := by
      intro c hc
      refine nvMv_C_le ((norm_le_of_VB hc).trans (le_of_eq ?_))
      rw [neg_neg]
    refine (nvMv_add_le _ _).trans (max_le (hcoef _ (betaC_VB_single hn hn1 h2 hsl hk hm)) ?_)
    refine (nvMv_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (nvMv_mul_le _ _).trans ?_
    have h1 := hcoef _ (alphaC_VB_single (d := d) hn hn1 h2 hsl hk j m)
    have h3 := nvMv_X_le (ℓ := ℓ) j
    calc nvMv ℓ (MvPolynomial.C (alphaC q d n (↑j) k m)) + nvMv ℓ (MvPolynomial.X j)
        ≤ (B : WithBot ℤ) + 0 := add_le_add h1 h3
      _ = (B : WithBot ℤ) := add_zero _
  · simp

/-! ### The minor bound with row/column-dependent entry bounds -/

theorem nvMv_det_le_rc {σ : Type*} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℚ))
    (r c : Fin s → ℤ) (hM : ∀ i j, nvMv ℓ (M i j) ≤ ((r i + c j : ℤ) : WithBot ℤ)) :
    nvMv ℓ M.det ≤ ((∑ i, r i + ∑ j, c j : ℤ) : WithBot ℤ) := by
  rw [Matrix.det_apply]
  refine (nvMv_sum_le _ _).trans (Finset.sup_le fun τ _ => ?_)
  rw [nvMv_zsmul_units]
  refine (nvMv_prod_le _ _).trans ?_
  calc ∑ i, nvMv ℓ (M (τ i) i) ≤ ∑ i, ((r (τ i) + c i : ℤ) : WithBot ℤ) :=
        sum_le_sum fun i _ => hM _ _
    _ = ((∑ i, (r (τ i) + c i) : ℤ) : WithBot ℤ) := (WithBot.coe_sum _ _).symm
    _ = ((∑ i, r i + ∑ j, c j : ℤ) : WithBot ℤ) := by
        rw [sum_add_distrib, Equiv.sum_comp τ r]

theorem sum_orderEmb_eq {q : ℕ} (Rs : Finset (Fin q)) :
    ∑ i : Fin Rs.card, ((Rs.orderEmbOfFin rfl i : Fin q) : ℕ) = ∑ r ∈ Rs, (r : ℕ) := by
  set e := Rs.orderEmbOfFin rfl
  rw [← Finset.sum_image (f := fun r : Fin q => (r : ℕ)) (s := univ)
    (g := fun i => e i) (fun a _ b _ h => e.injective h)]
  congr 1
  ext r
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact Rs.orderEmbOfFin_mem rfl i
  · intro hr
    obtain ⟨i, hi⟩ := (Set.ext_iff.1 (Rs.range_orderEmbOfFin rfl) r).2 (by simpa using hr)
    exact ⟨i, hi⟩

theorem choose_le_sumR {q : ℕ} (Rs : Finset (Fin q)) : Rs.card.choose 2 ≤ ∑ r ∈ Rs, (r : ℕ) := by
  rw [← sum_orderEmb_eq]
  refine choose_two_le_sumQ (F := fun i => ((Rs.orderEmbOfFin rfl i : Fin q) : ℕ)) ?_
  intro i j h
  exact (Rs.orderEmbOfFin rfl).strictMono h

theorem two_choose_two (s : ℕ) : ((s.choose 2 : ℕ) : ℤ) * 2 = s * ((s : ℤ) - 1) := by
  have h2 : s.choose 2 * 2 = s * (s - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; simp
  have h3 : ((s.choose 2 * 2 : ℕ) : ℤ) = ((s * (s - 1) : ℕ) : ℤ) := by rw [h2]
  push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at h3
  exact h3

/-- **Generic leaf bound**: if `−v(c_{k,m}) ≤ D' − m L` for all `m` and `λ_ℓ(k) ≤ L`, then
`f_ℓ(k, s) ≤ s D' − L s (s − 1)`. -/
theorem fP_le_gen {k : ℤ} (D' : ℤ) (L : ℕ)
    (hc : ∀ m : ℕ, nvMv ℓ (cMv q d n k m) ≤ ((D' - m * L : ℤ) : WithBot ℤ))
    (hlam : lambdaP n ℓ k ≤ L) (s : ℕ) :
    fP q d n ℓ k s ≤ (((s : ℤ) * D' - L * s * ((s : ℤ) - 1) : ℤ) : WithBot ℤ) := by
  have hminor : ∀ Rs : Finset (Fin q), nvMv ℓ (minorRQ q d n k Rs) ≤
      (((Rs.card : ℤ) * D' - L * ((∑ r ∈ Rs, (r : ℕ) : ℕ) + Rs.card.choose 2 : ℕ) : ℤ) :
        WithBot ℤ) := by
    intro Rs
    unfold minorRQ
    refine (nvMv_det_le_rc _
      (fun i => D' - L * ((Rs.orderEmbOfFin rfl i : Fin q) : ℕ))
      (fun j => -(L * (j : ℕ) : ℤ)) fun i j => ?_).trans (le_of_eq ?_)
    · simp only [Matrix.of_apply, CmatQ]
      refine (hc _).trans (le_of_eq ?_)
      congr 1
      simp only [Fin.val_castLE]
      push_cast; ring
    · congr 1
      rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum, sum_neg_distrib,
        ← mul_sum]
      have h1 : ∑ i : Fin Rs.card, (((Rs.orderEmbOfFin rfl i : Fin q) : ℕ) : ℤ) =
          ∑ r ∈ Rs, (r : ℕ) := by exact_mod_cast sum_orderEmb_eq Rs
      have h2 : ∑ i : Fin Rs.card, ((i : ℕ) : ℤ) = Rs.card.choose 2 := by
        exact_mod_cast sum_fin_id Rs.card
      rw [h1, h2]
      push_cast; ring
  unfold fP
  split_ifs with hs0
  · subst hs0; simp
  refine Finset.sup_le fun j _ => ?_
  set B : ℤ := (s : ℤ) * D' - L * s * ((s : ℤ) - 1)
  have hE : eP q d n ℓ k s j ≤ ((B - (j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun Rs hRs => ?_
    simp only [mem_filter, mem_univ, true_and] at hRs
    obtain ⟨hRc, hRj⟩ := hRs
    refine (hminor Rs).trans (WithBot.coe_le_coe.2 ?_)
    have hc := choose_le_sumR Rs
    have hj : (j : ℤ) = (∑ r ∈ Rs, (r : ℕ) : ℕ) - Rs.card.choose 2 := by
      rw [← hRj, ellRQ]; push_cast [Nat.cast_sub hc]; ring
    have hch := two_choose_two s
    have hlam' : ((j * lambdaP n ℓ k : ℕ) : ℤ) ≤ j * L := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (by positivity)
    rw [hRc] at hj ⊢
    simp only [B]
    have hjL := congrArg (· * (L : ℤ)) hj
    have hchL := congrArg (· * (L : ℤ)) hch
    simp only at hjL hchL
    push_cast at hjL hlam' ⊢
    nlinarith
  calc eP q d n ℓ k s j + (((j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ)
      ≤ ((B - (j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ) +
          (((j * lambdaP n ℓ k : ℕ) : ℤ) : WithBot ℤ) := add_le_add_left hE _
    _ = (B : WithBot ℤ) := by rw [← WithBot.coe_add, sub_add_cancel]

theorem lambdaP_le_mu (hn1 : 1 ≤ n) (hsl : 4 * n < ℓ ^ 2) {k : ℤ} (hk : k ∈ nodes n) :
    lambdaP n ℓ k ≤ muI n ℓ k := by
  unfold lambdaP
  refine Finset.sup_le fun m hm => ?_
  rw [mem_erase] at hm
  have := padicValInt_diff_le_mu hn1 hsl hk hm.2 hm.1
  have e : padicValInt ℓ (k - m) = padicValInt ℓ (m - k) := by
    unfold padicValInt; rw [← neg_sub, Int.natAbs_neg]
  rw [e]; exact this

/-- **Leaf values**: at a single-level prime,
`f_ℓ(k, s) ≤ s(D_k + c_k) − s(s−1)` if `μ_k = 1` or `hs_k = 1`, and `f_ℓ(k, s) ≤ 0` otherwise. -/
theorem fP_le_single (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) (hsl : 4 * n < ℓ ^ 2) {k : ℤ}
    (hk : k ∈ nodes n) (s : ℕ) :
    fP q d n ℓ k s ≤ ((gval q d n ℓ k s : ℤ) : WithBot ℤ) := by
  have hlam := lambdaP_le_mu hn1 hsl hk
  by_cases hact : muI n ℓ k = 1 ∨ hsI ℓ k = 1
  · have hlam1 : lambdaP n ℓ k ≤ 1 := hlam.trans (muI_le_one n ℓ k)
    refine (fP_le_gen (Dk q n ℓ k + cK q d ℓ k) 1 (fun m => ?_) hlam1 s).trans (le_of_eq ?_)
    · refine (nvMv_cMv_single hn hn1 h2 hsl hk m).trans (le_of_eq ?_)
      unfold Ebd; rw [if_pos hact]; push_cast; ring_nf
    · unfold gval; rw [if_pos hact]; push_cast; ring_nf
  · have hm0 : muI n ℓ k = 0 := by have := muI_le_one n ℓ k; omega
    refine (fP_le_gen 0 0 (fun m => ?_) (by rw [← hm0]; exact hlam) s).trans (le_of_eq ?_)
    · refine (nvMv_cMv_single hn hn1 h2 hsl hk m).trans (le_of_eq ?_)
      unfold Ebd; rw [if_neg hact]; simp
    · unfold gval; rw [if_neg hact]; simp

end TwoAdicWin.Asm
