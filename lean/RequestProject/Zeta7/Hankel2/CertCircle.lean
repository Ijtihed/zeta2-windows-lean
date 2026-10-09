import RequestProject.Zeta7.Hankel2.CertPsi

/-!
# Computable circle model at rational `u` (paper §8.4, Appendix B)

For rational `u > 0` the data of the circle model are rational:
`k_i(u) = ⌊b_i/u⌋` (`kkQ`), `ρ_i(u)` (`rhoQ`), the gap ends `L_β, R_β` (`LQ`, `RQ`), and the type
`τ(k, β)` of a gap (`tauC`, computed by interval counting).

* `kk_cast`, `rho_cast`, `len_cast`, `tau_eq_tauC`: agreement with `kk`, `rho`, `Lbeta/Rbeta`, `tau`;
* `Gpot_eq_betaSum`: `Gpot ψ u = ∑_β max(R_β − L_β, 0) ψ(τ(k(u), β))` (from `meas_eq_sum`);
* `gpotQ`, **`gfun_le_gpotQ`**: the computable upper bound `λκ + gpotQ u λ` for `g(λ, u, κ)`.
-/

open Finset MeasureTheory

namespace Hankel2.CertC

open Hankel2.Fam3 Hankel2.Circle

/-- The boundary points `−1, 2, u/2, u/2 + 1`. -/
def bptQ (u : ℚ) (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => -1
  | 1 => 2
  | 2 => u / 2
  | _ => u / 2 + 1

theorem bpt_cast (u : ℚ) (i : Fin 4) : bpt (u : ℝ) i = (bptQ u i : ℝ) := by
  fin_cases i <;> simp [bpt, bptQ]

/-- `k_i(u) = ⌊b_i/u⌋`. -/
def kkQ (u : ℚ) (i : Fin 4) : ℤ := ⌊bptQ u i / u⌋

theorem kk_cast (u : ℚ) (i : Fin 4) : kk (u : ℝ) i = kkQ u i := by
  unfold kk kkQ
  rw [bpt_cast, ← Rat.cast_div, Rat.floor_cast]

/-- `ρ_i(u) = b_i − k_i(u) u`. -/
def rhoQ (u : ℚ) (i : Fin 4) : ℚ := bptQ u i - kkQ u i * u

theorem rho_cast (u : ℚ) (i : Fin 4) : rho (u : ℝ) i = (rhoQ u i : ℝ) := by
  unfold rho rhoQ
  rw [bpt_cast, kk_cast]; push_cast; ring

def lowQ (u : ℚ) (β : Fin 4 → Bool) (i : Fin 4) : ℚ := if β i then 0 else rhoQ u i

def upQ (u : ℚ) (β : Fin 4 → Bool) (i : Fin 4) : ℚ := if β i then rhoQ u i else u

def LQ (u : ℚ) (β : Fin 4 → Bool) : ℚ :=
  max (max (max (lowQ u β 0) (lowQ u β 1)) (lowQ u β 2)) (lowQ u β 3)

def RQ (u : ℚ) (β : Fin 4 → Bool) : ℚ :=
  min (min (min (upQ u β 0) (upQ u β 1)) (upQ u β 2)) (upQ u β 3)

/-- The length `max(R_β − L_β, 0)` of the gap with bit vector `β`. -/
def lenQ (u : ℚ) (β : Fin 4 → Bool) : ℚ := max (RQ u β - LQ u β) 0

theorem len_cast (u : ℚ) (β : Fin 4 → Bool) :
    max (Rbeta (u : ℝ) β - Lbeta (u : ℝ) β) 0 = (lenQ u β : ℝ) := by
  have hl : ∀ i, lowF (u : ℝ) β i = (lowQ u β i : ℝ) := fun i => by
    unfold lowF lowQ; split_ifs <;> simp [rho_cast]
  have hu : ∀ i, upF (u : ℝ) β i = (upQ u β i : ℝ) := fun i => by
    unfold upF upQ; split_ifs <;> simp [rho_cast]
  unfold Rbeta Lbeta lenQ RQ LQ
  simp only [hl, hu]
  push_cast
  rfl

/-! ### The type of a gap by interval counting -/

def nLo (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : ℤ := if β 0 then k 0 + 1 else k 0
def nHi (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : ℤ := if β 1 then k 1 else k 1 - 1
def zLo (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : ℤ := if β 2 then k 2 + 1 else k 2
def zHi (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : ℤ := if β 3 then k 3 else k 3 - 1

/-- **Computable type** `τ(k, β) = (N, z, h)`. -/
def tauC (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : CType :=
  ((nHi k β - nLo k β + 1).toNat, (zHi k β - zLo k β + 1).toNat,
    (min (nHi k β) (zLo k β - 2) - nLo k β + 1).toNat + (nHi k β - max (nLo k β) (zLo k β) + 1).toNat)

theorem ncard_Icc_int (a b : ℤ) : (Set.Icc a b).ncard = (b + 1 - a).toNat := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]

theorem tauN_eq (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : tauN k β = Set.Icc (nLo k β) (nHi k β) := by
  ext m
  simp only [tauN, nLo, nHi, Set.mem_setOf_eq, Set.mem_Icc]
  cases β 0 <;> cases β 1 <;> simp <;> omega

theorem tauZ_eq (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : tauZ k β = Set.Icc (zLo k β) (zHi k β) := by
  ext m
  simp only [tauZ, zLo, zHi, Set.mem_setOf_eq, Set.mem_Icc]
  cases β 2 <;> cases β 3 <;> simp <;> omega

theorem tauH_eq (k : Fin 4 → ℤ) (β : Fin 4 → Bool) :
    tauH k β = Set.Icc (nLo k β) (min (nHi k β) (zLo k β - 2)) ∪
      Set.Icc (max (nLo k β) (zLo k β)) (nHi k β) := by
  ext m
  simp only [tauH, tauN, nLo, nHi, zLo, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_union]
  cases β 0 <;> cases β 1 <;> cases β 2 <;> simp <;> omega

theorem tau_eq_tauC (k : Fin 4 → ℤ) (β : Fin 4 → Bool) : tau k β = tauC k β := by
  unfold tau tauC
  rw [tauN_eq, tauZ_eq, tauH_eq, ncard_Icc_int, ncard_Icc_int,
    Set.ncard_union_eq _ (Set.finite_Icc _ _) (Set.finite_Icc _ _), ncard_Icc_int, ncard_Icc_int]
  · congr 2 <;> ring_nf
  · rw [Set.disjoint_left]
    intro m h1 h2
    simp only [Set.mem_Icc] at h1 h2
    omega

/-! ### `Gpot` as a sum over the 16 gaps -/

theorem Gpot_eq_betaSum {u : ℝ} (hu : 0 < u) (ψ : CType → ℝ) :
    Gpot ψ u = ∑ β : Fin 4 → Bool, max (Rbeta u β - Lbeta u β) 0 * ψ (tau (kk u) β) := by
  classical
  set T := (Finset.univ : Finset (Fin 4 → Bool)).image (tau (kk u))
  unfold Gpot
  rw [finsum_eq_sum_of_support_subset (s := T)]
  · have : ∀ t ∈ T, meas u t * ψ t = ∑ β ∈ Finset.univ.filter (fun β => tau (kk u) β = t),
        max (Rbeta u β - Lbeta u β) 0 * ψ (tau (kk u) β) := by
      intro t _
      rw [meas_eq_sum hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [(Finset.mem_filter.1 hβ).2]
    rw [Finset.sum_congr rfl this]
    exact Finset.sum_fiberwise_of_maps_to (fun β _ => Finset.mem_image_of_mem _ (Finset.mem_univ β)) _
  · intro t ht
    rw [Function.mem_support] at ht
    have hm : meas u t ≠ 0 := fun h => ht (by rw [h, zero_mul])
    rw [meas_eq_sum hu] at hm
    obtain ⟨β, hβ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.coe_image]
    exact ⟨β, Finset.mem_coe.2 (Finset.mem_univ _), (Finset.mem_filter.1 hβ).2⟩

/-- The `n`-th bit vector, `n < 16`. -/
def betaOf (n : ℕ) : Fin 4 → Bool := fun i => n.testBit i.val

theorem betaOf_injOn : Set.InjOn betaOf ((Finset.range 16 : Finset ℕ) : Set ℕ) := by
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [betaOf] at h0 h1 h2 h3
  interval_cases a <;> interval_cases b <;> simp_all (config := { decide := true })

theorem image_betaOf : (Finset.range 16).image betaOf = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn betaOf_injOn]
  simp

theorem sum_beta_eq {M : Type*} [AddCommMonoid M] (f : (Fin 4 → Bool) → M) :
    ∑ β : Fin 4 → Bool, f β = ∑ n ∈ Finset.range 16, f (betaOf n) := by
  rw [← image_betaOf, Finset.sum_image betaOf_injOn]

/-! ### The computable bound for `g(λ, u, κ)` -/

/-- Key of a pair (type, `λ`) in the table of tangent points. -/
def pairKey (t : CType) (lam : ℤ) : ℕ := ((t.1 * 64 + t.2.1) * 64 + t.2.2) * 64 + lam.toNat

/-- The certified value of `ψ_t(λ)`, with tangent points looked up in `tab`. -/
def psiTab (tab : List (ℕ × ℕ)) (t : CType) (lam : ℤ) : ℤ :=
  psiHat t.1 t.2.1 t.2.2 lam (tab.lookup (pairKey t lam))

theorem psiT_le_psiTab (tab : List (ℕ × ℕ)) (t : CType) (lam : ℤ) :
    psiT t 0 (lam : ℝ) ≤ psiTab tab t lam :=
  psiT_le_psiHat t.1 t.2.1 t.2.2 lam _

/-- The contribution of the gap `β = betaOf n`. -/
def gapTerm (tab : List (ℕ × ℕ)) (u : ℚ) (lam : ℤ) (n : ℕ) : ℚ :=
  if lenQ u (betaOf n) = 0 then 0 else lenQ u (betaOf n) * psiTab tab (tauC (kkQ u) (betaOf n)) lam

/-- **Computable upper bound** for `Gpot ψ_λ u`. -/
def gpotQ (tab : List (ℕ × ℕ)) (u : ℚ) (lam : ℤ) : ℚ := ∑ n ∈ Finset.range 16, gapTerm tab u lam n

theorem Gpot_le_gpotQ (tab : List (ℕ × ℕ)) {u : ℚ} (hu : 0 < u) (lam : ℤ) :
    Gpot (fun t => psiT t 0 (lam : ℝ)) (u : ℝ) ≤ (gpotQ tab u lam : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  rw [Gpot_eq_betaSum hu', sum_beta_eq, gpotQ, Rat.cast_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [len_cast]
  unfold gapTerm
  have hk : kk (u : ℝ) = fun i => kkQ u i := funext (kk_cast u)
  rw [hk, tau_eq_tauC]
  split_ifs with h0
  · rw [h0]; simp
  · push_cast
    refine mul_le_mul_of_nonneg_left (psiT_le_psiTab tab _ lam) ?_
    exact_mod_cast le_max_right _ _

/-- **`g(λ, u, κ) ≤ λκ + gpotQ u λ`** for rational `u > 0` and integer `λ`. -/
theorem gfun_le_gpotQ (tab : List (ℕ × ℕ)) {u : ℚ} (hu : 0 < u) (lam : ℤ) (κ : ℝ) :
    gfun (lam : ℝ) (u : ℝ) κ ≤ lam * κ + (gpotQ tab u lam : ℝ) := by
  unfold gfun
  have := Gpot_le_gpotQ tab hu lam
  linarith

end Hankel2.CertC
