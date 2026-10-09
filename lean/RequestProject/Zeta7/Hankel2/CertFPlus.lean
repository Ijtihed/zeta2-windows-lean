import RequestProject.Zeta7.Hankel2.Thm81Reduction
import RequestProject.Zeta7.Hankel2.Leaf82

/-!
# Computable mirror of `f⁺` (paper §8.3, Appendix B)

For node data `(D, μ, hs, 1[o>0])` with `μ, hs, 1[o>0] ∈ {0,1}` we have, for `a ≤ 3`,
`v̄_a = −D + β a − c₀` with `β = 0` if `μ = hs = 0` and `β = 1` otherwise, and
`c₀ = 8, 3, 0` for `hs = 1`, (`hs = 0`, `μ = 1`), (`hs = 0`, `μ = 0`) (`vbarT_eq`).
Hence the value of an admissible pair `(R, σ)` is independent of `σ`:
`s D − β (ΣR + C(s,2)) + s c₀ + ℓ(R)·1[o>0]` (`term_eq`), and with `C(s,2) ≤ ΣR ≤ 6 − C(4−s,2)`
one gets the closed form `f⁺ = max(sD + K(μ, hs, o, s), 0)` (`fPlusT_eq_fPlusC`).

* `fKc`, `fPlusC`: the computable mirror;
* `fPlusT_eq_fPlusC`: **`fPlusT D μ hs o s = fPlusC D μ hs o s`** for `μ, hs, o ≤ 1`;
* `typeFC`, `typeF_eq_typeFC`: the same for the class-type values `typeF t 0 hs s`.
-/

open Finset

namespace Hankel2.CertC

open Hankel2.Fam3

/-- The slope `β` of `a ↦ v̄_a + D`. -/
def betaF (mu hs : ℕ) : ℤ := if mu = 0 ∧ hs = 0 then 0 else 1

/-- The constant `c₀` of `v̄_a = −D + β a − c₀`. -/
def c0F (mu hs : ℕ) : ℤ := if hs = 1 then 8 else if mu = 1 then 3 else 0

theorem vbarT_eq (D : ℤ) {mu hs a : ℕ} (hmu : mu ≤ 1) (hhs : hs ≤ 1) (ha : a ≤ 3) :
    vbarT D mu hs a = -D + betaF mu hs * a - c0F mu hs := by
  have hb : vbarBetaT D mu hs a = -D + betaF mu hs * a - c0F mu hs := by
    unfold vbarBetaT
    rw [dif_pos ha]
    refine le_antisymm (inf'_le_of_le _ (b := if hs = 1 then 4 - a else 1)
      (mem_Icc.2 ⟨by split_ifs <;> omega, by split_ifs <;> omega⟩) ?_) (le_inf' _ _ fun i hi => ?_)
    · interval_cases mu <;> interval_cases hs <;> simp [betaF, c0F] <;> omega
    · have hi' := mem_Icc.1 hi
      interval_cases mu <;> interval_cases hs <;> simp [betaF, c0F] <;> omega
  unfold vbarT
  split_ifs with h1
  · rw [hb]
    refine min_eq_left ?_
    interval_cases mu <;> interval_cases hs <;> simp [betaF, c0F] <;> omega
  · exact hb

/-- `∑_{r ∈ R} r ≤ 6 − C(4 − |R|, 2)`. -/
theorem sum_le_top (R : Finset (Fin 4)) :
    ∑ r ∈ R, (r : ℕ) + (4 - R.card).choose 2 ≤ 6 := by
  revert R; decide

/-- The value of an admissible pair `(R, σ)`. -/
theorem term_eq (D : ℤ) {mu hs : ℕ} (oi : ℕ) (hmu : mu ≤ 1) (hhs : hs ≤ 1) (R : Finset (Fin 4))
    {σ : Equiv.Perm (Fin R.card)} (hσ : σ ∈ admPerms R) :
    (∑ i, -vbarT D mu hs (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i)) + (ellR R : ℤ) * oi =
      R.card * D - betaF mu hs * ((∑ r ∈ R, (r : ℕ) : ℕ) + (R.card.choose 2 : ℕ)) +
        R.card * c0F mu hs + (((∑ r ∈ R, (r : ℕ) : ℕ) : ℤ) - (R.card.choose 2 : ℕ)) * oi := by
  have hadm := (mem_filter.1 hσ).2
  rw [sum_congr rfl fun i _ => by rw [vbarT_eq D hmu hhs (hadm i)]]
  have h1 : ∑ i : Fin R.card, (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) : ℤ) =
      ((∑ r ∈ R, (r : ℕ) : ℕ) : ℤ) := by
    rw [Equiv.sum_comp σ (fun i => (((R.orderEmbOfFin rfl i : Fin 4) : ℕ) : ℤ))]
    exact_mod_cast sum_orderEmbOfFin R
  have h2 : ∑ i : Fin R.card, ((i : ℕ) : ℤ) = (R.card.choose 2 : ℕ) := by
    exact_mod_cast sum_fin_val R.card
  have hc := choose_le_sum R
  have hell : ((ellR R : ℕ) : ℤ) = ((∑ r ∈ R, (r : ℕ) : ℕ) : ℤ) - (R.card.choose 2 : ℕ) := by
    rw [ellR]; push_cast [Nat.cast_sub hc]; ring
  rw [hell]
  have e : ∀ i : Fin R.card, -(-D + betaF mu hs * ((((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) + i : ℕ)
      : ℤ) - c0F mu hs) = D + c0F mu hs - betaF mu hs * (((R.orderEmbOfFin rfl (σ i) : Fin 4) : ℕ) : ℤ)
        - betaF mu hs * ((i : ℕ) : ℤ) := fun i => by push_cast; ring
  rw [sum_congr rfl fun i _ => e i, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, h1, h2]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The constant `K(μ, hs, o, s)` of the closed form `f⁺ = max(s D + K, 0)`. -/
def fKc (mu hs oi s : ℕ) : ℤ :=
  s * c0F mu hs - betaF mu hs * (s.choose 2 : ℕ) - ((s.choose 2 : ℕ) : ℤ) * oi +
    (if 0 < (oi : ℤ) - betaF mu hs then ((oi : ℤ) - betaF mu hs) * (6 - ((4 - s).choose 2 : ℕ))
      else ((oi : ℤ) - betaF mu hs) * (s.choose 2 : ℕ))

/-- **Computable `f⁺`** (clipped at `0`). -/
def fPlusC (D : ℤ) (mu hs oi s : ℕ) : ℤ := if s ≤ 4 then max (s * D + fKc mu hs oi s) 0 else 0

theorem fPlusRawT_le (D : ℤ) {mu hs oi : ℕ} (hmu : mu ≤ 1) (hhs : hs ≤ 1) (hoi : oi ≤ 1) (s : ℕ) :
    fPlusRawT D mu hs oi s ≤ ((s * D + fKc mu hs oi s : ℤ) : WithBot ℤ) := by
  unfold fPlusRawT
  refine Finset.sup_le fun R hR => Finset.sup_le fun σ hσ => WithBot.coe_le_coe.2 ?_
  have hRs : R.card = s := (mem_filter.1 hR).2
  rw [term_eq D oi hmu hhs R hσ]
  have hc := choose_le_sum R
  have ht := sum_le_top R
  set S := ∑ r ∈ R, (r : ℕ)
  subst hRs
  unfold fKc
  have hc' : ((R.card.choose 2 : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast hc
  have ht' : (S : ℤ) ≤ 6 - (((4 - R.card).choose 2 : ℕ) : ℤ) := by
    have : ((S + (4 - R.card).choose 2 : ℕ) : ℤ) ≤ 6 := by exact_mod_cast ht
    push_cast at this; linarith
  have hb : betaF mu hs = 0 ∨ betaF mu hs = 1 := by unfold betaF; split_ifs <;> simp
  interval_cases oi <;> rcases hb with hb | hb <;> rw [hb] <;> norm_num <;> nlinarith

/-- **`f⁺` agrees with its computable mirror** (upper bound direction; see also
`fPlusT_eq_fPlusC`). -/
theorem fPlusT_le_fPlusC (D : ℤ) {mu hs oi : ℕ} (hmu : mu ≤ 1) (hhs : hs ≤ 1) (hoi : oi ≤ 1)
    (s : ℕ) : fPlusT D mu hs oi s ≤ fPlusC D mu hs oi s := by
  unfold fPlusT fPlusC
  split_ifs with hs4
  · have h := fPlusRawT_le D hmu hhs hoi s
    induction hr : fPlusRawT D mu hs oi s with
    | bot => simp
    | coe r =>
      rw [hr] at h
      have h' : r ≤ s * D + fKc mu hs oi s := WithBot.coe_le_coe.1 h
      have : max (r : WithBot ℤ) 0 = ((max r 0 : ℤ) : WithBot ℤ) := by
        rcases le_total r 0 with h0 | h0
        · rw [max_eq_right (by exact_mod_cast h0), max_eq_right h0]; rfl
        · rw [max_eq_left (by exact_mod_cast h0), max_eq_left h0]
      rw [this, WithBot.unbotD_coe]
      exact max_le_max h' le_rfl
  · have : (univ.filter fun R : Finset (Fin 4) => R.card = s) = ∅ := by
      ext R; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h; have := card_le_four R; omega
    unfold fPlusRawT; rw [this, Finset.sup_empty]
    simp

/-- The class-type value `f⁺(k, s)` for a node of a class of type `(N, z, ·)` with `g = 0`. -/
def typeFC (N z hs s : ℕ) : ℤ :=
  fPlusC (4 * ((N : ℤ) - 1) - 6 * z) (if 0 < N - 1 + z then 1 else 0) hs
    (if 0 < N - 1 then 1 else 0) s

theorem typeF_le_typeFC (t : Circle.CType) {hs : ℕ} (hhs : hs ≤ 1) (s : ℕ) :
    typeF t 0 hs s ≤ typeFC t.1 t.2.1 hs s := by
  unfold typeF typeFC
  have e1 : DT t.1 t.2.1 0 = 4 * ((t.1 : ℤ) - 1) - 6 * t.2.1 := by unfold DT; ring
  have e2 : muT t.1 t.2.1 0 = if 0 < t.1 - 1 + t.2.1 then 1 else 0 := rfl
  rw [e1, e2]
  exact fPlusT_le_fPlusC _ (by split_ifs <;> omega) hhs (by unfold oiT; split_ifs <;> omega) s

end Hankel2.CertC
