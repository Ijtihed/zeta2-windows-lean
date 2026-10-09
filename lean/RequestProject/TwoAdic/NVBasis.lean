import RequestProject.TwoAdic.NVLocal
import RequestProject.Zeta7.Hankel2.NVFamily3

/-!
# II, Lemma 6.3 (the basis dual to the jets at the affected nodes)

`E_x`, `x = (k, j₀)` with `k ∈ 𝒜` and `j₀ < q`, is the basis of `ℚ[x]_{<qn}` dual to the jets of
order `< q` at the points `−k`, `k ∈ 𝒜` (`exists_basis`; the confluent Vandermonde is an `ℓ`-unit
because the affected nodes are pairwise incongruent modulo `ℓ`).  Its coefficients are `ℓ`-integral,
and its jets satisfy:

* `jet_int`: every jet at an integer point is `ℓ`-integral;
* `jet_partner`: at every node `k` with `n/2 + 1 ≤ |k|` (affected nodes and partners),
  `v_ℓ((E_x)_b(k)) ≥ j₀ − b` (at a partner, by the Taylor shift by `±ℓ` from its mate).
-/

open Polynomial Finset PadicWin

namespace TwoAdicWin.Dom

variable {q d n ℓ : ℕ}

/-- The index set `x = (k, j₀)`, `k ∈ 𝒜`, `j₀ < q`. -/
abbrev HIdx (q n : ℕ) := Σ _ : ↥(aff n), Fin q

theorem card_HIdx (h : Hyp q d n ℓ) : Fintype.card (HIdx q n) = q * n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_coe, card_aff h, mul_comm]

theorem aff_inj_zmod (h : Hyp q d n ℓ) :
    Function.Injective (fun i : ↥(aff n) => (((-(i : ℤ)) : ℤ) : ZMod ℓ)) := by
  intro i i' heq
  simp only at heq
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 heq
  apply Subtype.ext
  have := aff_inj_mod h i.2 i'.2 (by
    have : (i : ℤ) - i' = -(-(i : ℤ) - -(i' : ℤ)) := by ring
    rw [this]; exact (dvd_neg).2 (by
      have : -(i : ℤ) - -(i' : ℤ) = -(-(i' : ℤ) - -(i : ℤ)) := by ring
      rw [this]; exact (dvd_neg).2 hd))
  exact this

theorem exists_basis (h : Hyp q d n ℓ) :
    haveI := Fact.mk h.prime
    ∃ E : HIdx q n → ℚ[X],
      (∀ x (i : ↥(aff n)) j (hj : j < q),
        Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0) ∧
      (∀ x m, padicNorm ℓ ((E x).coeff m) ≤ 1) ∧
      (∀ x m, Fintype.card (HIdx q n) ≤ m → (E x).coeff m = 0) := by
  haveI := Fact.mk h.prime
  obtain ⟨E, h1, h2, h3, _⟩ := Hankel2.W3.exists_dual_hermite_basis (p := ℓ)
    (fun i : ↥(aff n) => -(i : ℤ)) (aff_inj_zmod h) (fun _ => q)
  refine ⟨E, fun x i j hj => ?_, h2, h3⟩
  have := h1 x i j hj
  unfold Pjet PF.Pjet
  rw [show (-((i : ℤ) : ℚ)) = (((-(i : ℤ)) : ℤ) : ℚ) by push_cast; ring]
  exact this

variable [Fact ℓ.Prime]

theorem jet_int (E : HIdx q n → ℚ[X]) (hE2 : ∀ x m, padicNorm ℓ ((E x).coeff m) ≤ 1)
    (x : HIdx q n) (k : ℤ) (b : ℕ) : VB ℓ (Pjet (E x) k b) 0 := by
  unfold Pjet PF.Pjet VB
  rw [show (-((k : ℤ) : ℚ)) = (((-k : ℤ)) : ℚ) by push_cast; ring]
  simpa using Hankel2.W3.Fam3.padicNorm_jet_le_one (p := ℓ) (E x) (hE2 x) _ b

/-- **II, Lemma 6.3 (jets)**: `v_ℓ((E_x)_b(k)) ≥ j₀ − b` at the affected nodes and the partners. -/
theorem jet_partner (h : Hyp q d n ℓ) (E : HIdx q n → ℚ[X])
    (hE1 : ∀ x (i : ↥(aff n)) j (hj : j < q),
      Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
    (hE2 : ∀ x m, padicNorm ℓ ((E x).coeff m) ≤ 1)
    (x : HIdx q n) {k : ℤ} (hk : k ∈ nodes n) (hk1 : n / 2 + 1 ≤ k.natAbs) {b : ℕ} (hb : b < q) :
    VB ℓ (Pjet (E x) k b) ((x.2 : ℤ) - b) := by
  by_cases hka : k ∈ aff n
  · -- an affected node: the jet is `δ`
    rw [show k = ((⟨k, hka⟩ : ↥(aff n)) : ℤ) from rfl, hE1 x ⟨k, hka⟩ b hb]
    split_ifs with hx
    · rw [hx]; simpa using (VB_one (ℓ := ℓ))
    · exact VB_zero _
  · -- a partner: Taylor shift from the mate
    have hk2 : k.natAbs ≤ n := by
      rw [mem_aff_iff] at hka; push_neg at hka; exact Nat.lt_succ_iff.1 (hka hk)
    have hma := mate_mem_aff h hk hk1 hk2
    obtain ⟨_, _, hmd, _⟩ := mate_spec h hk hk1
    set i : ↥(aff n) := ⟨mate ℓ k, hma⟩
    set N : ℕ := if x.1 = i then (x.2 : ℕ) else q with hN
    have hint : ∀ m, padicNorm ℓ ((hasseDeriv m (E x)).eval (((-(i : ℤ)) : ℤ) : ℚ)) ≤ 1 :=
      fun m => Hankel2.W3.Fam3.padicNorm_jet_le_one (p := ℓ) (E x) (hE2 x) _ m
    have hvan : ∀ m < N, (hasseDeriv m (E x)).eval (((-(i : ℤ)) : ℤ) : ℚ) = 0 := by
      intro m hm
      have hmq : m < q := by
        rw [hN] at hm; split_ifs at hm
        · exact lt_trans hm x.2.isLt
        · exact hm
      have := hE1 x i m hmq
      unfold Pjet PF.Pjet at this
      rw [show (((-(i : ℤ)) : ℤ) : ℚ) = -((i : ℤ) : ℚ) by push_cast; ring, this, if_neg]
      rintro rfl
      rw [hN] at hm
      simp at hm
    have hd : padicNorm ℓ (((i : ℤ) - k : ℤ) : ℚ) ≤ (ℓ : ℚ)⁻¹ := by
      rw [padicNorm_int_pm (by simp only [i]; omega)]
    have hs := Hankel2.W3.padicNorm_jet_shift_le (p := ℓ) (E x) (((-(i : ℤ)) : ℤ) : ℚ)
      (((i : ℤ) - k : ℤ) : ℚ) N b hint hvan hd
    have e : (((-(i : ℤ)) : ℤ) : ℚ) + (((i : ℤ) - k : ℤ) : ℚ) = -((k : ℤ) : ℚ) := by
      push_cast; ring
    rw [e] at hs
    unfold VB Pjet PF.Pjet
    refine hs.trans (zpow_le_zpow_right₀ (one_lt_ell (ℓ := ℓ)).le ?_)
    have : (x.2 : ℕ) ≤ N := by
      rw [hN]; split_ifs
      · exact le_rfl
      · exact x.2.isLt.le
    omega

end TwoAdicWin.Dom
