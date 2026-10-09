import RequestProject.Frame.Criterion
import RequestProject.Zeta7.Hankel2.LemmaTNv

/-!
# The negative Gauss valuation of multivariable polynomials (P, §7)

`nvMv p F = negTop (gaussValMv p F) = −min_m v_p([X^m] F) ∈ WithBot ℤ` (`⊥` iff `F = 0`).
Only the two properties used by the tree bound are needed: ultrametricity
(`nvMv_add_le`, `nvMv_sum_le`) and `nvMv (F G) ≤ nvMv F + nvMv G` (`nvMv_mul_le`, `nvMv_prod_le`).
The sublevel sets `{F | nvMv p F ≤ B}` are additive subgroups (`nvSub`).
This is the multivariable version of `Hankel2.nv`, for any prime `p` and any variable type.
-/

open Finset

namespace PadicWin

open Hankel2

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*}

/-- `nvMv p F = −v_p(F)`. -/
noncomputable def nvMv (p : ℕ) (F : MvPolynomial σ ℚ) : WithBot ℤ := negTop (gaussValMv p F)

theorem nvMv_le_iff (F : MvPolynomial σ ℚ) (T : ℤ) :
    nvMv p F ≤ (T : WithBot ℤ) ↔ ∀ m, ‖((F.coeff m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ T := by
  rw [nvMv, negTop_le_coe_iff, gaussValMv, Finset.le_inf_iff]
  simp only [norm_rat_le_zpow_iff, MvPolynomial.mem_support_iff, WithTop.coe_le_coe]
  constructor
  · intro h m
    by_cases hm : F.coeff m = 0
    · exact Or.inl hm
    · exact Or.inr (h m hm)
  · intro h m hm
    exact (h m).resolve_left hm

omit hp in
theorem nvMv_eq_bot_iff (F : MvPolynomial σ ℚ) : nvMv p F = ⊥ ↔ F = 0 := by
  constructor
  · intro h
    by_contra hF
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hF
    have hle : gaussValMv p F ≤ ((padicValRat p (F.coeff m) : ℤ) : WithTop ℤ) :=
      Finset.inf_le (MvPolynomial.mem_support_iff.2 hm)
    unfold nvMv at h
    revert h hle
    generalize gaussValMv p F = a
    cases a with
    | top => simp
    | coe a => simp [negTop]
  · rintro rfl; simp [nvMv, gaussValMv, negTop]

omit hp in
@[simp] theorem nvMv_zero : nvMv p (0 : MvPolynomial σ ℚ) = ⊥ := (nvMv_eq_bot_iff 0).2 rfl

omit hp in
theorem nvMv_le_of_forall {F : MvPolynomial σ ℚ} {B : WithBot ℤ}
    (h : ∀ T : ℤ, B ≤ (T : WithBot ℤ) → nvMv p F ≤ T) : nvMv p F ≤ B := by
  induction B with
  | bot =>
    by_contra hne
    rw [le_bot_iff] at hne
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    have := h (a - 1) bot_le
    rw [← ha, WithBot.coe_le_coe] at this
    omega
  | coe B => exact h B le_rfl

theorem nvMv_add_le (F G : MvPolynomial σ ℚ) : nvMv p (F + G) ≤ max (nvMv p F) (nvMv p G) := by
  refine nvMv_le_of_forall fun T hT => ?_
  rw [max_le_iff] at hT
  have h1 := (nvMv_le_iff F T).1 hT.1
  have h2 := (nvMv_le_iff G T).1 hT.2
  rw [nvMv_le_iff]
  intro i
  rw [MvPolynomial.coeff_add, Rat.cast_add]
  exact (Padic.nonarchimedean _ _).trans (max_le (h1 i) (h2 i))

theorem nvMv_neg (F : MvPolynomial σ ℚ) : nvMv p (-F) = nvMv p F := by
  refine le_antisymm (nvMv_le_of_forall fun T hT => ?_) (nvMv_le_of_forall fun T hT => ?_) <;>
    rw [nvMv_le_iff] at hT ⊢ <;> intro i <;>
    simpa [MvPolynomial.coeff_neg] using hT i

/-- The sublevel set `{F | nvMv p F ≤ B}` is an additive subgroup. -/
def nvSub (p : ℕ) [Fact p.Prime] (σ : Type*) (B : WithBot ℤ) : AddSubgroup (MvPolynomial σ ℚ) where
  carrier := {F | nvMv p F ≤ B}
  add_mem' {F G} hF hG := (nvMv_add_le F G).trans (max_le hF hG)
  zero_mem' := by simp
  neg_mem' {F} hF := by simpa [Set.mem_setOf_eq, nvMv_neg] using hF

theorem mem_nvSub {B : WithBot ℤ} {F : MvPolynomial σ ℚ} : F ∈ nvSub p σ B ↔ nvMv p F ≤ B :=
  Iff.rfl

theorem nvMv_sum_le {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) :
    nvMv p (∑ i ∈ s, F i) ≤ s.sup fun i => nvMv p (F i) :=
  (nvSub p σ _).sum_mem fun _ hi => le_sup (f := fun i => nvMv p (F i)) hi

theorem nvMv_mul_le (F G : MvPolynomial σ ℚ) : nvMv p (F * G) ≤ nvMv p F + nvMv p G := by
  refine nvMv_le_of_forall fun T hT => ?_
  induction h1 : nvMv p F with
  | bot => rw [nvMv_eq_bot_iff] at h1; subst h1; simp
  | coe a =>
    induction h2 : nvMv p G with
    | bot => rw [nvMv_eq_bot_iff] at h2; subst h2; simp
    | coe b =>
      rw [h1, h2, ← WithBot.coe_add, WithBot.coe_le_coe] at hT
      have hF := (nvMv_le_iff F a).1 h1.le
      have hG := (nvMv_le_iff G b).1 h2.le
      rw [nvMv_le_iff]
      intro i
      classical
      rw [MvPolynomial.coeff_mul, Rat.cast_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
      rw [Rat.cast_mul, norm_mul]
      calc ‖((F.coeff x.1 : ℚ) : ℚ_[p])‖ * ‖((G.coeff x.2 : ℚ) : ℚ_[p])‖
          ≤ (p : ℝ) ^ a * (p : ℝ) ^ b :=
            mul_le_mul (hF _) (hG _) (norm_nonneg _) (by positivity)
        _ = (p : ℝ) ^ (a + b) := by
            rw [zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
        _ ≤ (p : ℝ) ^ T :=
            zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) hT

theorem nvMv_C_le {a : ℚ} {T : ℤ} (h : ‖(a : ℚ_[p])‖ ≤ (p : ℝ) ^ T) :
    nvMv p (MvPolynomial.C a : MvPolynomial σ ℚ) ≤ T := by
  rw [nvMv_le_iff]
  intro i
  classical
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact h
  · simp; positivity

theorem nvMv_one : nvMv p (1 : MvPolynomial σ ℚ) ≤ 0 := by
  rw [← MvPolynomial.C_1]
  exact nvMv_C_le (by simp)

theorem nvMv_prod_le {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) :
    nvMv p (∏ i ∈ s, F i) ≤ ∑ i ∈ s, nvMv p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nvMv_one
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (nvMv_mul_le _ _).trans (add_le_add le_rfl ih)

end PadicWin
