import RequestProject.Zeta7.Hankel2.CertDP

/-!
# Cheap certified upper bounds for `ψ_t(λ)` (Appendix B)

The knapsack mirror `psiC` (`CertDP.lean`) is exact but too expensive for kernel evaluation on
all types.  For the certificate we use two *closed-form* upper bounds, both valid for every
integer `λ`:

* **tangent (dual) bound** `psiDual`: for `μ = m/2 ≥ 0`, `−S² ≤ −2μ S + μ²`, hence
  `ψ_t(λ) ≤ h·max_s (w₁(s) − (λ+m) s) + (N−h)·max_s (w₀(s) − (λ+m) s) + ⌊m²/4⌋`
  (`w_hs(s) = f⁺(s) + s²`; the floor is legitimate because `ψ_t(λ)` is a maximum of integers);
* **crude bound** `psiCrude`: `∑ s_k² ≤ S²`, hence
  `ψ_t(λ) ≤ h·max_s (f⁺₁(s) − λ s) + (N−h)·max_s (f⁺₀(s) − λ s)` (exact for `N ≤ 1`).

`psiT_le_dual`, `psiT_le_crude`.
-/

open Finset

namespace Hankel2.CertC

open Hankel2.Fam3

/-- `max_{0 ≤ s ≤ 4} (f s − ℓ s)`. -/
def max5 (f : ℕ → ℤ) (l : ℤ) : ℤ :=
  max (max (max (max (f 0) (f 1 - l)) (f 2 - 2 * l)) (f 3 - 3 * l)) (f 4 - 4 * l)

theorem le_max5 (f : ℕ → ℤ) (l : ℤ) (j : Fin 5) : f j - (j : ℕ) * l ≤ max5 f l := by
  unfold max5
  fin_cases j <;> simp

/-- The tangent (dual) bound, with `μ = m/2`. -/
def psiDual (N z h : ℕ) (lam : ℤ) (m : ℕ) : ℤ :=
  h * max5 (wNode N z 1) (lam + m) + ((N - h : ℕ) : ℤ) * max5 (wNode N z 0) (lam + m) +
    ((m : ℤ) * m) / 4

/-- The crude bound. -/
def psiCrude (N z h : ℕ) (lam : ℤ) : ℤ :=
  h * max5 (typeFC N z 1) lam + ((N - h : ℕ) : ℤ) * max5 (typeFC N z 0) lam

/-- `∑_j j² c_j ≤ (∑_j j c_j)²` for natural `c_j`. -/
theorem sq_sum_le (c : Fin 5 → ℕ) :
    ∑ j : Fin 5, ((j : ℕ) : ℤ) ^ 2 * c j ≤ (∑ j : Fin 5, ((j : ℕ) : ℤ) * c j) ^ 2 := by
  simp only [Fin.sum_univ_five]
  have h : ∀ j, (0 : ℤ) ≤ (c j : ℤ) * ((c j : ℤ) - 1) := fun j => by
    rcases Nat.eq_zero_or_pos (c j) with h0 | h0
    · simp [h0]
    · have : (1 : ℤ) ≤ c j := by exact_mod_cast h0
      nlinarith
  have p : ∀ i j, (0 : ℤ) ≤ (c i : ℤ) * c j := fun i j => by positivity
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at *
  norm_num
  nlinarith [h 0, h 1, h 2, h 3, h 4, p 1 2, p 1 3, p 1 4, p 2 3, p 2 4, p 3 4]

/-- The objective `cvF − S² − λ S` of a count vector is bounded by the weights. -/
theorem cvF_le (N z h : ℕ) (ab : (Fin 5 → ℕ) × (Fin 5 → ℕ)) :
    cvF (N, z, h) 0 ab ≤ ∑ j : Fin 5, ((ab.1 j : ℤ) * wNode N z 1 j + (ab.2 j : ℤ) * wNode N z 0 j) := by
  refine sum_le_sum fun j _ => ?_
  have e1 := typeF_le_typeFC (N, z, h) (hs := 1) le_rfl j
  have e0 := typeF_le_typeFC (N, z, h) (hs := 0) (by norm_num) j
  simp only [wNode]
  have p1 : (0 : ℤ) ≤ ab.1 j := Nat.cast_nonneg _
  have p2 : (0 : ℤ) ≤ ab.2 j := Nat.cast_nonneg _
  nlinarith

theorem sum_le_card_mul (a : Fin 5 → ℕ) (g : ℕ → ℤ) (l : ℤ) :
    ∑ j : Fin 5, (a j : ℤ) * (g j - (j : ℕ) * l) ≤ ((∑ j, a j : ℕ) : ℤ) * max5 g l := by
  push_cast
  rw [sum_mul]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max5 g l j) (Nat.cast_nonneg _)

theorem psiT_le_of_int {t : Circle.CType} {lam : ℤ} {B : ℤ}
    (h : ∀ ab ∈ cntVecs t.1 t.2.2, cvF t 0 ab - (cvS ab : ℤ) ^ 2 - lam * cvS ab ≤ B) :
    psiT t 0 (lam : ℝ) ≤ B := by
  unfold psiT
  refine Finset.sup'_le _ _ fun ab hab => ?_
  have := (Int.cast_le (R := ℝ)).2 (h ab hab)
  push_cast at this ⊢
  linarith

/-- **The tangent bound.** -/
theorem psiT_le_dual (N z h : ℕ) (lam : ℤ) (m : ℕ) :
    psiT (N, z, h) 0 (lam : ℝ) ≤ psiDual N z h lam m := by
  refine psiT_le_of_int fun ab hab => ?_
  obtain ⟨-, ha, hb⟩ := Finset.mem_filter.1 hab
  dsimp only at ha hb
  have hF := cvF_le N z h ab
  have hS : ((cvS ab : ℕ) : ℤ) = ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.1 j + ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.2 j := by
    simp only [cvS, ← sum_add_distrib]; push_cast; exact sum_congr rfl fun j _ => by ring
  have h1 := sum_le_card_mul ab.1 (wNode N z 1) (lam + m)
  have h2 := sum_le_card_mul ab.2 (wNode N z 0) (lam + m)
  rw [ha] at h1
  rw [hb] at h2
  unfold psiDual
  set X : ℤ := h * max5 (wNode N z 1) (lam + m) + ((N - h : ℕ) : ℤ) * max5 (wNode N z 0) (lam + m)
  set S : ℤ := ((cvS ab : ℕ) : ℤ)
  have e1 : ∑ j : Fin 5, (ab.1 j : ℤ) * (wNode N z 1 j - (j : ℕ) * (lam + m)) =
      ∑ j : Fin 5, (ab.1 j : ℤ) * wNode N z 1 j - (lam + m) * ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.1 j := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have e2 : ∑ j : Fin 5, (ab.2 j : ℤ) * (wNode N z 0 j - (j : ℕ) * (lam + m)) =
      ∑ j : Fin 5, (ab.2 j : ℤ) * wNode N z 0 j - (lam + m) * ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.2 j := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  rw [sum_add_distrib] at hF
  have hlin : cvF (N, z, h) 0 ab - lam * S - X ≤ m * S := by
    rw [e1] at h1; rw [e2] at h2; rw [hS]; linarith
  have key : (cvF (N, z, h) 0 ab - S ^ 2 - lam * S - X) * 4 ≤ (m : ℤ) * m := by
    nlinarith [sq_nonneg (2 * S - m)]
  have := (Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 4)).2 key
  linarith

/-- **The crude bound.** -/
theorem psiT_le_crude (N z h : ℕ) (lam : ℤ) :
    psiT (N, z, h) 0 (lam : ℝ) ≤ psiCrude N z h lam := by
  refine psiT_le_of_int fun ab hab => ?_
  obtain ⟨-, ha, hb⟩ := Finset.mem_filter.1 hab
  dsimp only at ha hb
  have hS : ((cvS ab : ℕ) : ℤ) = ∑ j : Fin 5, ((j : ℕ) : ℤ) * (ab.1 j + ab.2 j : ℕ) := by
    simp only [cvS]; push_cast; rfl
  have hsq := sq_sum_le (fun j => ab.1 j + ab.2 j)
  have h1 := sum_le_card_mul ab.1 (typeFC N z 1) lam
  have h2 := sum_le_card_mul ab.2 (typeFC N z 0) lam
  rw [ha] at h1
  rw [hb] at h2
  have hF : cvF (N, z, h) 0 ab ≤ ∑ j : Fin 5, ((ab.1 j : ℤ) * typeFC N z 1 j +
      (ab.2 j : ℤ) * typeFC N z 0 j + ((j : ℕ) : ℤ) ^ 2 * (ab.1 j + ab.2 j : ℕ)) := by
    refine sum_le_sum fun j _ => ?_
    have e1 := typeF_le_typeFC (N, z, h) (hs := 1) le_rfl j
    have e0 := typeF_le_typeFC (N, z, h) (hs := 0) (by norm_num) j
    have p1 : (0 : ℤ) ≤ ab.1 j := Nat.cast_nonneg _
    have p2 : (0 : ℤ) ≤ ab.2 j := Nat.cast_nonneg _
    push_cast
    nlinarith
  rw [sum_add_distrib, sum_add_distrib] at hF
  have e1 : ∑ j : Fin 5, (ab.1 j : ℤ) * (typeFC N z 1 j - (j : ℕ) * lam) =
      ∑ j : Fin 5, (ab.1 j : ℤ) * typeFC N z 1 j - lam * ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.1 j := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have e2 : ∑ j : Fin 5, (ab.2 j : ℤ) * (typeFC N z 0 j - (j : ℕ) * lam) =
      ∑ j : Fin 5, (ab.2 j : ℤ) * typeFC N z 0 j - lam * ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.2 j := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have e3 : ∑ j : Fin 5, ((j : ℕ) : ℤ) * (ab.1 j + ab.2 j : ℕ) =
      ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.1 j + ∑ j : Fin 5, ((j : ℕ) : ℤ) * ab.2 j := by
    rw [← sum_add_distrib]; push_cast; exact sum_congr rfl fun j _ => by ring
  unfold psiCrude
  rw [hS] at *
  push_cast at hsq hF e3 ⊢
  rw [e3] at hsq ⊢
  linarith

/-- **The certified value of `ψ_t(λ)`**: the minimum of the two bounds (the tangent point `m`
is supplied by the certificate). -/
def psiHat (N z h : ℕ) (lam : ℤ) (m : Option ℕ) : ℤ :=
  match m with
  | some m => min (psiDual N z h lam m) (psiCrude N z h lam)
  | none => psiCrude N z h lam

theorem psiT_le_psiHat (N z h : ℕ) (lam : ℤ) (m : Option ℕ) :
    psiT (N, z, h) 0 (lam : ℝ) ≤ psiHat N z h lam m := by
  unfold psiHat
  cases m with
  | none => exact psiT_le_crude N z h lam
  | some m =>
    push_cast
    exact le_min (psiT_le_dual N z h lam m) (psiT_le_crude N z h lam)

end Hankel2.CertC
