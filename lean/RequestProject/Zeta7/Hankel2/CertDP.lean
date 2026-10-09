import RequestProject.Zeta7.Hankel2.CertFPlus

/-!
# Computable class values `V_t(S)` and `ψ_t(λ)` (knapsack), paper §8.3

* `dpA w k`: the knapsack table `A_k(S) = max_{s_1+⋯+s_k = S, s_i ≤ 4} ∑ w(s_i)` (`dpA_sound`);
* `conv`: max-plus convolution of lists (`conv_ge`);
* `convC N z h`, `vlistC N z h`: `V_t(S) + S²` and `V_t(S)` for the type `t = (N, z, h)` (the `h`
  `hs`-nodes and the `N − h` other nodes are combined by a max-plus convolution), as `V_of_nodes`
  of the ζ₂(7) certificate checker;
* `psiC N z h λ = max_S (V_t(S) − λ S)`;
* **`psiT_le_psiC`**: `ψ_t(λ) ≤ psiC t λ` for every integer `λ`.
-/

open Finset

namespace Hankel2.CertC

open Hankel2.Fam3

/-- The "minus infinity" sentinel of the tables. -/
def NEG : ℤ := -1000000000

/-- Max-plus convolution: `(conv A B)(k) = max_{i + j = k} A(i) + B(j)`. -/
def conv : List ℤ → List ℤ → List ℤ
  | [], B => List.replicate (B.length - 1) NEG
  | a :: A, B => List.zipWith max (B.map (· + a) ++ List.replicate A.length NEG) (NEG :: conv A B)

theorem length_conv (A B : List ℤ) (hB : B ≠ []) : (conv A B).length = A.length + B.length - 1 := by
  have hB1 : 1 ≤ B.length := List.length_pos_iff.2 hB
  induction A with
  | nil => simp [conv]
  | cons a A ih => simp only [conv, List.length_zipWith, List.length_append, List.length_map,
      List.length_replicate, List.length_cons, ih]; omega

/-- **Soundness of the convolution.** -/
theorem conv_ge (A B : List ℤ) {i j : ℕ} (hi : i < A.length) (hj : j < B.length) :
    A.getD i 0 + B.getD j 0 ≤ (conv A B).getD (i + j) 0 := by
  have hB : B ≠ [] := List.ne_nil_of_length_pos (by omega)
  induction A generalizing i with
  | nil => simp at hi
  | cons a A ih =>
    have hl := length_conv A B hB
    have hlt : i + j < (conv (a :: A) B).length := by
      rw [length_conv _ _ hB]; simp only [List.length_cons] at hi ⊢; omega
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [conv, List.getElem_zipWith]
    rcases i with _ | i
    · refine le_trans ?_ (le_max_left _ _)
      simp only [Nat.zero_add, List.getD_cons_zero]
      rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getD_eq_getElem _ _ hj]
      linarith
    · refine le_trans ?_ (le_max_right _ _)
      simp only [List.length_cons] at hi
      have := ih (i := i) (by omega)
      rw [List.getD_eq_getElem (l := conv A B) _ (by rw [hl]; omega)] at this
      simpa [show i + 1 + j = (i + j) + 1 by omega] using this

/-- The knapsack table for `k` identical items with values `w 0, …, w 4`. -/
def dpA (w : ℕ → ℤ) : ℕ → List ℤ
  | 0 => [0]
  | k + 1 => conv (dpA w k) [w 0, w 1, w 2, w 3, w 4]

theorem length_dpA (w : ℕ → ℤ) (k : ℕ) : (dpA w k).length = 4 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dpA, length_conv _ _ (by simp), ih]; simp; ring

/-- **Soundness of the knapsack table.** -/
theorem dpA_sound (w : ℕ → ℤ) (L : List ℕ) (hL : ∀ x ∈ L, x ≤ 4) :
    (L.map w).sum ≤ (dpA w L.length).getD L.sum 0 ∧ L.sum ≤ 4 * L.length := by
  induction L with
  | nil => simp [dpA]
  | cons x L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hx := hL x List.mem_cons_self
    have hlen := length_dpA w L.length
    refine ⟨?_, by simp only [List.sum_cons, List.length_cons]; omega⟩
    simp only [List.map_cons, List.sum_cons, List.length_cons, dpA]
    have h := conv_ge (dpA w L.length) [w 0, w 1, w 2, w 3, w 4] (i := L.sum) (j := x)
      (by omega) (by simp; omega)
    have hw : [w 0, w 1, w 2, w 3, w 4].getD x 0 = w x := by
      interval_cases x <;> rfl
    rw [hw, add_comm L.sum x] at h
    linarith

/-- `max(m, max_{i} (C(i) − (S₀+i)² − λ (S₀+i)))`. -/
def psiAux (lam : ℤ) : ℕ → List ℤ → ℤ → ℤ
  | _, [], m => m
  | S, c :: cs, m => psiAux lam (S + 1) cs (max m (c - (S : ℤ) ^ 2 - lam * S))

theorem psiAux_ge_init (lam : ℤ) (S : ℕ) (C : List ℤ) (m : ℤ) : m ≤ psiAux lam S C m := by
  induction C generalizing S m with
  | nil => exact le_rfl
  | cons c C ih => exact le_trans (le_max_left _ _) (ih _ _)

theorem psiAux_ge (lam : ℤ) (S : ℕ) (C : List ℤ) (m : ℤ) {i : ℕ} (hi : i < C.length) :
    C.getD i 0 - ((S + i : ℕ) : ℤ) ^ 2 - lam * ((S + i : ℕ) : ℤ) ≤ psiAux lam S C m := by
  induction C generalizing S m i with
  | nil => simp at hi
  | cons c C ih =>
    rcases i with _ | i
    · simp only [List.getD_cons_zero, Nat.add_zero, psiAux]
      exact le_trans (le_max_right _ _) (psiAux_ge_init _ _ _ _)
    · simp only [List.getD_cons_succ, psiAux]
      have := ih (S + 1) (max m (c - (S : ℤ) ^ 2 - lam * S)) (i := i)
        (by simp only [List.length_cons] at hi; omega)
      rwa [show S + 1 + i = S + (i + 1) by omega] at this

/-- The node weight `f⁺(s) + s²` of an `hs`-node (`hs = 1`) or of another node (`hs = 0`). -/
def wNode (N z hs : ℕ) (s : ℕ) : ℤ := typeFC N z hs s + (s : ℤ) ^ 2

/-- **Computable class values** `C_t(S) = V_t(S) + S²` for the type `t = (N, z, h)` (`g = 0`). -/
def convC (N z h : ℕ) : List ℤ := conv (dpA (wNode N z 1) h) (dpA (wNode N z 0) (N - h))

/-- `V_t(S) = C_t(S) − S²`, as in the ζ₂(7) certificate checker. -/
def vlistC (N z h : ℕ) : List ℤ := (convC N z h).zipIdx.map fun p => p.1 - (p.2 : ℤ) ^ 2

/-- **Computable** `ψ_t(λ) = max_S (V_t(S) − λ S)`. -/
def psiC (N z h : ℕ) (lam : ℤ) : ℤ := psiAux lam 0 (convC N z h) NEG

/-- The list with `a j` copies of `j`, `j = 0, …, 4`. -/
def cntList (a : Fin 5 → ℕ) : List ℕ :=
  List.replicate (a 0) 0 ++ List.replicate (a 1) 1 ++ List.replicate (a 2) 2 ++
    List.replicate (a 3) 3 ++ List.replicate (a 4) 4

theorem cntList_le (a : Fin 5 → ℕ) : ∀ x ∈ cntList a, x ≤ 4 := by
  intro x hx
  simp only [cntList, List.mem_append, List.mem_replicate] at hx
  omega

theorem cntList_length (a : Fin 5 → ℕ) : (cntList a).length = ∑ j, a j := by
  simp [cntList, Fin.sum_univ_five]; ring

theorem cntList_sum (a : Fin 5 → ℕ) : (cntList a).sum = ∑ j : Fin 5, (j : ℕ) * a j := by
  simp [cntList, Fin.sum_univ_five]; ring

theorem cntList_map (a : Fin 5 → ℕ) (w : ℕ → ℤ) :
    ((cntList a).map w).sum = ∑ j : Fin 5, (a j : ℤ) * w j := by
  simp [cntList, Fin.sum_univ_five, List.map_replicate, List.sum_replicate]; ring

/-- **`ψ_t(λ)` is bounded by its computable mirror.** -/
theorem psiT_le_psiC (N z h : ℕ) (lam : ℤ) :
    psiT (N, z, h) 0 (lam : ℝ) ≤ (psiC N z h lam : ℝ) := by
  unfold psiT
  refine Finset.sup'_le _ _ fun ab hab => ?_
  obtain ⟨-, ha, hb⟩ := Finset.mem_filter.1 hab
  dsimp only at ha hb
  set A := dpA (wNode N z 1) h
  set B := dpA (wNode N z 0) (N - h)
  have hA := dpA_sound (wNode N z 1) (cntList ab.1) (cntList_le _)
  have hB := dpA_sound (wNode N z 0) (cntList ab.2) (cntList_le _)
  rw [cntList_length, ha] at hA
  rw [cntList_length, hb] at hB
  rw [cntList_map, cntList_sum] at hA hB
  set S1 := ∑ j : Fin 5, (j : ℕ) * ab.1 j
  set S2 := ∑ j : Fin 5, (j : ℕ) * ab.2 j
  have hS : cvS ab = S1 + S2 := by
    simp only [cvS, S1, S2, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hlA : A.length = 4 * h + 1 := length_dpA _ _
  have hlB : B.length = 4 * (N - h) + 1 := length_dpA _ _
  -- `cvF ≤ A(S₁) + B(S₂)`
  have hF : cvF (N, z, h) 0 ab ≤ A.getD S1 0 + B.getD S2 0 := by
    refine le_trans ?_ (add_le_add hA.1 hB.1)
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have e1 := typeF_le_typeFC (N, z, h) (hs := 1) le_rfl j
    have e0 := typeF_le_typeFC (N, z, h) (hs := 0) (by norm_num) j
    simp only [wNode]
    have p1 : (0 : ℤ) ≤ ab.1 j := Nat.cast_nonneg _
    have p2 : (0 : ℤ) ≤ ab.2 j := Nat.cast_nonneg _
    nlinarith
  -- `A(S₁) + B(S₂) ≤ C(S₁ + S₂)`
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  have hC := conv_ge A B (i := S1) (j := S2) (by omega) (by omega)
  have hCl : S1 + S2 < (convC N z h).length := by
    show S1 + S2 < (conv A B).length
    rw [length_conv _ _ (List.ne_nil_of_length_pos (by omega))]; omega
  have hP := psiAux_ge lam 0 (convC N z h) NEG hCl
  rw [Nat.zero_add] at hP
  rw [hS]
  have key : cvF (N, z, h) 0 ab - ((S1 + S2 : ℕ) : ℤ) ^ 2 - lam * ((S1 + S2 : ℕ) : ℤ) ≤
      psiC N z h lam := by
    unfold psiC; simp only [convC] at hP ⊢; linarith
  have := (Int.cast_le (R := ℝ)).2 key
  push_cast at this ⊢
  linarith

end Hankel2.CertC
