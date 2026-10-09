import RequestProject.TwoAdic.TreeVdm

/-!
# The tree bound `−v_ℓ(Δ_{qn}) ≤ T_ℓ` (P, Thm 7.1)

`tree_bound_general`: for every prime `ℓ` and all `q, d, n, K`, `−v_ℓ(Δ_K) ≤ T_ℓ`, where `v_ℓ` is the
minimum of `v_ℓ` over the coefficients of the multivariable Hankel polynomial
`Δ_K = hankelPoly q d n K ∈ ℚ[X_1, …, X_r]`.  As W remarks, only `v(fg) ≥ v(f) + v(g)` and
ultrametricity of the Gauss valuation are used.

`tree_field` is field (iii-a) `tree` of `TwoAdicInputsOpen`, verbatim.

Proof: by the double Cauchy–Binet expansion (`hankelPoly_eq_sumQ`),
`Δ_K = ∑_{f,g} det E[:, f] · det C[f, g] · det E[:, g]`; for a term with `det C[f,g] ≠ 0` the node
profiles agree, and the bounds of `TreeBlock`, `TreeVdm`, `TreePenalty` combine with
`e_ℓ(u, s_u, λ_u) + λ_u λ_ℓ(u) ≤ f_ℓ(u, s_u)` (`eP_add_le_fPQ`).
-/

open Polynomial Finset Matrix

namespace TwoAdicWin

open Hankel2 PadicWin

variable {q d n K : ℕ}

/-- `λ(R) ≤ |R|(q − |R|)`. -/
theorem ellRQ_le (Rs : Finset (Fin q)) : ellRQ Rs ≤ Rs.card * (q - Rs.card) := by
  obtain ⟨s, hcs⟩ : ∃ s, Rs.card = s := ⟨_, rfl⟩
  have hsq : s ≤ q := by rw [← hcs]; simpa using Rs.card_le_univ
  set e := Rs.orderEmbOfFin hcs
  have hsum : ∑ r ∈ Rs, (r : ℕ) = ∑ i : Fin s, ((e i : Fin q) : ℕ) := by
    rw [← Finset.sum_image (f := fun r : Fin q => (r : ℕ)) (s := univ)
      (g := fun i => e i) (fun a _ b _ h => e.injective h)]
    congr 1
    ext r
    simp only [mem_image, mem_univ, true_and]
    constructor
    · intro hr
      obtain ⟨i, hi⟩ := (Set.ext_iff.1 (Rs.range_orderEmbOfFin hcs) r).2 (by simpa using hr)
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩; exact Rs.orderEmbOfFin_mem hcs i
  have hrev : StrictMono fun i : Fin s => q - 1 - (e (Fin.rev i) : ℕ) := by
    intro i j h
    have h1 : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.2 h
    have h2 := e.strictMono h1
    have h3 := (e (Fin.rev i)).isLt
    have : ((e (Fin.rev j)) : ℕ) < (e (Fin.rev i) : ℕ) := h2
    simp only
    omega
  have hlow := choose_two_le_sumQ hrev
  have hrevsum : ∑ i : Fin s, (q - 1 - (e (Fin.rev i) : ℕ)) =
      ∑ i : Fin s, (q - 1 - (e i : ℕ)) :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun i => rfl)
  rw [hrevsum] at hlow
  have hbd : ∀ i : Fin s, (e i : ℕ) ≤ q - 1 := fun i => by
    have := (e i).isLt; omega
  have hsplit : ∑ i : Fin s, (q - 1 - (e i : ℕ)) + ∑ i : Fin s, (e i : ℕ) = s * (q - 1) := by
    rw [← sum_add_distrib]
    rw [sum_congr rfl fun i _ => Nat.sub_add_cancel (hbd i)]
    simp
  rw [ellRQ, hsum, hcs]
  have hc : 2 * s.choose 2 = s * (s - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd
  have hkey : s * (q - 1) = s * (q - s) + s * (s - 1) := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · simp [h0]
    · rw [← Nat.mul_add]; congr 1; omega
  omega

theorem eP_add_le_fPQ (p : ℕ) (k : ℤ) {s : ℕ} (hs : s ≠ 0) (j : ℕ) :
    eP q d n p k s j + (((j * lambdaP n p k : ℕ) : ℤ) : WithBot ℤ) ≤ fP q d n p k s := by
  rw [fP, if_neg hs]
  by_cases hj : j ≤ s * (q - s)
  · exact le_sup (f := fun j => eP q d n p k s j + (((j * lambdaP n p k : ℕ) : ℤ) : WithBot ℤ))
      (mem_range.2 (Nat.lt_succ_of_le hj))
  · have : eP q d n p k s j = ⊥ := by
      rw [eP, Finset.sup_eq_bot_iff]
      intro Rs hR
      simp only [mem_filter, mem_univ, true_and] at hR
      have := ellRQ_le Rs
      rw [hR.1, hR.2] at this
      exact absurd this hj
    rw [this, WithBot.bot_add]; exact bot_le

theorem ellColQ_eq_zero_of_not_mem {f : Fin K → IdxQ q n} {u : Fin (2 * R n + 1)}
    (hu : u ∉ univ.image (nodeFQ f)) : ellColQ f u = 0 := by
  have : univ.filter (fun c => nodeFQ f c = u) = ∅ := by
    ext c; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h; exact hu (mem_image.2 ⟨c, mem_univ _, h⟩)
  simp [ellColQ, this]

theorem profQ_ne_zero_of_mem {f : Fin K → IdxQ q n} {u : Fin (2 * R n + 1)}
    (hu : u ∈ univ.image (nodeFQ f)) : profQ f u ≠ 0 := by
  obtain ⟨c, _, hc⟩ := mem_image.1 hu
  rw [profQ, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨c, by simp [hc]⟩

theorem profQ_eq_zero_of_not_mem {f : Fin K → IdxQ q n} {u : Fin (2 * R n + 1)}
    (hu : u ∉ univ.image (nodeFQ f)) : profQ f u = 0 := by
  rw [profQ, card_eq_zero]
  ext c; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h; exact hu (mem_image.2 ⟨c, mem_univ _, h⟩)

theorem nvMv_C_le' (p : ℕ) [Fact p.Prime] {a : ℚ} {T : ℤ} (h : ‖(a : ℚ_[p])‖ ≤ (p : ℝ) ^ T) :
    nvMv p (MvPolynomial.C a : MvPolynomial (Fin (rr q)) ℚ) ≤ T := nvMv_C_le h

/-- One term of the double Cauchy–Binet expansion. -/
theorem nvMv_term_le (p : ℕ) [Fact p.Prime] {f g : Fin K → IdxQ q n} (hf : StrictMono f)
    (hg : StrictMono g) :
    nvMv p (MvPolynomial.C ((EmatQ q n K).submatrix id f).det * ((CblQ q d n).submatrix f g).det *
      MvPolynomial.C ((EmatQ q n K).submatrix id g).det) ≤ TP q d n p K := by
  by_cases hpr : profQ f = profQ g
  swap
  · rw [det_cblQ_eq_zero_of_prof_ne hpr, mul_zero, zero_mul, nvMv_zero]; exact bot_le
  have hfg := nodeFQ_eq_of_prof_eq hf hg hpr
  set s := profQ f with hs
  have h1 : nvMv p (MvPolynomial.C ((EmatQ q n K).submatrix id f).det :
      MvPolynomial (Fin (rr q)) ℚ) ≤ ZfQ p f := nvMv_C_le (norm_det_EmatQ_le p f)
  have h3 : nvMv p (MvPolynomial.C ((EmatQ q n K).submatrix id g).det :
      MvPolynomial (Fin (rr q)) ℚ) ≤ ZfQ p g := nvMv_C_le (norm_det_EmatQ_le p g)
  have h2 := nvMv_det_cbl_le (d := d) p hf hg hfg
  set S := ∑ u ∈ univ.image (nodeFQ f),
    eP q d n p (nodeOf n u) (profQ f u) (ellColQ f u + ellColQ g u)
  have hZ : ZfQ p f + ZfQ p g =
      ∑ u, (lamQ n p u : ℤ) * ((ellColQ f u : ℤ) + (ellColQ g u : ℤ)) - penalty n p s := by
    have e1 := two_ZfQ p hf
    have e2 := two_ZfQ p hg
    rw [← hs] at e1
    rw [← hpr] at e2
    rw [penalty_eq_pairSumQ]
    have : ∑ u, (lamQ n p u : ℤ) * ((ellColQ f u : ℤ) + (ellColQ g u : ℤ)) =
        ∑ u, (lamQ n p u : ℤ) * (ellColQ f u : ℤ) + ∑ u, (lamQ n p u : ℤ) * (ellColQ g u : ℤ) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun u _ => by ring
    rw [this]
    linarith
  have hsum : ∑ u, (lamQ n p u : ℤ) * ((ellColQ f u : ℤ) + (ellColQ g u : ℤ)) =
      ∑ u ∈ univ.image (nodeFQ f), (lamQ n p u : ℤ) * ((ellColQ f u : ℤ) + (ellColQ g u : ℤ)) := by
    symm
    refine sum_subset (subset_univ _) fun u _ hu => ?_
    have hu' : u ∉ univ.image (nodeFQ g) := by rwa [← hfg]
    rw [ellColQ_eq_zero_of_not_mem hu, ellColQ_eq_zero_of_not_mem hu']; simp
  have hfP : ∑ u ∈ univ.image (nodeFQ f),
      (eP q d n p (nodeOf n u) (profQ f u) (ellColQ f u + ellColQ g u) +
        ((((ellColQ f u + ellColQ g u) * lambdaP n p (nodeOf n u) : ℕ) : ℤ) : WithBot ℤ)) ≤
      ∑ u, fP q d n p (nodeOf n u) (s u) := by
    rw [← sum_subset (subset_univ (univ.image (nodeFQ f))) (fun u _ hu => by
      rw [hs, profQ_eq_zero_of_not_mem hu, fP, if_pos rfl])]
    exact sum_le_sum fun u hu => eP_add_le_fPQ p _ (profQ_ne_zero_of_mem hu) _
  rw [sum_add_distrib] at hfP
  have hTP : (∑ u, fP q d n p (nodeOf n u) (s u)) + ((-penalty n p s : ℤ) : WithBot ℤ) ≤
      TP q d n p K :=
    le_sup (f := fun s => (∑ i, fP q d n p (nodeOf n i) (s i)) + ((-penalty n p s : ℤ) : WithBot ℤ))
      (profQ_mem_profiles hf)
  have hcast : (∑ u ∈ univ.image (nodeFQ f),
      ((((ellColQ f u + ellColQ g u) * lambdaP n p (nodeOf n u) : ℕ) : ℤ) : WithBot ℤ)) =
      (((ZfQ p f + ZfQ p g + penalty n p s : ℤ)) : WithBot ℤ) := by
    rw [← WithBot.coe_sum, hZ, hsum, sub_add_cancel]
    congr 1
    push_cast
    refine sum_congr rfl fun u _ => ?_
    rw [lamQ]; ring
  rw [hcast] at hfP
  calc nvMv p (MvPolynomial.C ((EmatQ q n K).submatrix id f).det *
        ((CblQ q d n).submatrix f g).det * MvPolynomial.C ((EmatQ q n K).submatrix id g).det)
      ≤ (ZfQ p f : WithBot ℤ) + S + (ZfQ p g : WithBot ℤ) :=
        (nvMv_mul_le _ _).trans (add_le_add ((nvMv_mul_le _ _).trans (add_le_add h1 h2)) h3)
    _ = S + (((ZfQ p f + ZfQ p g + penalty n p s : ℤ)) : WithBot ℤ) +
          ((-penalty n p s : ℤ) : WithBot ℤ) := by
        rw [add_assoc S, ← WithBot.coe_add, show ZfQ p f + ZfQ p g + penalty n p s +
          -penalty n p s = ZfQ p f + ZfQ p g by ring, WithBot.coe_add]
        abel
    _ ≤ (∑ u, fP q d n p (nodeOf n u) (s u)) + ((-penalty n p s : ℤ) : WithBot ℤ) :=
        add_le_add hfP le_rfl
    _ ≤ TP q d n p K := hTP

/-- **The tree bound** (P, Thm 7.1), for every prime `ℓ` and all `q, d, n, K`. -/
theorem tree_bound_general (q d n K p : ℕ) (hp : p.Prime) :
    negTop (gaussValMv p (hankelPoly q d n K)) ≤ TP q d n p K := by
  haveI := Fact.mk hp
  change nvMv p (hankelPoly q d n K) ≤ TP q d n p K
  rw [hankelPoly_eq_sumQ]
  refine (nvMv_sum_le _ _).trans (Finset.sup_le fun f hf => ?_)
  refine (nvMv_sum_le _ _).trans (Finset.sup_le fun g hg => ?_)
  exact nvMv_term_le p (mem_smSet.1 hf) (mem_smSet.1 hg)

/-- **Field (iii-a) `tree` of `TwoAdicInputsOpen`, discharged**. -/
theorem tree_field : ∀ q d n ℓ : ℕ, Admissible q d → Even n → ℓ.Prime → ℓ ≠ 2 →
    negTop (PadicWin.gaussValMv ℓ (hankelPoly q d n (q * n))) ≤ TP q d n ℓ (q * n) :=
  fun q d n ℓ _ _ hℓ _ => tree_bound_general q d n (q * n) ℓ hℓ

end TwoAdicWin
