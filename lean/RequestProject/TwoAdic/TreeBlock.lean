import RequestProject.TwoAdic.TreeFactor
import RequestProject.Frame.NvMv
import RequestProject.Frame.HankelMinor

/-!
# Tree bound, step 2: minors of the block-diagonal matrix `C` (P, §7)

General-`q`, several-variable port of `Zeta35.nv_det_cbl_le`: `det C[f, g] = 0` unless the node
profiles agree, and otherwise `−v_ℓ(det C[f, g]) ≤ ∑_u e_ℓ(u, s_u, ℓ_u(f) + ℓ_u(g))`
(`nvMv_det_cbl_le`).  The reduction of a local minor to minors with standard columns is the general
`PadicWin.hdet_mem_of_std_trunc`.
-/

open Polynomial Finset Matrix

namespace TwoAdicWin

open Hankel2 PadicWin

variable {q d n K : ℕ}

/-- The node of the column `f c`. -/
def nodeFQ (f : Fin K → IdxQ q n) (c : Fin K) : Fin (2 * R n + 1) := (ofLex (f c)).1

/-- The Taylor order of the column `f c`. -/
def ordFQ (f : Fin K → IdxQ q n) (c : Fin K) : Fin q := (ofLex (f c)).2

/-- The node profile `s_u(f) = #{c : node(f c) = u}`. -/
def profQ (f : Fin K → IdxQ q n) (u : Fin (2 * R n + 1)) : ℕ :=
  (univ.filter fun c => nodeFQ f c = u).card

/-- `ℓ_u(f) = ∑_{node(f c) = u} b_c − C(s_u, 2)`. -/
def ellColQ (f : Fin K → IdxQ q n) (u : Fin (2 * R n + 1)) : ℕ :=
  (∑ c ∈ univ.filter (fun c => nodeFQ f c = u), (ordFQ f c : ℕ)) - (profQ f u).choose 2

theorem nodeFQ_mono {f : Fin K → IdxQ q n} (hf : StrictMono f) : Monotone (nodeFQ f) :=
  fun _ _ h => Prod.Lex.monotone_fst _ _ (hf.monotone h)

theorem sum_profQ (f : Fin K → IdxQ q n) : ∑ u, profQ f u = K := by
  have := card_eq_sum_card_fiberwise (f := nodeFQ f) (s := univ) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))
  simpa [profQ] using this.symm

theorem det_cblQ_eq_zero_of_prof_ne {f g : Fin K → IdxQ q n} (h : profQ f ≠ profQ g) :
    ((CblQ q d n).submatrix f g).det = 0 := by
  rw [det_apply]
  refine sum_eq_zero fun σ _ => ?_
  by_contra hne
  have hall : ∀ i, nodeFQ f (σ i) = nodeFQ g i := by
    intro i
    by_contra hi
    apply hne
    rw [Finset.prod_eq_zero (mem_univ i) (by simp [CblQ, nodeFQ] at hi ⊢; simp [hi])]
    simp
  apply h
  have hle : ∀ u, profQ g u ≤ profQ f u := by
    intro u
    refine card_le_card_of_injOn σ (fun i hi => ?_) (σ.injective.injOn)
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    rw [hall]; exact hi
  funext u
  have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun u _ => hle u)).1
    (by rw [sum_profQ, sum_profQ])
  exact (this u (mem_univ _)).symm

theorem mono_le_iffQ {α : Type*} [LinearOrder α] {h : Fin K → α} (hm : Monotone h) (c : Fin K)
    (u : α) : h c ≤ u ↔ (c : ℕ) < (univ.filter fun c' => h c' ≤ u).card := by
  constructor
  · intro hc
    have hs : Iic c ⊆ univ.filter fun c' => h c' ≤ u := fun c' hc' => by
      simp only [mem_Iic] at hc'
      simp only [mem_filter, mem_univ, true_and]
      exact (hm hc').trans hc
    have := card_le_card hs
    rw [Fin.card_Iic] at this
    omega
  · intro hc
    by_contra hcu
    push_neg at hcu
    have hs : (univ.filter fun c' => h c' ≤ u) ⊆ Iio c := fun c' hc' => by
      simp only [mem_filter, mem_univ, true_and] at hc'
      simp only [mem_Iio]
      by_contra hh
      push_neg at hh
      exact absurd (hc'.trans_lt hcu) (not_lt.2 (hm hh))
    have := card_le_card hs
    rw [Fin.card_Iio] at this
    omega

theorem card_le_eq_sum_profQ (f : Fin K → IdxQ q n) (u : Fin (2 * R n + 1)) :
    (univ.filter fun c => nodeFQ f c ≤ u).card = ∑ u' ∈ Iic u, profQ f u' := by
  rw [card_eq_sum_card_fiberwise (f := nodeFQ f) (t := Iic u)
    (fun c hc => by simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc; simpa using hc)]
  refine sum_congr rfl fun u' hu' => ?_
  rw [profQ, filter_filter]
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ mem_Iic.1 hu', h⟩

theorem nodeFQ_eq_of_prof_eq {f g : Fin K → IdxQ q n} (hf : StrictMono f) (hg : StrictMono g)
    (h : profQ f = profQ g) : nodeFQ f = nodeFQ g := by
  have key : ∀ u, (univ.filter fun c => nodeFQ f c ≤ u).card =
      (univ.filter fun c => nodeFQ g c ≤ u).card := by
    intro u; rw [card_le_eq_sum_profQ, card_le_eq_sum_profQ, h]
  funext c
  apply le_antisymm
  · rw [mono_le_iffQ (nodeFQ_mono hf), key, ← mono_le_iffQ (nodeFQ_mono hg)]
  · rw [mono_le_iffQ (nodeFQ_mono hg), ← key, ← mono_le_iffQ (nodeFQ_mono hf)]

theorem toLex_nodeFQ_ordFQ (f : Fin K → IdxQ q n) (c : Fin K) :
    toLex (nodeFQ f c, ordFQ f c) = f c := rfl

theorem profQ_le {f : Fin K → IdxQ q n} (hf : StrictMono f) (u : Fin (2 * R n + 1)) :
    profQ f u ≤ q := by
  have := card_le_card_of_injOn (s := univ.filter fun c => nodeFQ f c = u)
    (t := (univ : Finset (Fin q))) (ordFQ f)
    (fun _ _ => mem_coe.2 (mem_univ _)) (by
      intro c hc c' hc' hcc
      simp at hc hc'
      apply hf.injective
      rw [← toLex_nodeFQ_ordFQ f c, ← toLex_nodeFQ_ordFQ f c', hc, hc', hcc])
  simpa [profQ] using this

theorem profQ_mem_profiles {f : Fin K → IdxQ q n} (hf : StrictMono f) :
    profQ f ∈ profiles q n K := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range]
  exact ⟨fun u => Nat.lt_succ_of_le (profQ_le hf u), sum_profQ f⟩

/-! ### The block factorisation -/

theorem strictMono_le_applyQ {s : ℕ} {F : Fin s → ℕ} (hF : StrictMono F) (i : Fin s) :
    (i : ℕ) ≤ F i := by
  have hsub : (Iic i).image F ⊆ range (F i + 1) := fun x hx => by
    simp only [mem_image, mem_Iic] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact mem_range.2 (Nat.lt_succ_of_le (hF.monotone hj))
  have := card_le_card hsub
  rw [card_image_of_injective _ hF.injective, Fin.card_Iic, card_range] at this
  omega

theorem sum_fin_id (s : ℕ) : ∑ i : Fin s, (i : ℕ) = s.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) s, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_two_le_sumQ {s : ℕ} {F : Fin s → ℕ} (hF : StrictMono F) :
    s.choose 2 ≤ ∑ i, F i := by
  rw [← sum_fin_id]
  exact sum_le_sum fun i _ => strictMono_le_applyQ hF i

/-- The rows of the block of node `u`, in increasing order. -/
noncomputable def blockEquivQ (f : Fin K → IdxQ q n) (u : Fin (2 * R n + 1)) :
    Fin (profQ f u) ≃o {c // nodeFQ f c = u} :=
  Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_subtype]; rfl)

/-- The orders of the block of node `u`, as natural numbers. -/
noncomputable def blockOrd (f : Fin K → IdxQ q n) (u : Fin (2 * R n + 1)) (g : Fin K → IdxQ q n) :
    Fin (profQ f u) → ℕ := fun r => (ordFQ g (blockEquivQ f u r) : ℕ)

theorem blockOrd_strictMono {f g : Fin K → IdxQ q n} (hg : StrictMono g)
    (hfg : nodeFQ f = nodeFQ g) (u : Fin (2 * R n + 1)) : StrictMono (blockOrd f u g) := by
  intro r r' hr
  have h1 : (blockEquivQ f u r : Fin K) < blockEquivQ f u r' := (blockEquivQ f u).strictMono hr
  have h2 := hg h1
  rw [Prod.Lex.lt_iff] at h2
  have e1 : nodeFQ g (blockEquivQ f u r) = u := by rw [← hfg]; exact (blockEquivQ f u r).2
  have e2 : nodeFQ g (blockEquivQ f u r') = u := by rw [← hfg]; exact (blockEquivQ f u r').2
  simp only [nodeFQ] at e1 e2
  rcases h2 with h2 | h2
  · exact absurd (lt_of_lt_of_eq (lt_of_eq_of_lt e1.symm h2) e2) (lt_irrefl u)
  · simp only [blockOrd, ordFQ]; exact_mod_cast h2.2

theorem sum_blockOrd {f g : Fin K → IdxQ q n} (hfg : nodeFQ f = nodeFQ g)
    (u : Fin (2 * R n + 1)) :
    ∑ r, blockOrd f u g r = ∑ c ∈ univ.filter (fun c => nodeFQ g c = u), (ordFQ g c : ℕ) := by
  rw [Fintype.sum_equiv (blockEquivQ f u).toEquiv (fun r => blockOrd f u g r)
    (fun c => (ordFQ g c : ℕ)) (fun r => rfl)]
  exact (Finset.sum_subtype (univ.filter fun c => nodeFQ g c = u) (fun x => by simp [hfg])
    (fun c => (ordFQ g c : ℕ))).symm

theorem profQ_eq {f g : Fin K → IdxQ q n} (hfg : nodeFQ f = nodeFQ g) (u : Fin (2 * R n + 1)) :
    profQ f u = profQ g u := by simp only [profQ, hfg]

theorem sum_ordFQ_eq {f : Fin K → IdxQ q n} (hf : StrictMono f) (u : Fin (2 * R n + 1)) :
    ∑ c ∈ univ.filter (fun c => nodeFQ f c = u), (ordFQ f c : ℕ) =
      ellColQ f u + (profQ f u).choose 2 := by
  have := choose_two_le_sumQ (blockOrd_strictMono hf rfl u)
  rw [sum_blockOrd rfl] at this
  rw [ellColQ]; omega

/-- The block of node `u` is a local minor `det C_u[F_u, G_u]`. -/
theorem det_blockQ_eq {f g : Fin K → IdxQ q n} (hfg : nodeFQ f = nodeFQ g)
    (u : Fin (2 * R n + 1)) :
    (((CblQ q d n).submatrix f g).toSquareBlock (nodeFQ f) u).det =
      hdet (cMv q d n (nodeOf n u)) (blockOrd f u f) (blockOrd f u g) := by
  rw [← det_submatrix_equiv_self (blockEquivQ f u).toEquiv, hdet]
  congr 1
  refine Matrix.ext fun r r' => ?_
  have e1 := (blockEquivQ f u r).2
  have e2 := (blockEquivQ f u r').2
  have e2' : nodeFQ g (blockEquivQ f u r') = u := by rw [← hfg]; exact e2
  change CblQ q d n (f (blockEquivQ f u r)) (g (blockEquivQ f u r')) = _
  simp only [CblQ]
  simp only [nodeFQ] at e1 e2'
  split_ifs with h
  · simp only [of_apply, blockOrd, ordFQ]
    exact congrArg (fun k => cMv q d n (nodeOf n k) _) e1
  · exact absurd (e1.trans e2'.symm) h

/-- A standard minor with entries `< q` is a `minorRQ`. -/
theorem hdet_std_eq_minorRQ (k : ℤ) {s : ℕ} (Rw : Fin s → ℕ) (hR : StrictMono Rw)
    (hq : ∀ i, Rw i < q) :
    ∃ Rs : Finset (Fin q), Rs.card = s ∧ ellRQ Rs = (∑ i, Rw i) - s.choose 2 ∧
      hdet (cMv q d n k) Rw (stdF s) = minorRQ q d n k Rs := by
  set Rf : Fin s → Fin q := fun i => ⟨Rw i, hq i⟩ with hRf
  have hRfm : StrictMono Rf := fun i j h => by simp only [hRf, Fin.mk_lt_mk]; exact hR h
  have hc : (univ.image Rf).card = s := by
    rw [card_image_of_injective _ hRfm.injective, card_univ, Fintype.card_fin]
  refine ⟨univ.image Rf, hc, ?_, ?_⟩
  · rw [ellRQ, sum_image (fun a _ b _ h => hRfm.injective h), hc]
  · have hRw : Rf = fun i => (univ.image Rf).orderEmbOfFin hc i :=
      orderEmbOfFin_unique hc (fun i => mem_image_of_mem _ (mem_univ i)) hRfm
    have key : ∀ (Rs : Finset (Fin q)) (hc : Rs.card = s),
        Rf = (fun i => Rs.orderEmbOfFin hc i) →
        hdet (cMv q d n k) Rw (stdF s) = minorRQ q d n k Rs := by
      intro Rs hc' hRs
      subst hc'
      rw [minorRQ, hdet]
      congr 1
      refine Matrix.ext fun i j => ?_
      simp only [of_apply, CmatQ, stdF]
      have : Rw i = (Rs.orderEmbOfFin rfl i : ℕ) := by
        have := congrFun hRs i
        simp only [hRf] at this
        rw [← this]
      rw [this]
      rfl
    exact key _ hc hRw

theorem nvMv_hdet_le (p : ℕ) [Fact p.Prime] (k : ℤ) {s : ℕ} {F G : Fin s → ℕ}
    (hF : StrictMono F) (hG : StrictMono G) :
    nvMv p (hdet (cMv q d n k) F G) ≤
      eP q d n p k s ((∑ i, F i - s.choose 2) + (∑ i, G i - s.choose 2)) := by
  rw [← mem_nvSub]
  refine hdet_mem_of_std_trunc (cMv q d n k) (fun m hm => cMv_eq_zero hm) hF hG _ ?_
  intro Rw hR hq hsum
  obtain ⟨Rs, hcard, hell, heq⟩ := hdet_std_eq_minorRQ (d := d) (n := n) k Rw hR hq
  rw [mem_nvSub, heq]
  refine le_sup (f := fun Rs => negTop (gaussValMv p (minorRQ q d n k Rs))) ?_
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨hcard, ?_⟩
  rw [hell]
  have h1 := choose_two_le_sumQ hF
  have h2 := choose_two_le_sumQ hG
  rw [show ∑ i, stdF s i = s.choose 2 from sum_fin_id s] at hsum
  omega

/-- **The block bound**: `−v_p(det C[f,g]) ≤ ∑_u e_p(u, s_u, ℓ_u(f) + ℓ_u(g))`. -/
theorem nvMv_det_cbl_le (p : ℕ) [Fact p.Prime] {f g : Fin K → IdxQ q n} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : nodeFQ f = nodeFQ g) :
    nvMv p ((CblQ q d n).submatrix f g).det ≤ ∑ u ∈ univ.image (nodeFQ f),
      eP q d n p (nodeOf n u) (profQ f u) (ellColQ f u + ellColQ g u) := by
  have hbt : ((CblQ q d n).submatrix f g).BlockTriangular (nodeFQ f) := by
    intro c e hce
    simp only [submatrix_apply, CblQ]
    rw [if_neg]
    intro h
    have h' : nodeFQ f c = nodeFQ g e := h
    rw [← hfg] at h'
    exact absurd h' (ne_of_gt hce)
  rw [hbt.det]
  refine (nvMv_prod_le _ _).trans (sum_le_sum fun u _ => ?_)
  rw [det_blockQ_eq hfg u]
  refine (nvMv_hdet_le p (nodeOf n u) (blockOrd_strictMono hf rfl u)
    (blockOrd_strictMono hg hfg u)).trans (le_of_eq ?_)
  congr 2
  · rw [sum_blockOrd rfl]; rfl
  · rw [sum_blockOrd hfg, profQ_eq hfg u]; rfl

end TwoAdicWin
