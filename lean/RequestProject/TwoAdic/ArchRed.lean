import RequestProject.TwoAdic.ArchLocal
import RequestProject.TwoAdic.TreeBlock
import RequestProject.Zeta35.ArchReduction3

/-!
# The discrete reduction (port of P, Lemma 6.2), general `q`, several variables

Over the double Cauchy–Binet expansion `Δ_K = ∑_{f,g} det E[:,f] · det C[f,g] · det E[:,g]`
(`hankelPoly_eq_sumQ`):

* `abs_det_EmatQ_le`: `|det E[:,f]| ≤ exp(½ ∑_{u,v} s_u s_v ln(|u − v| + 2))`, `s = profQ f`;
* `l1_det_CblQ_le`: `‖det C[f,g]‖₁ ≤ (q!)^{2R+1} ∏_u (Q |h_u|)^{s_u}`;
* at most `2^{q(2R+1)}` column sets (`(q+1)^{3n+1}` profiles in W);
* the kernel replacement `ln(|d| + 2) ≤ B(d) + 2/|d|` (`d ≠ 0`) with the harmonic estimate.

**`arch_reduction`**: if `E_B(s) ≤ M` for every profile `0 ≤ s_u ≤ q`, `∑ s_u = K`, then
`‖Δ_K‖₁ ≤ exp(M + 𝓔(n, K))`, where
`E_B(s) = ∑_u s_u ln|h_u| + ∑_{u,v} s_u s_v B(u − v)`, `B(d) = ½ ln(1 + d²)`, and
`𝓔(n,K) = K (ln Q + 4q(1 + ln 2R) + q ln 2) + (2R+1)(ln q! + 2q ln 2)`.
-/

open Polynomial Finset Matrix Hankel2 PadicWin

namespace TwoAdicWin.Arch

variable {q d n K : ℕ}

/-- `h_u = H_u[0]` at the node `nodeOf n u`, as a real number. -/
noncomputable def hR (q n : ℕ) (u : Fin (2 * R n + 1)) : ℝ := ((Hk q n (nodeOf n u) 0 : ℚ) : ℝ)

/-- The discrete energy `E_B(s) = ∑_u s_u ln|h_u| + ∑_{u,v} s_u s_v B(u − v)`. -/
noncomputable def EB (q n : ℕ) (s : Fin (2 * R n + 1) → ℝ) : ℝ :=
  ∑ u, s u * Real.log |hR q n u| +
    ∑ u, ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v)

/-- The error term `𝓔(n, K)`. -/
noncomputable def errR (q d n K : ℕ) : ℝ :=
  K * (Real.log (Qc q d n) + 4 * q * (1 + Real.log (2 * R n)) + q * Real.log 2) +
    (2 * R n + 1) * (Real.log (q.factorial) + 2 * q * Real.log 2)

theorem hR_ne_zero (hn : Even n) (u : Fin (2 * R n + 1)) : hR q n u ≠ 0 := by
  unfold hR; exact_mod_cast Hk_zero_ne_zero hn _

theorem sum_nodeFQ_real (f : Fin K → IdxQ q n) (G : Fin (2 * R n + 1) → ℝ) :
    ∑ c, G (nodeFQ f c) = ∑ u, (profQ f u : ℝ) * G u := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := nodeFQ f) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const, nsmul_eq_mul, profQ]

/-- `G(u, v) = ln(|u − v| + 2)`. -/
noncomputable def Gk (n : ℕ) (u v : Fin (2 * R n + 1)) : ℝ :=
  Real.log (|((nodeOf n u : ℝ) - nodeOf n v)| + 2)

theorem abs_det_EmatQ_le (f : Fin K → IdxQ q n) :
    |((((EmatQ q n K).submatrix id f).det : ℚ) : ℝ)| ≤
      Real.exp ((∑ u, ∑ v, (profQ f u : ℝ) * profQ f v * Gk n u v) / 2) := by
  set x : Fin K → ℝ := fun c => -((nodeOf n (nodeFQ f c) : ℤ) : ℝ) with hx
  have hdet : ((((EmatQ q n K).submatrix id f).det : ℚ) : ℝ) =
      (Matrix.of fun (i c : Fin K) => (((i : ℕ).choose (ordFQ f c : ℕ) : ℕ) : ℝ) *
        x c ^ ((i : ℕ) - (ordFQ f c : ℕ))).det := by
    have := RingHom.map_det (Rat.castHom ℝ) ((EmatQ q n K).submatrix id f)
    simp only [Rat.coe_castHom] at this
    rw [this]
    congr 1
    ext i c
    simp [EmatQ, hx, nodeFQ, ordFQ]
  rw [hdet]
  refine (ArchB.abs_det_confluent_le x (fun c => (ordFQ f c : ℕ))).trans ?_
  have hpos : ∀ c c', 0 < |x c' - x c| + 2 := fun _ _ => by positivity
  have hprod : ∏ c, ∏ c' ∈ Ioi c, (|x c' - x c| + 2) =
      Real.exp (∑ c, ∑ c' ∈ Ioi c, Real.log (|x c' - x c| + 2)) := by
    rw [Real.exp_sum]
    refine prod_congr rfl fun c _ => ?_
    rw [Real.exp_sum]
    refine prod_congr rfl fun c' _ => ?_
    rw [Real.exp_log (hpos c c')]
  rw [hprod, Real.exp_le_exp]
  have hx' : ∀ c c', |x c' - x c| =
      |((nodeOf n (nodeFQ f c) : ℝ)) - nodeOf n (nodeFQ f c')| := by
    intro c c'
    simp only [hx]
    congr 1; ring
  have hsym := ArchB.sym_sum_Ioi_le (fun c c' => Real.log (|x c' - x c| + 2))
    (fun c c' => by simp only; rw [abs_sub_comm])
    (fun c => Real.log_nonneg (by simp))
  have hfull : ∑ c, ∑ c', Real.log (|x c' - x c| + 2) =
      ∑ u, ∑ v, (profQ f u : ℝ) * profQ f v * Gk n u v := by
    simp_rw [hx']
    rw [sum_nodeFQ_real f (fun u => ∑ c', Real.log (|((nodeOf n u : ℝ)) -
      nodeOf n (nodeFQ f c')| + 2))]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_nodeFQ_real f (fun v => Real.log (|((nodeOf n u : ℝ)) - nodeOf n v| + 2)), mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [Gk]; ring
  linarith

theorem l1_det_CblQ_le (hq : 2 ≤ q) (hn : Even n) {f g : Fin K → IdxQ q n} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : profQ f = profQ g) :
    l1Mv ((CblQ q d n).submatrix f g).det ≤
      (q.factorial : ℝ) ^ (2 * R n + 1) * ∏ u, (Qc q d n * |hR q n u|) ^ profQ f u := by
  have hnode := nodeFQ_eq_of_prof_eq hf hg hfg
  have hbt : ((CblQ q d n).submatrix f g).BlockTriangular (nodeFQ f) := by
    intro c e hce
    simp only [submatrix_apply, CblQ]
    rw [if_neg]
    intro h
    have h' : nodeFQ f c = nodeFQ g e := h
    rw [← hnode] at h'
    exact absurd h' (ne_of_gt hce)
  rw [hbt.det]
  have hA : ∀ u, 0 ≤ Qc q d n * |hR q n u| :=
    fun u => mul_nonneg (Qc_pos (by omega)).le (abs_nonneg _)
  have hblock : ∀ u, l1Mv (((CblQ q d n).submatrix f g).toSquareBlock (nodeFQ f) u).det ≤
      (q.factorial : ℝ) * (Qc q d n * |hR q n u|) ^ profQ f u := by
    intro u
    have hcard : Fintype.card {c // nodeFQ f c = u} = profQ f u := by
      rw [Fintype.card_subtype]; rfl
    refine (l1Mv_det_le _ (Qc q d n * |hR q n u|) fun c e => ?_).trans ?_
    · show l1Mv (CblQ q d n (f c) (g e)) ≤ _
      simp only [CblQ]
      split_ifs with h
      · have hc : (ofLex (f c)).1 = u := c.2
        rw [hc]
        exact l1_cMv_le hq hn _ _
      · rw [l1Mv_zero]; exact hA u
    · rw [hcard]
      have h4 := profQ_le hf u
      have : ((profQ f u).factorial : ℝ) ≤ q.factorial := by
        exact_mod_cast Nat.factorial_le h4
      exact mul_le_mul_of_nonneg_right this (pow_nonneg (hA u) _)
  refine (l1Mv_prod_le _ _).trans ?_
  calc ∏ u ∈ univ.image (nodeFQ f),
        l1Mv (((CblQ q d n).submatrix f g).toSquareBlock (nodeFQ f) u).det
      ≤ ∏ u ∈ univ.image (nodeFQ f), (q.factorial : ℝ) * (Qc q d n * |hR q n u|) ^ profQ f u :=
        prod_le_prod (fun _ _ => l1Mv_nonneg _) (fun u _ => hblock u)
    _ = (q.factorial : ℝ) ^ (univ.image (nodeFQ f)).card *
          ∏ u ∈ univ.image (nodeFQ f), (Qc q d n * |hR q n u|) ^ profQ f u := by
        rw [prod_mul_distrib, prod_const]
    _ ≤ (q.factorial : ℝ) ^ (2 * R n + 1) * ∏ u, (Qc q d n * |hR q n u|) ^ profQ f u := by
        refine mul_le_mul ?_ (le_of_eq ?_) (prod_nonneg fun u _ => pow_nonneg (hA u) _)
          (by positivity)
        · refine pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos q)) ?_
          exact (card_le_univ _).trans (by simp)
        · refine prod_subset (subset_univ _) fun u _ hu => ?_
          have : profQ f u = 0 := by
            rw [profQ, card_eq_zero, filter_eq_empty_iff]
            intro c _ hc
            exact hu (mem_image.2 ⟨c, mem_univ _, hc⟩)
          rw [this, pow_zero]

/-- `∑_v 1/|u − v| ≤ 2(1 + ln 2R)` over the nodes. -/
theorem sum_inv_node_le (n : ℕ) (u : Fin (2 * R n + 1)) :
    ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| ≤ 2 * (1 + Real.log (2 * R n)) :=
  Zeta35.Arch.sum_inv_node_le3 n u

theorem nodeOf_injective (n : ℕ) : Function.Injective (nodeOf n) := by
  intro u v h
  simp only [nodeOf] at h
  exact Fin.ext (by omega)

/-- The Vandermonde exponent against the energy. -/
theorem sum_Gk_le (s : Fin (2 * R n + 1) → ℝ) (hs0 : ∀ u, 0 ≤ s u) (hsq : ∀ u, s u ≤ q) :
    ∑ u, ∑ v, s u * s v * Gk n u v ≤
      ∑ u, ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        (∑ u, s u) * (4 * q * (1 + Real.log (2 * R n)) + q * Real.log 2) := by
  rw [sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun u _ => ?_
  have hterm : ∀ v, s u * s v * Gk n u v ≤
      s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
      s u * (2 * q * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then q * Real.log 2 else 0)) := by
    intro v
    have h := ArchB.log_add_two_le ((nodeOf n u : ℝ) - nodeOf n v)
    have hsuv : 0 ≤ s u * s v := mul_nonneg (hs0 u) (hs0 v)
    have e : (((nodeOf n u : ℝ) - nodeOf n v) = 0) ↔ u = v := by
      constructor
      · intro h0
        exact nodeOf_injective n (by exact_mod_cast sub_eq_zero.1 h0)
      · rintro rfl; simp
    have hG : s u * s v * Gk n u v ≤ s u * s v * (ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then Real.log 2 else 0)) := by
      unfold Gk
      refine mul_le_mul_of_nonneg_left ?_ hsuv
      have := h
      simp only [e] at this
      exact this
    have hinv : 0 ≤ 1 / |((nodeOf n u : ℝ) - nodeOf n v)| := by positivity
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : s u * s v * (2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) ≤
        s u * (2 * q * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) := by
      have hx : 0 ≤ s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) := mul_nonneg (hs0 u) hinv
      calc s u * s v * (2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) =
          (s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) * (2 * s v) := by ring
        _ ≤ (s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) * (2 * q) :=
          mul_le_mul_of_nonneg_left (by linarith [hsq v]) hx
        _ = _ := by ring
    have h2 : s u * s v * (if u = v then Real.log 2 else 0) ≤
        s u * (if u = v then q * Real.log 2 else 0) := by
      split_ifs
      · have hx : 0 ≤ s u * Real.log 2 := mul_nonneg (hs0 u) hl2
        calc s u * s v * Real.log 2 = (s u * Real.log 2) * s v := by ring
          _ ≤ (s u * Real.log 2) * q := mul_le_mul_of_nonneg_left (hsq v) hx
          _ = _ := by ring
      · simp
    nlinarith
  calc ∑ v, s u * s v * Gk n u v ≤ ∑ v, (s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (2 * q * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
          (if u = v then q * Real.log 2 else 0))) := sum_le_sum fun v _ => hterm v
    _ = ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (2 * q * ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| + q * Real.log 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _)]
    _ ≤ ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (4 * q * (1 + Real.log (2 * R n)) + q * Real.log 2) := by
        have hinv := sum_inv_node_le n u
        have hsu := hs0 u
        have h2 : 2 * (q : ℝ) * ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| ≤
            2 * q * (2 * (1 + Real.log (2 * R n))) := mul_le_mul_of_nonneg_left hinv (by positivity)
        have h3 := mul_le_mul_of_nonneg_left (add_le_add_right h2 ((q : ℝ) * Real.log 2)) hsu
        linarith

/-- **Discrete reduction (P, Lemma 6.2).** -/
theorem arch_reduction (hq : 2 ≤ q) (hn : Even n) (M : ℝ)
    (hM : ∀ s ∈ profiles q n K, EB q n (fun u => (s u : ℝ)) ≤ M) :
    l1Mv (hankelPoly q d n K) ≤ Real.exp (M + errR q d n K) := by
  set T := Real.exp (M + K * (Real.log (Qc q d n) + 4 * q * (1 + Real.log (2 * R n)) +
    q * Real.log 2) + (2 * R n + 1) * Real.log (q.factorial)) with hT
  have hQ : 0 < Qc q d n := Qc_pos (by omega)
  have hqf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hterm : ∀ f ∈ smSet K (IdxQ q n), ∀ g ∈ smSet K (IdxQ q n),
      l1Mv (MvPolynomial.C ((EmatQ q n K).submatrix id f).det * ((CblQ q d n).submatrix f g).det *
        MvPolynomial.C ((EmatQ q n K).submatrix id g).det) ≤ T := by
    intro f hf g hg
    rw [mem_smSet] at hf hg
    refine (l1Mv_C_mul_mul_C_le _ _ _).trans ?_
    by_cases hfg : profQ f = profQ g
    · set s : Fin (2 * R n + 1) → ℝ := fun u => (profQ f u : ℝ) with hs
      have hs0 : ∀ u, 0 ≤ s u := fun u => by positivity
      have hsq : ∀ u, s u ≤ q := fun u => by
        simp only [hs]; exact_mod_cast profQ_le hf u
      have hsK : ∑ u, s u = K := by simp only [hs]; exact_mod_cast sum_profQ f
      have hE1 := abs_det_EmatQ_le f
      have hE2 := abs_det_EmatQ_le g
      rw [← hfg] at hE2
      have hC := l1_det_CblQ_le (d := d) hq hn hf hg hfg
      have hprod : ∏ u, (Qc q d n * |hR q n u|) ^ profQ f u =
          Real.exp (∑ u, s u * (Real.log (Qc q d n) + Real.log |hR q n u|)) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun u _ => ?_
        have hpos : 0 < Qc q d n * |hR q n u| := mul_pos hQ (abs_pos.2 (hR_ne_zero hn u))
        rw [← Real.log_mul hQ.ne' (abs_pos.2 (hR_ne_zero hn u)).ne', mul_comm (s u), Real.exp_mul,
          Real.exp_log hpos, hs, Real.rpow_natCast]
      rw [hprod] at hC
      have hfac : (q.factorial : ℝ) ^ (2 * R n + 1) =
          Real.exp ((2 * R n + 1) * Real.log (q.factorial)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hqf]
        push_cast; ring_nf
      rw [hfac] at hC
      have hEB := hM (profQ f) (profQ_mem_profiles hf)
      have hG := sum_Gk_le s hs0 hsq
      rw [hsK] at hG
      unfold EB at hEB
      set S2 := ∑ u, ∑ v, (profQ f u : ℝ) * profQ f v * Gk n u v
      calc |(((EmatQ q n K).submatrix id f).det : ℝ)| * l1Mv ((CblQ q d n).submatrix f g).det *
            |(((EmatQ q n K).submatrix id g).det : ℝ)|
          ≤ Real.exp (S2 / 2) *
            (Real.exp ((2 * R n + 1) * Real.log (q.factorial)) *
              Real.exp (∑ u, s u * (Real.log (Qc q d n) + Real.log |hR q n u|))) *
            Real.exp (S2 / 2) := by
            refine mul_le_mul (mul_le_mul hE1 hC (l1Mv_nonneg _) (Real.exp_pos _).le) hE2
              (abs_nonneg _) (by positivity)
        _ = Real.exp (S2 + (2 * R n + 1) * Real.log (q.factorial) + K * Real.log (Qc q d n) +
              ∑ u, s u * Real.log |hR q n u|) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [mul_add, sum_add_distrib, ← sum_mul, hsK]
            ring
        _ ≤ T := by
            rw [hT, Real.exp_le_exp]
            simp only [hs] at hG
            linarith
    · rw [det_cblQ_eq_zero_of_prof_ne hfg, l1Mv_zero, mul_zero, zero_mul]
      exact (Real.exp_pos _).le
  rw [hankelPoly_eq_sumQ]
  refine (l1Mv_sum_le _ _).trans ?_
  have hcard := ArchB.card_smSet_le K (IdxQ q n)
  have hcardI : Fintype.card (IdxQ q n) = q * (2 * R n + 1) := by
    simp [IdxQ, Fintype.card_prod, mul_comm]
  rw [hcardI] at hcard
  calc ∑ f ∈ smSet K (IdxQ q n), l1Mv (∑ g ∈ smSet K (IdxQ q n),
        MvPolynomial.C ((EmatQ q n K).submatrix id f).det * ((CblQ q d n).submatrix f g).det *
          MvPolynomial.C ((EmatQ q n K).submatrix id g).det)
      ≤ ∑ _f ∈ smSet K (IdxQ q n), ∑ _g ∈ smSet K (IdxQ q n), T :=
        sum_le_sum fun f hf => (l1Mv_sum_le _ _).trans (sum_le_sum fun g hg => hterm f hf g hg)
    _ = ((smSet K (IdxQ q n)).card : ℝ) ^ 2 * T := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ ((2 : ℝ) ^ (q * (2 * R n + 1))) ^ 2 * T := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) (Real.exp_pos _).le
        exact_mod_cast hcard
    _ = Real.exp (M + errR q d n K) := by
        rw [hT, errR, ← pow_mul]
        have : (2 : ℝ) ^ (q * (2 * R n + 1) * 2) =
            Real.exp ((2 * R n + 1) * (2 * q * Real.log 2)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
          push_cast; ring_nf
        rw [this, ← Real.exp_add]
        congr 1; ring

end TwoAdicWin.Arch
