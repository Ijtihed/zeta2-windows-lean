import RequestProject.Zeta7.Hankel2.ClassType

/-!
# The circle model (paper §8.4): Lemma 8.7 (Counting) and eq. (gdef)

Let `p` be an odd prime, `n ≥ 1` and `u = p/n`.  The residue class `c ∈ [0, p)` sits at the
position `x = c/n` of the circle `ℝ/uℤ`.

* `clsN_eq_ncard`, `zL_eq_ncard`, `hsCnt_eq_ncard`: the class data `(N_c, z_c, h_c)` are *exactly*
  the continuous counts at the positions `c/n` (nodes) and `c/n − 1/(2n)` (zeros), with the
  `hs`-threshold shifted by `1/(2n)`;
* `clsType_eq_ctype`: for a *good* class (no boundary point within `1/n` of `c/n`, and not the
  class of `n/2`) the discrete type is the continuous type `ctype u (c/n)`;
* `card_bad_le`: at most `13` classes are bad;
* **`lemma87_count`** (Lemma 8.7): `|N_t(n, p) − n · meas_t(p/n)| ≤ 13` for every type `t`
  (no exceptional `p/n` near `𝓑` is needed: `meas_t` is defined directly as a measure);
* `lemma87_psi`: `0 ≤ ψ_t(λ) ≤ C_ε (1 + |λ|)` for the types occurring when `u ≥ ε`;
* **`TP_le_gdef`** (eq. (gdef)): for `p² > 6n`, odd `n` and every `λ`,
  `T_p ≤ n · g(λ, p/n, K/n) + 13 C` with `g(λ, u, κ) = λ κ + ∑_t meas_t(u) ψ_t(λ)` and an explicit
  `C` depending only on `λ` and a lower bound `ε ≤ p/n`.
-/

open Finset MeasureTheory

namespace Hankel2.Fam3

open Circle

section Corr

variable {p n : ℕ}

/-- Counting the nodes of the class `c` with a property `P` through the shifts `m`. -/
theorem card_nodes_filter_eq_ncard (hp : 0 < p) (hn : 0 < n) {c : ℕ} (hc : c < p) (P : ℤ → Prop)
    [DecidablePred P] :
    #{k ∈ Fam3PF.nodes n | k % (p : ℤ) = c ∧ P k} =
      {m : ℤ | m ∈ nodeSet ((p : ℝ) / n) ((c : ℝ) / n) ∧ P (c + m * p)}.ncard := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ m : ℤ, m ∈ nodeSet ((p : ℝ) / n) ((c : ℝ) / n) ↔ (c + m * p : ℤ) ∈ Fam3PF.nodes n := by
    intro m
    simp only [nodeSet, Set.mem_setOf_eq, Fam3PF.nodes, Finset.mem_Icc]
    have e : (c : ℝ) / n + m * ((p : ℝ) / n) = ((c + m * p : ℤ) : ℝ) / n := by push_cast; ring
    rw [e, le_div_iff₀ hn', div_le_iff₀ hn']
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have : (-(n : ℤ) : ℝ) ≤ ((c + m * p : ℤ) : ℝ) := by push_cast at h1 ⊢; linarith
        exact_mod_cast this
      · have : ((c + m * p : ℤ) : ℝ) ≤ ((2 * n : ℤ) : ℝ) := by push_cast at h2 ⊢; linarith
        exact_mod_cast this
    · rintro ⟨h1, h2⟩
      have h1' : (-(n : ℤ) : ℝ) ≤ ((c + m * p : ℤ) : ℝ) := by exact_mod_cast h1
      have h2' : ((c + m * p : ℤ) : ℝ) ≤ ((2 * n : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h1' h2' ⊢; constructor <;> linarith
  rw [← Set.ncard_coe_finset]

  have hinj : Function.Injective (fun m : ℤ => (c : ℤ) + m * p) := by
    intro a b h; simp only at h
    have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    exact mul_right_cancel₀ hp' (by linarith)
  rw [← Set.ncard_image_of_injective
    (s := {m : ℤ | m ∈ nodeSet ((p : ℝ) / n) ((c : ℝ) / n) ∧ P (c + m * p)}) hinj]

  congr 1
  ext k
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hk, hkc, hP⟩
    have e := Int.emod_add_mul_ediv k (p : ℤ)
    rw [hkc] at e
    have e' : (c : ℤ) + k / (p : ℤ) * p = k := by linarith
    refine ⟨k / (p : ℤ), ⟨(key _).2 ?_, ?_⟩, e'⟩
    · rw [e']; exact hk
    · rw [e']; exact hP
  · rintro ⟨m, ⟨hm, hP⟩, rfl⟩



    refine ⟨(key m).1 hm, ?_, hP⟩
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hc)


theorem card_clsC_filter (p n c : ℕ) (Q : ℤ → Prop) [DecidablePred Q] :
    #{i ∈ clsC p n c | Q (nodeOf n i)} = #{k ∈ Fam3PF.nodes n | k % (p : ℤ) = c ∧ Q k} := by
  unfold clsC
  refine Finset.card_bij (fun i _ => nodeOf n i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.2 ⟨nodeOf_mem n i, hi⟩
  · intro i _ j _ h
    simp only [nodeOf] at h
    exact Fin.ext (by omega)
  · intro m hm
    obtain ⟨hm1, hm2, hm3⟩ := Finset.mem_filter.1 hm
    have := Finset.mem_Icc.1 hm1
    refine ⟨⟨(m + n).toNat, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, nodeOf]
      rw [show (((m + n).toNat : ℕ) : ℤ) - n = m by omega]; exact ⟨hm2, hm3⟩
    · simp only [nodeOf]; omega

theorem clsN_eq_ncard (hp : 0 < p) (hn : 0 < n) {c : ℕ} (hc : c < p) :
    clsN n p c = (nodeSet ((p : ℝ) / n) ((c : ℝ) / n)).ncard := by
  have := card_nodes_filter_eq_ncard hp hn hc (fun _ => True)
  simp only [and_true, Set.setOf_mem_eq] at this
  exact this

theorem hsCnt_eq_ncard (hp : 0 < p) (hn : 0 < n) {c : ℕ} (hc : c < p) :
    hsCnt p n c = {m : ℤ | m ∈ nodeSet ((p : ℝ) / n) ((c : ℝ) / n) ∧
      (p : ℤ) ≤ 2 * |(c : ℤ) + m * p| - 1}.ncard := by
  unfold hsCnt
  have e : #{i ∈ clsC p n c | hsK p (nodeOf n i) = 1} =
      #{i ∈ clsC p n c | (p : ℤ) ≤ 2 * |nodeOf n i| - 1} := by
    congr 1; refine Finset.filter_congr fun i _ => ?_
    unfold hsK; split_ifs with h <;> simp [h]
  rw [e, card_clsC_filter p n c (fun k => (p : ℤ) ≤ 2 * |k| - 1)]
  exact card_nodes_filter_eq_ncard hp hn hc _

theorem zL_eq_ncard (hp : Odd p) (hn : 0 < n) (c : ℕ) :
    zL n p c = (zSet ((p : ℝ) / n) ((c : ℝ) / n - 1 / (2 * n))).ncard := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rw [zL_eq_count hp]
  set r : ℤ := (c : ℤ) - ((p : ℤ) + 1) / 2
  have hr : (r : ℝ) = c - ((p : ℝ) + 1) / 2 := by
    obtain ⟨k, hk⟩ := hp
    have : ((p : ℤ) + 1) / 2 = k + 1 := by rw [hk]; push_cast; omega
    simp only [r, this]; rw [hk]; push_cast; ring
  have key : ∀ m : ℤ, m ∈ zSet ((p : ℝ) / n) ((c : ℝ) / n - 1 / (2 * n)) ↔ r + m * p ∈ Finset.Ico 0 (n : ℤ) := by
    intro m
    simp only [zSet, Set.mem_setOf_eq, Finset.mem_Ico]
    have e : (c : ℝ) / n - 1 / (2 * n) - (p : ℝ) / n / 2 + m * ((p : ℝ) / n) = ((r + m * p : ℤ) : ℝ) / n := by
      push_cast; rw [hr]; field_simp; ring
    rw [e, le_div_iff₀ hn', div_lt_iff₀ hn', zero_mul, one_mul]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hinj : Function.Injective (fun m : ℤ => r + m * p) := by
    intro a b h; simp only at h
    exact mul_right_cancel₀ hp0.ne' (by linarith)
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective
    (s := zSet ((p : ℝ) / n) ((c : ℝ) / n - 1 / (2 * n))) hinj]
  congr 1
  ext x
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hxr⟩
    obtain ⟨d, hd⟩ := (Int.modEq_iff_dvd.1 hxr.symm)
    refine ⟨d, (key d).2 ?_, ?_⟩
    · rw [show r + d * p = x by linarith]; exact hx
    · linarith
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(key m).1 hm, ?_⟩
    exact Int.modEq_iff_dvd.2 ⟨-m, by ring⟩

/-- A class is **good** if no boundary point lies within `1/n` of its position `c/n` and it is not
the class of `n/2`. -/
def Good (p n c : ℕ) : Prop :=
  (∀ e ∈ Ebad ((p : ℝ) / n), e ∉ Set.Icc (((c : ℝ) - 1) / n) (((c : ℝ) + 1) / n)) ∧ gC p n c = 0

/-- **For a good class the discrete type is the continuous type.** -/
theorem clsType_eq_ctype (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) {c : ℕ} (hc : c < p)
    (hg : Good p n c) : clsType p n c = ctype ((p : ℝ) / n) ((c : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set u := (p : ℝ) / n
  set x := (c : ℝ) / n
  have hsub : ∀ a b : ℝ, ((c : ℝ) - 1) / n ≤ a → b ≤ ((c : ℝ) + 1) / n →
      ∀ e ∈ Ebad u, e ∉ Set.Icc a b := by
    intro a b ha hb e he hmem
    exact hg.1 e he ⟨ha.trans hmem.1, hmem.2.trans hb⟩
  have hδ : 1 / (2 * (n : ℝ)) ≤ 1 / n := by
    rw [div_le_div_iff₀ (by positivity) hn']; linarith
  have hx1 : ((c : ℝ) - 1) / n = x - 1 / n := by simp only [x]; ring
  have hx2 : ((c : ℝ) + 1) / n = x + 1 / n := by simp only [x]; ring
  -- zeros
  have h0 : (0 : ℝ) ≤ 1 / (2 * n) := by positivity
  have h1 : (0 : ℝ) ≤ 1 / n := by positivity
  have hz : zL n p c = (zSet u x).ncard := by
    rw [zL_eq_ncard hodd hn c]
    have := ctype_const_of_avoid (u := u) (x := x - 1 / (2 * n)) (x' := x) (by linarith)
      (hsub _ _ (by rw [hx1]; linarith) (by rw [hx2]; linarith))
    exact congrArg (fun t : CType => t.2.1) this
  -- hs-nodes
  have hh : hsCnt p n c = (hsSet u x).ncard := by
    rw [hsCnt_eq_ncard hp.pos hn hc]
    congr 1
    ext m
    simp only [Set.mem_setOf_eq, hsSet]
    refine and_congr_right fun hm => ?_
    set k : ℤ := (c : ℤ) + m * p
    have hy : x + m * u = (k : ℝ) / n := by simp only [x, u, k]; push_cast; ring
    have hk : ((p : ℤ) ≤ 2 * |k| - 1) ↔ u / 2 + 1 / (2 * n) ≤ |x + m * u| := by
      rw [hy, abs_div, abs_of_pos hn']
      have : u / 2 + 1 / (2 * n) = ((p : ℝ) + 1) / 2 / n := by simp only [u]; field_simp
      rw [this, div_le_div_iff_of_pos_right hn']
      constructor
      · intro h
        have : ((p : ℤ) : ℝ) ≤ ((2 * |k| - 1 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      · intro h
        have : ((p : ℤ) : ℝ) + 1 ≤ 2 * ((|k| : ℤ) : ℝ) := by push_cast; linarith

        have : (p : ℤ) + 1 ≤ 2 * |k| := by exact_mod_cast this
        linarith
    rw [hk]
    constructor
    · intro h; linarith

    · intro h
      by_contra hlt
      push_neg at hlt
      rcases le_or_gt 0 (x + m * u) with hy0 | hy0
      · rw [abs_of_nonneg hy0] at h hlt
        refine hg.1 (bpt u 2 + ((-m : ℤ) : ℝ) * u) (bpt_add_mem_Ebad u 2 (-m)) ⟨?_, ?_⟩
        · rw [hx1, bpt2]; push_cast; linarith
        · rw [hx2, bpt2]; push_cast
          linarith
      · rw [abs_of_neg hy0] at h hlt
        refine hg.1 (bpt u 2 + ((-m - 1 : ℤ) : ℝ) * u) (bpt_add_mem_Ebad u 2 (-m - 1)) ⟨?_, ?_⟩
        · rw [hx1, bpt2]; push_cast
          linarith
        · rw [hx2, bpt2]; push_cast; linarith
  simp only [clsType, ctype]
  rw [clsN_eq_ncard hp.pos hn hc, hz, hh]


/-- The bad classes. -/
noncomputable def badSet (p n : ℕ) : Finset ℕ := by
  classical exact (range p).filter fun c => ¬ Good p n c

/-- The classes whose position is within `1/n` of the boundary point `b_i` (mod `u`). -/
noncomputable def nearSet (p n : ℕ) (i : Fin 4) : Finset ℕ :=
  (range 3).image fun d : ℕ => ((⌈(n : ℝ) * bpt ((p : ℝ) / n) i - 1⌉ + (d : ℤ)) % (p : ℤ)).toNat

theorem card_nearSet_le (p n : ℕ) (i : Fin 4) : (nearSet p n i).card ≤ 3 :=
  (Finset.card_image_le).trans (by simp)

theorem mem_nearSet (hn : 0 < n) {c : ℕ} (hc : c < p) {i : Fin 4} {m : ℤ}
    (h : bpt ((p : ℝ) / n) i + m * ((p : ℝ) / n) ∈ Set.Icc (((c : ℝ) - 1) / n) (((c : ℝ) + 1) / n)) :
    c ∈ nearSet p n i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set B := (n : ℝ) * bpt ((p : ℝ) / n) i
  obtain ⟨h1, h2⟩ := h
  have e : bpt ((p : ℝ) / n) i + m * ((p : ℝ) / n) = (B + m * p) / n := by
    simp only [B]; field_simp
  rw [e] at h1 h2
  rw [div_le_div_iff_of_pos_right hn'] at h1 h2
  set z : ℤ := c - m * p
  have hz1 : B - 1 ≤ z := by simp only [z]; push_cast; linarith
  have hz2 : (z : ℝ) ≤ B + 1 := by simp only [z]; push_cast; linarith
  set z0 := ⌈B - 1⌉
  have hz0 : z0 ≤ z := Int.ceil_le.2 hz1
  have hz3 : z < z0 + 3 := by
    have := Int.le_ceil (B - 1)
    have : (z : ℝ) < z0 + 3 := by linarith
    exact_mod_cast this
  unfold nearSet
  rw [Finset.mem_image]
  refine ⟨(z - z0).toNat, Finset.mem_range.2 (by omega), ?_⟩
  rw [show z0 + (((z - z0).toNat : ℕ) : ℤ) = c + (-m) * p by
    rw [Int.toNat_of_nonneg (by omega)]; simp only [z]; ring]
  rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hc)]
  simp

theorem card_gset_le (hp : p.Prime) (hp2 : p ≠ 2) :
    ((range p).filter fun c => gC p n c ≠ 0).card ≤ 1 := by
  refine Finset.card_le_one.2 fun c hc c' hc' => ?_
  simp only [Finset.mem_filter, Finset.mem_range, gC, ne_eq, ite_eq_right_iff, one_ne_zero,
    imp_false, not_not] at hc hc'
  have hd : (p : ℤ) ∣ 2 * ((c' : ℤ) - c) := by
    have := dvd_sub hc.2 hc'.2; rw [show (n : ℤ) - 2 * c - ((n : ℤ) - 2 * c') = 2 * ((c' : ℤ) - c) by ring]
      at this; exact this
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h2 | h2
  · have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
    have := hp.two_le; omega
  · have := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    omega

theorem badSet_subset (hn : 0 < n) :
    badSet p n ⊆ (Finset.univ.biUnion fun i => nearSet p n i) ∪
      (range p).filter fun c => gC p n c ≠ 0 := by
  classical
  intro c hc
  simp only [badSet, Finset.mem_filter, Finset.mem_range, Good, not_and_or, not_forall,
    not_not] at hc
  obtain ⟨hcp, h⟩ := hc
  rcases h with ⟨e, he, hmem⟩ | h
  · obtain ⟨i, m, rfl⟩ := he
    refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      mem_nearSet hn hcp hmem⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hcp, h⟩)

/-- **At most 13 classes are bad.** -/
theorem card_bad_le (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) : (badSet p n).card ≤ 13 := by
  classical
  refine (Finset.card_le_card (badSet_subset hn)).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 : (Finset.univ.biUnion fun i => nearSet p n i).card ≤ 12 :=
    (Finset.card_biUnion_le).trans (by
      calc ∑ i : Fin 4, (nearSet p n i).card ≤ ∑ _i : Fin 4, 3 :=
            Finset.sum_le_sum fun i _ => card_nearSet_le p n i
        _ = 12 := by simp)
  have h2 := card_gset_le (n := n) hp hp2
  omega


/-! ### Lemma 8.7 (Counting) -/

/-- `N_t(n, p)`: the number of residue classes mod `p` of type `t`. -/
noncomputable def Ncount (p n : ℕ) (t : CType) : ℕ := #{c ∈ range p | clsType p n c = t}

/-- The good classes whose continuous type is `t`. -/
noncomputable def goodT (p n : ℕ) (t : CType) : Finset ℕ := by
  classical exact (range p).filter fun c => Good p n c ∧ ctype ((p : ℝ) / n) ((c : ℝ) / n) = t

theorem ctype_eq_of_good (hn : 0 < n) {c : ℕ} (hg : Good p n c) {x : ℝ}
    (hx : x ∈ Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n)) :
    ctype ((p : ℝ) / n) x = ctype ((p : ℝ) / n) ((c : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (ctype_const_of_avoid hx.1 fun e he hmem => hg.1 e he ⟨?_, ?_⟩).symm
  · have : ((c : ℝ) - 1) / n ≤ (c : ℝ) / n := div_le_div_of_nonneg_right (by linarith) hn'.le
    linarith [hmem.1]
  · linarith [hmem.2, hx.2]

theorem mem_Ico_u {c : ℕ} (hn : 0 < n) (hc : c < p) {x : ℝ}
    (hx : x ∈ Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n)) : x ∈ Set.Ico 0 ((p : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨le_trans (by positivity) hx.1, lt_of_lt_of_le hx.2 ?_⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) hn'.le

theorem volume_iUnion_Ico (hn : 0 < n) (F : Finset ℕ) :
    volume (⋃ c ∈ F, Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n)) = F.card * ENNReal.ofReal (1 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun c _ => by
      rw [Real.volume_Ico, show ((c : ℝ) + 1) / n - (c : ℝ) / n = 1 / n by ring]]
    simp
  · intro c _ c' _ hne
    simp only [Function.onFun]
    rw [Set.Ico_disjoint_Ico]
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((c : ℝ) + 1) / n ≤ (c' : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hn'.le
      exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
    · have : ((c' : ℝ) + 1) / n ≤ (c : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hn'.le
      exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
  · intro c _; exact measurableSet_Ico

theorem volume_Ico_u_ne_top (u : ℝ) (t : CType) :
    volume {x ∈ Set.Ico 0 u | ctype u x = t} ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    (measure_mono fun x hx => hx.1)

/-- `#{good classes of type t} ≤ n · meas_t(p/n)`. -/
theorem card_goodT_le (hn : 0 < n) (t : CType) :
    ((goodT p n t).card : ℝ) ≤ n * meas ((p : ℝ) / n) t := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : (⋃ c ∈ goodT p n t, Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n)) ⊆
      {x ∈ Set.Ico 0 ((p : ℝ) / n) | ctype ((p : ℝ) / n) x = t} := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hx⟩ := hx
    simp only [goodT, Finset.mem_filter, Finset.mem_range] at hc
    exact ⟨mem_Ico_u hn hc.1 hx, (ctype_eq_of_good hn hc.2.1 hx).trans hc.2.2⟩
  have h := ENNReal.toReal_mono (volume_Ico_u_ne_top _ t) (measure_mono hsub)
  rw [volume_iUnion_Ico hn, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  unfold meas
  simp only [ENNReal.toReal_natCast] at h
  rw [← div_le_iff₀' hn']; rw [mul_one_div] at h; exact h

/-- `n · meas_t(p/n) ≤ #{good classes of type t} + #{bad classes}`. -/
theorem meas_le_card (hn : 0 < n) (t : CType) :
    n * meas ((p : ℝ) / n) t ≤ (goodT p n t).card + (badSet p n).card := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : {x ∈ Set.Ico 0 ((p : ℝ) / n) | ctype ((p : ℝ) / n) x = t} ⊆
      ⋃ c ∈ goodT p n t ∪ badSet p n, Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n) := by
    intro x hx
    obtain ⟨⟨hx0, hxu⟩, ht⟩ := hx
    set c := ⌊(n : ℝ) * x⌋₊
    have hnx : 0 ≤ (n : ℝ) * x := by positivity
    have hc1 : (c : ℝ) ≤ n * x := Nat.floor_le hnx
    have hc2 : (n : ℝ) * x < c + 1 := Nat.lt_floor_add_one _
    have hxc : x ∈ Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n) :=
      ⟨by rw [div_le_iff₀ hn']; linarith, by rw [lt_div_iff₀ hn']; linarith⟩
    have hcp : c < p := by
      have : (n : ℝ) * x < p := by rw [lt_div_iff₀ hn'] at hxu; linarith
      exact_mod_cast (lt_of_le_of_lt hc1 this)
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨c, ?_, hxc⟩
    by_cases hg : Good p n c
    · refine Finset.mem_union_left _ ?_
      simp only [goodT, Finset.mem_filter, Finset.mem_range]
      exact ⟨hcp, hg, (ctype_eq_of_good hn hg hxc).symm.trans ht⟩
    · refine Finset.mem_union_right _ ?_
      simp only [badSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨hcp, hg⟩
  have h1 := measure_mono (μ := (volume : Measure ℝ)) hsub
  have h2 := measure_biUnion_finset_le (μ := (volume : Measure ℝ)) (goodT p n t ∪ badSet p n)
    (fun c => Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n))
  have h3 : ∑ c ∈ goodT p n t ∪ badSet p n, volume (Set.Ico ((c : ℝ) / n) (((c : ℝ) + 1) / n)) =
      (goodT p n t ∪ badSet p n).card * ENNReal.ofReal (1 / n) := by
    rw [Finset.sum_congr rfl fun c _ => by
      rw [Real.volume_Ico, show ((c : ℝ) + 1) / n - (c : ℝ) / n = 1 / n by ring]]
    simp
  rw [h3] at h2
  have h4 := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) (h1.trans h2)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast] at h4
  have h5 : ((goodT p n t ∪ badSet p n).card : ℝ) ≤ (goodT p n t).card + (badSet p n).card := by
    exact_mod_cast Finset.card_union_le _ _
  unfold meas
  have : (volume {x ∈ Set.Ico 0 ((p : ℝ) / n) | ctype ((p : ℝ) / n) x = t}).toReal * n ≤
      ((goodT p n t ∪ badSet p n).card : ℝ) := by
    rw [← le_div_iff₀ hn']; rw [mul_one_div] at h4; exact h4
  linarith

/-- **Lemma 8.7 (Counting).** For every odd prime `p`, every `n ≥ 1` and every type `t`, the
number `N_t(n, p)` of residue classes of type `t` satisfies `|N_t − n · meas_t(p/n)| ≤ 13`. -/
theorem lemma87_count (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) (t : CType) :
    |(Ncount p n t : ℝ) - n * meas ((p : ℝ) / n) t| ≤ 13 := by
  classical
  have hbad : ((badSet p n).card : ℝ) ≤ 13 := by exact_mod_cast card_bad_le hp hp2 hn
  have hG1 : goodT p n t ⊆ (range p).filter fun c => clsType p n c = t := by
    intro c hc
    simp only [goodT, Finset.mem_filter, Finset.mem_range] at hc ⊢
    exact ⟨hc.1, (clsType_eq_ctype hp hp2 hn hc.1 hc.2.1).trans hc.2.2⟩
  have hG2 : ((range p).filter fun c => clsType p n c = t) ⊆ goodT p n t ∪ badSet p n := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    by_cases hg : Good p n c
    · refine Finset.mem_union_left _ ?_
      simp only [goodT, Finset.mem_filter, Finset.mem_range]
      exact ⟨hc.1, hg, (clsType_eq_ctype hp hp2 hn hc.1 hg).symm.trans hc.2⟩
    · exact Finset.mem_union_right _ (by
        simp only [badSet, Finset.mem_filter, Finset.mem_range]; exact ⟨hc.1, hg⟩)
  have e1 : ((goodT p n t).card : ℝ) ≤ Ncount p n t := by
    unfold Ncount; exact_mod_cast Finset.card_le_card hG1
  have e2 : (Ncount p n t : ℝ) ≤ (goodT p n t).card + (badSet p n).card := by
    unfold Ncount
    exact_mod_cast (Finset.card_le_card hG2).trans (Finset.card_union_le _ _)
  have e3 := card_goodT_le (p := p) hn t
  have e4 := meas_le_card (p := p) hn t
  rw [abs_le]; constructor <;> linarith


/-! ### Eq. (gdef) -/

/-- **`g(λ, u, κ) = λ κ + ∑_t meas_t(u) ψ_t(λ)`** (paper eq. (gdef)). -/
noncomputable def gfun (lam u κ : ℝ) : ℝ := lam * κ + Gpot (fun t => psiT t 0 lam) u

/-- The constant `C_ε(λ) = N_ε(16 N_ε + 50) + 4 N_ε |λ|`, `N_ε = 3/ε + 2`, of Lemma 8.7. -/
noncomputable def Ceps (ε lam : ℝ) : ℝ :=
  (3 / ε + 2) * (16 * (3 / ε + 2) + 50) + 4 * (3 / ε + 2) * |lam|

theorem Ceps_nonneg {ε : ℝ} (hε : 0 < ε) (lam : ℝ) : 0 ≤ Ceps ε lam := by
  unfold Ceps; positivity

theorem clsN_le_eps (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) (hεp : ε * n ≤ p) {c : ℕ} (hc : c < p) :
    (clsN n p c : ℝ) ≤ 3 / ε + 2 := by
  have h := clsN_bounds (n := n) hp hc
  rw [abs_lt] at h
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have e1 : 3 * (n : ℝ) / p ≤ 3 / ε := by
    rw [div_le_div_iff₀ hp' hε]; linarith
  have e2 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp']; exact hp1
  have : (3 * (n : ℝ) + 1) / p = 3 * n / p + 1 / p := by ring
  linarith

theorem psi_bound_mono {N M lam : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) :
    N * (16 * N + 50) + 4 * N * |lam| ≤ M * (16 * M + 50) + 4 * M * |lam| := by
  have := abs_nonneg lam
  nlinarith

open Classical in
/-- The good classes contribute at most `n · ∑_t meas_t(u) ψ_t(λ)`. -/
theorem sum_good_le (hn : 0 < n) (hp : 0 < p) (lam : ℝ) :
    ∑ c ∈ (range p).filter (fun c => Good p n c), psiT (ctype ((p : ℝ) / n) ((c : ℝ) / n)) 0 lam ≤
      n * Gpot (fun t => psiT t 0 lam) ((p : ℝ) / n) := by
  classical
  have hu : (0 : ℝ) < (p : ℝ) / n := by positivity
  rw [Gpot_eq_sum _ hu le_rfl, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (range p).filter fun c => Good p n c)
    (g := fun c => ctype ((p : ℝ) / n) ((c : ℝ) / n))
    (f := fun c => psiT (ctype ((p : ℝ) / n) ((c : ℝ) / n)) 0 lam)
    (t := typeBox ((p : ℝ) / n)) fun c _ => ctype_mem_box hu le_rfl _]

  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.1 hc).2], Finset.sum_const,
    nsmul_eq_mul, Finset.filter_filter]
  have e : ((range p).filter fun c => Good p n c ∧ ctype ((p : ℝ) / n) ((c : ℝ) / n) = t) =
      goodT p n t := by unfold goodT; congr
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (card_goodT_le hn t) (psiT_nonneg _ _ _)

/-- **Eq. (gdef).** For an odd prime `p` with `p² > 6n` and `p ≥ εn`, odd `n`, every `K` and every
`λ`: `T_p ≤ n · g(λ, p/n, K/n) + 13 C_ε(λ)`. -/
theorem TP_le_gdef (hp : p.Prime) (hp2 : p ≠ 2) (hn : n % 2 = 1) (h6 : 6 * n < p ^ 2) (K : ℕ)
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (hεp : ε * n ≤ p) :
    ∀ t : ℤ, TP p n K = t →
      (t : ℝ) ≤ n * gfun lam ((p : ℝ) / n) ((K : ℝ) / n) + 13 * Ceps ε lam := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  set ψc : ℕ → ℝ := fun c => if Good p n c then psiT (ctype ((p : ℝ) / n) ((c : ℝ) / n)) 0 lam
    else Ceps ε lam
  have hψ : ∀ c < p, ∀ S : ℕ, ∀ v : ℤ, Vc p n c S = v → (v : ℝ) - lam * S ≤ ψc c := by
    intro c hc S v hv
    simp only [ψc]
    split_ifs with hg
    · have := Vc_sub_le_psiT h6 hn lam S v hv
      rwa [clsType_eq_ctype hp hp2 hn0 hc hg, hg.2] at this
    · refine (Vc_sub_le_crude h6 hn lam S v hv).trans ?_
      exact psi_bound_mono (Nat.cast_nonneg _) (clsN_le_eps hp.pos hε hεp hc)
  intro t ht
  have h1 := TP_le_dual hp2 h6 K lam ψc hψ t ht
  have h2 : ∑ c ∈ range p, ψc c ≤ n * Gpot (fun t => psiT t 0 lam) ((p : ℝ) / n) +
      13 * Ceps ε lam := by
    simp only [ψc]
    rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    have hb : (((range p).filter fun c => ¬ Good p n c).card : ℝ) ≤ 13 := by
      have := card_bad_le hp hp2 hn0; unfold badSet at this; exact_mod_cast this
    have := sum_good_le hn0 hp.pos lam
    have := mul_le_mul_of_nonneg_right hb (Ceps_nonneg hε lam)
    linarith
  unfold gfun
  have e : lam * (K : ℝ) = n * (lam * ((K : ℝ) / n)) := by field_simp
  rw [e] at h1
  nlinarith

theorem nodeSet_finite {u : ℝ} (hu : 0 < u) (x : ℝ) : (nodeSet u x).Finite := by
  refine (Finset.finite_toSet (Finset.Icc ⌈(-1 - x) / u⌉ ⌊(2 - x) / u⌋)).subset fun m hm => ?_
  obtain ⟨h1, h2⟩ := hm
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact ⟨Int.ceil_le.2 (by rw [div_le_iff₀ hu]; linarith),
    Int.le_floor.2 (by rw [le_div_iff₀ hu]; linarith)⟩

/-- **Lemma 8.7, the bound on `ψ_t`.** For `u ≥ ε > 0` the types `t` of positions satisfy
`0 ≤ ψ_t(λ) ≤ C_ε(λ) ≤ C'_ε (1 + |λ|)`. -/
theorem lemma87_psi {ε u : ℝ} (hε : 0 < ε) (hεu : ε ≤ u) (x : ℝ) (g : ℕ) (lam : ℝ) :
    0 ≤ psiT (ctype u x) g lam ∧ psiT (ctype u x) g lam ≤ Ceps ε lam ∧
      Ceps ε lam ≤ ((3 / ε + 2) * (16 * (3 / ε + 2) + 50) + 4 * (3 / ε + 2)) * (1 + |lam|) := by
  have hu : 0 < u := lt_of_lt_of_le hε hεu
  refine ⟨psiT_nonneg _ _ _, ?_, ?_⟩
  · have hh : (ctype u x).2.2 ≤ (ctype u x).1 :=
      Set.ncard_le_ncard (fun m hm => hm.1) (nodeSet_finite hu x)
    refine (psiT_le _ g lam hh).trans (psi_bound_mono (Nat.cast_nonneg _) ?_)
    have := ncard_nodeSet_le hu x
    have : 3 / u ≤ 3 / ε := div_le_div_of_nonneg_left (by norm_num) hε hεu
    simp only [ctype]; linarith
  · unfold Ceps
    have h0 : 0 ≤ (3 / ε + 2) * (16 * (3 / ε + 2) + 50) := by positivity
    have h1 : 0 ≤ 4 * (3 / ε + 2) := by positivity
    have := abs_nonneg lam
    nlinarith

end Corr

end Hankel2.Fam3
