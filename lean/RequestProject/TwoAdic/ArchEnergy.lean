import RequestProject.TwoAdic.ArchRed
import RequestProject.Frame.LogEnergy
import RequestProject.Zeta35.ArchCont3
import RequestProject.Zeta7.Hankel2.LogCND

/-!
# The discrete energy against the profile `σ = (q/2) 1_𝒪` (II Theorem 4.1)

For even `n = 2h`, the reference profile is `σ₀ = q/2` on the outer nodes
`𝒪 = {h < |k| ≤ 3h}` and `0` on the middle nodes `|k| ≤ h` (`sig0`); its mass is `qn = K`.

* `g_le`: the gradient `g_k = ln|h_k| + 2 (B σ₀)_k` satisfies `g_k ≤ 2q(1 + ln 2R)` at every node.
  The `n` zero factors `|k − w_j|` (`w_j` the half-integers in the middle third) are dominated by
  the distances to the `n + 1` middle nodes (an injection `w_j ↦ w_j ∓ 1/2` away from `k`), and
  on `𝒪` the kernel `B(d) = ½ ln(1 + d²)` exceeds `ln|d|` by at most `1/|d|`.  This is the
  discrete form of `P_σ = U + 2𝓛σ ≡ 0` (zero gap).
* `EB_le_lin`: linearisation at `σ₀` (the log kernel is conditionally negative definite,
  `Hankel2.quadratic_log_le_linearization`): `E_B(s) ≤ ∑_k s_k g_k − ⟨σ₀, B σ₀⟩`.
* `quad_sig0_ge`: `⟨σ₀, B σ₀⟩ ≥ q²n² ln n − F n² − 75 q² n (1 + ln n)`, from
  `PadicWin.LogEnergy.outer_energy_ge` (`⟨1_𝒪, 𝓛1_𝒪⟩ = 9 ln 3 − 8 ln 2 − 6`).
* **`EB_le`**: for every profile `0 ≤ s ≤ q` with `∑ s = qn`,
  `E_B(s) ≤ −q²n² ln n + F n² + 100 q² n (1 + ln n)`, `F = (q²/4)(6 + 8 ln 2 − 9 ln 3)`.
-/

open Finset PadicWin Hankel2

namespace TwoAdicWin.Arch

theorem Bk_le_log_add_inv {d : ℝ} (hd : d ≠ 0) :
    ArchB.Bk d ≤ Real.log |d| + 1 / |d| := by
  have h1 := Zeta35.Arch.Bk_le_log_one_add_abs d
  have hd' : 0 < |d| := abs_pos.2 hd
  have h2 : Real.log (1 + |d|) = Real.log |d| + Real.log (1 + 1 / |d|) := by
    rw [← Real.log_mul hd'.ne' (by positivity)]
    congr 1; field_simp; ring
  have h3 : Real.log (1 + 1 / |d|) ≤ 1 / |d| := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / |d| by positivity)
    linarith
  linarith

theorem Bk_zero' : ArchB.Bk 0 = 0 := by simp [ArchB.Bk]

/-- The middle nodes `|k| ≤ h` are the nodes outside `𝒪`. -/
theorem mem_Oset_iff {h : ℕ} {k : ℤ} (hk : k ∈ nodes (2 * h)) :
    k ∈ LogEnergy.Oset h ↔ ¬ (-(h : ℤ) ≤ k ∧ k ≤ h) := by
  have hR : (R (2 * h) : ℤ) = 3 * h := by unfold R; push_cast; omega
  simp only [nodes, mem_Icc] at hk
  rw [hR] at hk
  simp only [LogEnergy.Oset, mem_union, mem_Icc]
  omega

theorem Oset_subset (h : ℕ) : LogEnergy.Oset h ⊆ nodes (2 * h) := by
  intro k hk
  have hR : (R (2 * h) : ℤ) = 3 * h := by unfold R; push_cast; omega
  simp only [LogEnergy.Oset, mem_union, mem_Icc] at hk
  simp only [nodes, mem_Icc, hR]
  omega

/-- **The zero factors are dominated by the middle nodes.** -/
theorem zeros_le_middle (h : ℕ) (k : ℤ) :
    ∑ j ∈ range (2 * h), Real.log |(((Dom.ez (2 * h) j k : ℚ) / 2 : ℚ) : ℝ)| ≤
      ∑ k' ∈ ((nodes (2 * h)).erase k).filter (fun k' => k' ∉ LogEnergy.Oset h),
        Real.log |((k' - k : ℤ) : ℝ)| := by
  set phi : ℕ → ℤ := fun j => if (j : ℤ) - h < k then (j : ℤ) - h else (j : ℤ) - h + 1 with hphi
  have hR : (R (2 * h) : ℤ) = 3 * h := by unfold R; push_cast; omega
  have hmaps : ∀ j ∈ range (2 * h), phi j ∈
      ((nodes (2 * h)).erase k).filter (fun k' => k' ∉ LogEnergy.Oset h) := by
    intro j hj
    rw [mem_range] at hj
    have hmem : phi j ∈ nodes (2 * h) := by
      simp only [nodes, mem_Icc, hR, hphi]; split_ifs <;> omega
    rw [mem_filter, mem_erase, mem_Oset_iff hmem]
    refine ⟨⟨?_, hmem⟩, ?_⟩
    · simp only [hphi]; split_ifs <;> omega
    · simp only [hphi]; split_ifs <;> omega
  have hinj : Set.InjOn phi (range (2 * h) : Set ℕ) := by
    intro a _ b _ hab
    simp only [hphi] at hab
    split_ifs at hab <;> omega
  have hterm : ∀ j ∈ range (2 * h), Real.log |(((Dom.ez (2 * h) j k : ℚ) / 2 : ℚ) : ℝ)| ≤
      Real.log |((phi j - k : ℤ) : ℝ)| := by
    intro j _
    have hpos : 0 < |(((Dom.ez (2 * h) j k : ℚ) / 2 : ℚ) : ℝ)| := by
      have := abs_ez_half_ge (n := 2 * h) ⟨h, by ring⟩ j k; linarith
    refine Real.log_le_log hpos ?_
    have e : (((Dom.ez (2 * h) j k : ℚ) / 2 : ℚ) : ℝ) = ((2 * (j : ℤ) + 1 - 2 * k - 2 * h : ℤ) : ℝ) / 2 := by
      unfold Dom.ez; push_cast; ring
    rw [e, abs_div, abs_two]
    simp only [hphi]
    split_ifs with hc
    · have h1 : |((2 * (j : ℤ) + 1 - 2 * k - 2 * h : ℤ) : ℝ)| = ((2 * k - 2 * j - 1 + 2 * h : ℤ) : ℝ) := by
        rw [← Int.cast_abs, abs_of_neg (by omega)]; push_cast; ring
      have h2 : |(((j : ℤ) - h - k : ℤ) : ℝ)| = ((k - j + h : ℤ) : ℝ) := by
        rw [← Int.cast_abs, abs_of_neg (by omega)]; push_cast; ring
      rw [h1, h2]; push_cast; linarith
    · have h1 : |((2 * (j : ℤ) + 1 - 2 * k - 2 * h : ℤ) : ℝ)| = ((2 * j + 1 - 2 * k - 2 * h : ℤ) : ℝ) := by
        rw [← Int.cast_abs, abs_of_pos (by omega)]
      have h2 : |(((j : ℤ) - h + 1 - k : ℤ) : ℝ)| = ((j - h + 1 - k : ℤ) : ℝ) := by
        rw [← Int.cast_abs, abs_of_pos (by omega)]
      rw [h1, h2]; push_cast; linarith
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_image (f := fun k' => Real.log |((k' - k : ℤ) : ℝ)|) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun k' hk' _ => ?_
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    exact hmaps j hj
  · have hne : k' - k ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase (mem_filter.1 hk').1)
    exact Real.log_nonneg (by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne)

/-- **The gradient bound** `g_k = ln|h_k| + q ∑_{k' ∈ 𝒪} B(k − k') ≤ 2q(1 + ln 2R)`. -/
theorem g_le (h q : ℕ) {k : ℤ} (hk : k ∈ nodes (2 * h)) :
    Real.log |((Hk q (2 * h) k 0 : ℚ) : ℝ)| +
        q * ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((k : ℝ) - k') ≤
      2 * q * (1 + Real.log (2 * R (2 * h))) := by
  rw [log_abs_Hk_zero ⟨h, by ring⟩]
  set O := LogEnergy.Oset h
  set N := nodes (2 * h)
  have hsplit := sum_filter_add_sum_filter_not (N.erase k) (fun k' => k' ∈ O)
    (fun k' => Real.log |((k' - k : ℤ) : ℝ)|)
  have hfO : (N.erase k).filter (fun k' => k' ∈ O) = O.erase k := by
    ext x; simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, Oset_subset h h3⟩, h3⟩
  rw [hfO] at hsplit
  have hB : ∑ k' ∈ O, ArchB.Bk ((k : ℝ) - k') = ∑ k' ∈ O.erase k, ArchB.Bk ((k : ℝ) - k') := by
    rw [sum_erase]; simp [Bk_zero']
  rw [hB]
  have hmid := zeros_le_middle h k
  have hout : ∑ k' ∈ O.erase k, ArchB.Bk ((k : ℝ) - k') ≤
      ∑ k' ∈ O.erase k, Real.log |((k' - k : ℤ) : ℝ)| + ∑ k' ∈ N.erase k, 1 / |((k - k' : ℤ) : ℝ)| := by
    have h1 : ∑ k' ∈ O.erase k, ArchB.Bk ((k : ℝ) - k') ≤
        ∑ k' ∈ O.erase k, (Real.log |((k' - k : ℤ) : ℝ)| + 1 / |((k - k' : ℤ) : ℝ)|) := by
      refine sum_le_sum fun k' hk' => ?_
      have hne : (k : ℝ) - k' ≠ 0 := by
        have := ne_of_mem_erase hk'; intro h0; exact this (by exact_mod_cast (sub_eq_zero.1 h0).symm)
      have := Bk_le_log_add_inv hne
      have e1 : |((k' - k : ℤ) : ℝ)| = |(k : ℝ) - k'| := by push_cast; rw [abs_sub_comm]
      have e2 : |((k - k' : ℤ) : ℝ)| = |(k : ℝ) - k'| := by push_cast; rfl
      rw [e1, e2]; exact this
    have h2 : ∑ k' ∈ O.erase k, 1 / |((k - k' : ℤ) : ℝ)| ≤ ∑ k' ∈ N.erase k, 1 / |((k - k' : ℤ) : ℝ)| :=
      sum_le_sum_of_subset_of_nonneg (erase_subset_erase k (Oset_subset h))
        (fun _ _ _ => by positivity)
    rw [sum_add_distrib] at h1
    linarith
  have hharm : ∑ k' ∈ N.erase k, 1 / |((k - k' : ℤ) : ℝ)| ≤ 2 * (1 + Real.log (2 * R (2 * h))) :=
    Zeta35.Arch.sum_inv_dist_le3 (2 * h) k hk
  have hq : (0 : ℝ) ≤ q := by positivity
  have e : (((2 * h : ℕ)) : ℕ) = 2 * h := rfl
  nlinarith [mul_le_mul_of_nonneg_left hmid hq, mul_le_mul_of_nonneg_left hout hq,
    mul_le_mul_of_nonneg_left hharm hq]

/-! ### Linearisation at the reference profile -/

/-- The reference profile `σ₀ = (q/2) 1_𝒪` on the node index set. -/
noncomputable def sig0 (q h : ℕ) (u : Fin (2 * R (2 * h) + 1)) : ℝ :=
  if nodeOf (2 * h) u ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0

theorem Bk_eq (x : ℝ) : ArchB.Bk x = Real.log (1 + x ^ 2) / 2 := rfl

theorem nodeOf_mem (n : ℕ) (u : Fin (2 * R n + 1)) : nodeOf n u ∈ nodes n := by
  simp only [nodes, mem_Icc, nodeOf]
  have := u.isLt
  omega

theorem sum_nodeOf_eq (n : ℕ) {M : Type*} [AddCommMonoid M] (F : ℤ → M) :
    ∑ u : Fin (2 * R n + 1), F (nodeOf n u) = ∑ k ∈ nodes n, F k :=
  (sum_nodes_eq' n F).symm

theorem card_Oset (h : ℕ) : (LogEnergy.Oset h).card = 4 * h := by
  unfold LogEnergy.Oset
  rw [card_union_of_disjoint (LogEnergy.Oset_disj h), Int.card_Icc, Int.card_Icc]
  omega

theorem sum_sig0 (q h : ℕ) : ∑ u, sig0 q h u = q * (2 * h) := by
  unfold sig0
  rw [sum_nodeOf_eq (2 * h) (fun k => if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0),
    ← sum_filter, sum_const, nsmul_eq_mul]
  have : (nodes (2 * h)).filter (fun k => k ∈ LogEnergy.Oset h) = LogEnergy.Oset h := by
    ext x; simp only [mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨Oset_subset h hx, hx⟩⟩
  rw [this, card_Oset]; push_cast; ring

theorem sig0_nonneg (q h : ℕ) (u : Fin (2 * R (2 * h) + 1)) : 0 ≤ sig0 q h u := by
  unfold sig0; split_ifs <;> positivity

/-- `2 (B σ₀)_u = q ∑_{k' ∈ 𝒪} B(k_u − k')`. -/
theorem two_Bsig0 (q h : ℕ) (u : Fin (2 * R (2 * h) + 1)) :
    2 * ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v =
      q * ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - k') := by
  unfold sig0
  rw [sum_nodeOf_eq (2 * h) (fun k => ArchB.Bk ((nodeOf (2 * h) u : ℝ) - k) *
    (if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0))]
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter]
  have : (nodes (2 * h)).filter (fun k => k ∈ LogEnergy.Oset h) = LogEnergy.Oset h := by
    ext x; simp only [mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨Oset_subset h hx, hx⟩⟩
  rw [this, mul_sum, mul_sum]
  refine sum_congr rfl fun _ _ => by ring

/-- `⟨σ₀, B σ₀⟩ = (q²/4) ∑_{k,k' ∈ 𝒪} B(k − k')`. -/
theorem quad_sig0_eq (q h : ℕ) :
    ∑ u, ∑ v, sig0 q h u * sig0 q h v * ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) =
      (q : ℝ) ^ 2 / 4 * ∑ k ∈ LogEnergy.Oset h, ∑ k' ∈ LogEnergy.Oset h,
        ArchB.Bk ((k : ℝ) - k') := by
  unfold sig0
  rw [sum_nodeOf_eq (2 * h) (fun k => ∑ v, (if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
    (if nodeOf (2 * h) v ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
      ArchB.Bk ((k : ℝ) - nodeOf (2 * h) v))]
  have inner : ∀ k : ℤ, ∑ v, (if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
      (if nodeOf (2 * h) v ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
        ArchB.Bk ((k : ℝ) - nodeOf (2 * h) v) =
      ∑ k' ∈ nodes (2 * h), (if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
        (if k' ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) * ArchB.Bk ((k : ℝ) - k') :=
    fun k => sum_nodeOf_eq (2 * h) (fun k' => (if k ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) *
      (if k' ∈ LogEnergy.Oset h then (q : ℝ) / 2 else 0) * ArchB.Bk ((k : ℝ) - k'))
  rw [sum_congr rfl (fun k _ => inner k)]
  rw [← sum_subset (Oset_subset h) (fun k _ hk => by simp [hk]), mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [← sum_subset (Oset_subset h) (fun k' _ hk' => by simp [hk']), mul_sum]
  refine sum_congr rfl fun k' hk' => ?_
  rw [if_pos hk, if_pos hk']; ring

/-- **Linearisation**: `E_B(s) ≤ ∑_u s_u g_u − ⟨σ₀, B σ₀⟩` for every `s` of mass `qn`. -/
theorem EB_le_lin (q h : ℕ) (s : Fin (2 * R (2 * h) + 1) → ℝ) (hs : ∑ u, s u = q * (2 * h)) :
    EB q (2 * h) s ≤
      ∑ u, s u * (Real.log |hR q (2 * h) u| +
        q * ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - k')) -
      ∑ u, ∑ v, sig0 q h u * sig0 q h v *
        ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) := by
  have hlin := quadratic_log_le_linearization (univ : Finset (Fin (2 * R (2 * h) + 1)))
    (fun u => (nodeOf (2 * h) u : ℝ)) s (sig0 q h) (by rw [hs, sum_sig0])
  have hlin' : ∑ u, ∑ v, s u * s v * ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) ≤
      ∑ u, ∑ v, sig0 q h u * sig0 q h v * ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) +
      2 * ∑ u, (s u - sig0 q h u) *
        ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v := hlin
  unfold EB
  have e1 : ∑ u, s u * (Real.log |hR q (2 * h) u| +
        q * ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - k')) =
      ∑ u, s u * Real.log |hR q (2 * h) u| +
        ∑ u, s u * (2 * ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [two_Bsig0]; ring
  have hX : ∀ u, (s u - sig0 q h u) *
        ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v =
      s u * ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v -
        ∑ v, sig0 q h u * sig0 q h v * ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) := by
    intro u
    rw [sub_mul, mul_sum (s := univ) (a := sig0 q h u)]
    congr 1
    refine sum_congr rfl fun v _ => by ring
  have e2 : 2 * ∑ u, (s u - sig0 q h u) *
        ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v =
      ∑ u, s u * (2 * ∑ v, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) * sig0 q h v) -
        2 * ∑ u, ∑ v, sig0 q h u * sig0 q h v *
          ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) := by
    rw [sum_congr rfl (fun u _ => hX u), sum_sub_distrib, mul_sub]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun u _ => by ring
  rw [e1]
  linarith

/-- **The quadratic term**: `⟨σ₀, B σ₀⟩ ≥ q²n² ln n − F n² − 75 q² n (1 + ln n)`, `n = 2h`. -/
theorem quad_sig0_ge (q h : ℕ) (hh : 1 ≤ h) :
    (q : ℝ) ^ 2 * ((2 * h : ℕ) : ℝ) ^ 2 * Real.log (2 * h : ℕ) - Fconst q * ((2 * h : ℕ) : ℝ) ^ 2 -
        75 * (q : ℝ) ^ 2 * ((2 * h : ℕ) : ℝ) * (1 + Real.log (2 * h : ℕ)) ≤
      ∑ u, ∑ v, sig0 q h u * sig0 q h v *
        ArchB.Bk ((nodeOf (2 * h) u : ℝ) - nodeOf (2 * h) v) := by
  rw [quad_sig0_eq]
  have hE := LogEnergy.outer_energy_ge h hh
  have hB : ∑ k ∈ LogEnergy.Oset h, ∑ m ∈ LogEnergy.Oset h, Real.log |((k - m : ℤ) : ℝ)| ≤
      ∑ k ∈ LogEnergy.Oset h, ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((k : ℝ) - k') := by
    refine sum_le_sum fun k _ => sum_le_sum fun k' _ => ?_
    have := LogEnergy.log_le_Bk ((k : ℝ) - k')
    push_cast; exact this
  have hq : (0 : ℝ) ≤ (q : ℝ) ^ 2 / 4 := by positivity
  have := mul_le_mul_of_nonneg_left (hE.trans hB) hq
  unfold Fconst
  nlinarith

/-- **The energy bound for every profile.** -/
theorem EB_le (q h : ℕ) (hh : 1 ≤ h) {s : Fin (2 * R (2 * h) + 1) → ℕ}
    (hs : s ∈ profiles q (2 * h) (q * (2 * h))) :
    EB q (2 * h) (fun u => (s u : ℝ)) ≤
      -((q : ℝ) ^ 2 * ((2 * h : ℕ) : ℝ) ^ 2 * Real.log (2 * h : ℕ)) +
        Fconst q * ((2 * h : ℕ) : ℝ) ^ 2 +
        100 * (q : ℝ) ^ 2 * ((2 * h : ℕ) : ℝ) * (1 + Real.log (2 * h : ℕ)) := by
  simp only [profiles, mem_filter] at hs
  have hsum : ∑ u, (s u : ℝ) = q * (2 * h) := by exact_mod_cast hs.2
  have hlin := EB_le_lin q h (fun u => (s u : ℝ)) hsum
  have hquad := quad_sig0_ge q h hh
  have hg : ∀ u, (s u : ℝ) * (Real.log |hR q (2 * h) u| +
      q * ∑ k' ∈ LogEnergy.Oset h, ArchB.Bk ((nodeOf (2 * h) u : ℝ) - k')) ≤
      (s u : ℝ) * (2 * q * (1 + Real.log (2 * R (2 * h)))) := fun u =>
    mul_le_mul_of_nonneg_left (g_le h q (nodeOf_mem _ u)) (by positivity)
  have hsg := sum_le_sum fun u (_ : u ∈ univ) => hg u
  rw [← sum_mul, hsum] at hsg
  have hn1 : (1 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * h)
  have hL : 0 ≤ Real.log (2 * h : ℕ) := Real.log_natCast_nonneg _
  have hR3 : Real.log (2 * (R (2 * h) : ℝ)) ≤ 2 + Real.log (2 * h : ℕ) := by
    have e : (2 * (R (2 * h) : ℝ)) = 3 * ((2 * h : ℕ) : ℝ) := by
      have : 2 * R (2 * h) = 3 * (2 * h) := R_of_even ⟨h, by ring⟩
      exact_mod_cast this
    rw [e]; exact ArchB.log_three_mul_le (by omega)
  have hq : (0 : ℝ) ≤ q := by positivity
  push_cast at hsg hquad ⊢
  have key : (q : ℝ) * (2 * h) * (2 * q * (1 + Real.log (2 * (R (2 * h) : ℝ)))) ≤
      25 * (q : ℝ) ^ 2 * (2 * h) * (1 + Real.log (2 * h)) := by
    push_cast at hL hR3 hn1
    have : 0 ≤ (q : ℝ) ^ 2 * (2 * h) := by positivity
    nlinarith
  linarith

end TwoAdicWin.Arch
