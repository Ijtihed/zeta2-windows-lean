import RequestProject.Zeta7.Hankel2.PrimeSums

/-!
# Prime Riemann sums

Under `θ(x)/x → 1`: for `0 < a ≤ b` and a function `g ≥ 0` that is `L`-Lipschitz on `[a, b]`,

  `∑_{p prime, a n < p ≤ b n} ln p · g(p/n) ≤ n (∫_a^b g + η)`  for all large `n`

(`riemann_upper`), by cutting `[a, b]` into `m` equal pieces.
-/

open Filter Topology Finset Chebyshev MeasureTheory

namespace TwoAdicWin.Asm

/-- Every point of `(a, a + m h]` lies in one of the pieces `(a + i h, a + (i+1) h]`. -/
theorem exists_piece {a h t : ℝ} {m : ℕ} (hh : 0 < h) (ht1 : a < t) (ht2 : t ≤ a + m * h) :
    ∃ i ∈ range m, a + i * h < t ∧ t ≤ a + (i + 1) * h := by
  set s := (t - a) / h
  have hs0 : 0 < s := div_pos (by linarith) hh
  have hsm : s ≤ m := by rw [div_le_iff₀ hh]; linarith
  refine ⟨⌈s⌉₊ - 1, ?_, ?_, ?_⟩
  · rw [mem_range]
    have : ⌈s⌉₊ ≤ m := Nat.ceil_le.2 hsm
    have : 0 < ⌈s⌉₊ := Nat.ceil_pos.2 hs0
    omega
  · have h1 : 0 < ⌈s⌉₊ := Nat.ceil_pos.2 hs0
    have h2 : ((⌈s⌉₊ - 1 : ℕ) : ℝ) < s := by
      rw [Nat.cast_sub h1, Nat.cast_one]
      linarith [Nat.ceil_lt_add_one hs0.le]
    have : ((⌈s⌉₊ - 1 : ℕ) : ℝ) * h < t - a := by
      have := mul_lt_mul_of_pos_right h2 hh
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    linarith
  · have h1 : 0 < ⌈s⌉₊ := Nat.ceil_pos.2 hs0
    have h2 : s ≤ ((⌈s⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]; linarith [Nat.le_ceil s]
    have : t - a ≤ (((⌈s⌉₊ - 1 : ℕ) : ℝ) + 1) * h := by
      have := mul_le_mul_of_nonneg_right h2 hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    linarith

theorem aux_eta_bound {η b m C : ℝ} (hb : 0 < b) (hm : 0 < m) (hC : 0 ≤ C) (hη : 0 < η) :
    η / (4 * b * m * (C + 1)) * (2 * b) * (m * C) ≤ η / 2 := by
  have hD : 0 < 4 * b * m * (C + 1) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hD]
  have : 0 ≤ η * b * m := by positivity
  nlinarith

section Riemann

variable (hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
include hθ

/-- **Prime Riemann sums of Lipschitz functions.** -/
theorem riemann_upper {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b) {g : ℝ → ℝ} (hL : 0 ≤ L)
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hg : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ L * |x - y|)
    (hint : IntervalIntegrable g volume a b) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ n : ℝ, N₀ ≤ n → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ a * n < p ∧ (p : ℝ) ≤ b * n) →
        ∑ p ∈ P, Real.log p * g (p / n) ≤ n * ((∫ x in a..b, g x) + η) := by
  -- the number of pieces
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * L * (b - a) ^ 2 / η)
  have hm0 : 0 < m := by
    have : (0 : ℝ) ≤ 4 * L * (b - a) ^ 2 / η := by
      have : 0 ≤ b - a := by linarith
      positivity
    exact_mod_cast this.trans_lt hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  by_cases hab' : a = b
  · -- degenerate interval: no primes
    subst hab'
    refine ⟨1, one_pos, fun n hn P hP => ?_⟩
    have : P = ∅ := by
      ext p; simp only [notMem_empty, iff_false]; intro hp
      have := hP p hp; linarith [this.2.1, this.2.2]
    rw [this, sum_empty, intervalIntegral.integral_same, zero_add]
    exact mul_nonneg (by linarith) hη.le
  have hab2 : a < b := lt_of_le_of_ne hab hab'
  set h : ℝ := (b - a) / m with hhdef
  have hh : 0 < h := div_pos (by linarith) hmR
  have hmh : (m : ℝ) * h = b - a := by rw [hhdef]; field_simp
  set x : ℕ → ℝ := fun i => a + i * h
  have hxmem : ∀ i ≤ m, x i ∈ Set.Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
    refine ⟨by simp only [x]; nlinarith, ?_⟩
    simp only [x]
    nlinarith
  -- the piece values `c_i = g(x_{i+1}) + L h`
  set c : ℕ → ℝ := fun i => g (x (i + 1)) + L * h
  have hc0 : ∀ i ∈ range m, 0 ≤ c i := fun i hi =>
    add_nonneg (hg0 _ (hxmem _ (by rw [mem_range] at hi; omega))) (mul_nonneg hL hh.le)
  -- the integral on each piece
  have hpiece_int : ∀ i ∈ range m, h * c i - 2 * L * h ^ 2 ≤ ∫ t in x i..x (i + 1), g t := by
    intro i hi
    rw [mem_range] at hi
    have hxi := hxmem i hi.le
    have hxi1 := hxmem (i + 1) hi
    have hle : x i ≤ x (i + 1) := by simp only [x]; push_cast; linarith
    have hint' : IntervalIntegrable g volume (x i) (x (i + 1)) :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc hxi.1 hxi1.2)
    have hlow : ∀ t ∈ Set.Icc (x i) (x (i + 1)), g (x (i + 1)) - L * h ≤ g t := by
      intro t ht
      have htm : t ∈ Set.Icc a b := ⟨hxi.1.trans ht.1, ht.2.trans hxi1.2⟩
      have := hg _ hxi1 _ htm
      have hd : |x (i + 1) - t| ≤ h := by
        rw [abs_le]; simp only [x] at ht ⊢; push_cast at ht ⊢; constructor <;> linarith [ht.1, ht.2]
      have := (abs_le.1 this).2
      have := mul_le_mul_of_nonneg_left hd hL
      linarith
    have := intervalIntegral.integral_mono_on hle intervalIntegrable_const hint' hlow
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : x (i + 1) - x i = h := by simp only [x]; push_cast; ring
    rw [e] at this
    simp only [c]
    nlinarith
  have hsum_int : ∑ i ∈ range m, (h * c i - 2 * L * h ^ 2) ≤ ∫ t in a..b, g t := by
    refine (sum_le_sum hpiece_int).trans (le_of_eq ?_)
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume) (a := x) (n := m)
      (fun i hi => hint.mono_set (by
        have hle : x i ≤ x (i + 1) := by simp only [x]; push_cast; linarith
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc (hxmem i hi.le).1 (hxmem (i + 1) hi).2))
    rw [this]
    simp only [x, Nat.cast_zero, zero_mul, add_zero]
    rw [hmh]; ring_nf
  -- bound on the `c_i`
  set Cmax : ℝ := g a + L * (b - a) + L * h
  have hcmax : ∀ i ∈ range m, c i ≤ Cmax := by
    intro i hi
    rw [mem_range] at hi
    have := hg _ (hxmem (i + 1) hi) a ⟨le_rfl, hab⟩
    have hd : |x (i + 1) - a| ≤ b - a := by
      have := hxmem (i + 1) hi
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have := (abs_le.1 this).2
    simp only [c, Cmax]
    nlinarith [mul_le_mul_of_nonneg_left hd hL]
  have hCmax0 : 0 ≤ Cmax := by
    have := hg0 a ⟨le_rfl, hab⟩
    have : 0 ≤ b - a := by linarith
    simp only [Cmax]; positivity
  -- θ approximation
  set η' : ℝ := η / (4 * b * m * (Cmax + 1))
  have hη' : 0 < η' := by
    simp only [η']; have : 0 < b := by linarith
    positivity
  obtain ⟨y0, hy0, hθa⟩ := Hankel2.theta_approx hθ hη'
  refine ⟨y0 / a + 1, by positivity, fun n hn P hP => ?_⟩
  have hn0 : 0 < n := by
    have : 0 < y0 / a := by positivity
    linarith
  -- split `P` into the pieces
  set Pi : ℕ → Finset ℕ := fun i => P.filter fun p => x i * n < p ∧ (p : ℝ) ≤ x (i + 1) * n
  have hsplit : ∑ p ∈ P, Real.log p * g (p / n) ≤
      ∑ i ∈ range m, ∑ p ∈ Pi i, Real.log p * g (p / n) := by
    have : ∀ p ∈ P, Real.log p * g (p / n) ≤
        ∑ i ∈ range m, if p ∈ Pi i then Real.log p * g (p / n) else 0 := by
      intro p hp
      obtain ⟨hpp, h1, h2⟩ := hP p hp
      have ht1 : a < p / n := by rw [lt_div_iff₀ hn0]; linarith
      have ht2 : p / n ≤ a + m * h := by rw [hmh, div_le_iff₀ hn0]; linarith
      obtain ⟨i, hi, hi1, hi2⟩ := exists_piece hh ht1 ht2
      have hmem : p / n ∈ Set.Icc a b := ⟨ht1.le, by linarith [hmh]⟩
      have hnn : 0 ≤ Real.log p * g (p / n) :=
        mul_nonneg (Real.log_natCast_nonneg p) (hg0 _ hmem)
      refine le_trans ?_ (single_le_sum (f := fun i => if p ∈ Pi i then Real.log p * g (p / n) else 0)
        (fun j _ => by dsimp only; split_ifs; exacts [hnn, le_rfl]) hi)
      simp only [Pi, mem_filter]
      rw [if_pos ⟨hp, by
        refine ⟨?_, ?_⟩
        · simp only [x]; rw [← lt_div_iff₀ hn0]; linarith
        · simp only [x]; rw [← div_le_iff₀ hn0]; push_cast; linarith⟩]
    refine (sum_le_sum this).trans (le_of_eq ?_)
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_filter]
    congr 1
    ext p
    simp only [Pi, mem_filter]
    tauto
  -- each piece
  have hpiece : ∀ i ∈ range m, ∑ p ∈ Pi i, Real.log p * g (p / n) ≤
      c i * (h * n + η' * (2 * b * n)) := by
    intro i hi
    rw [mem_range] at hi
    have hxi := hxmem i hi.le
    have hxi1 := hxmem (i + 1) hi
    have hle : x i * n ≤ x (i + 1) * n :=
      mul_le_mul_of_nonneg_right (by simp only [x]; push_cast; linarith) hn0.le
    calc ∑ p ∈ Pi i, Real.log p * g (p / n) ≤ ∑ p ∈ Pi i, Real.log p * c i := by
          refine sum_le_sum fun p hp => ?_
          simp only [Pi, mem_filter] at hp
          obtain ⟨hpP, hp1, hp2⟩ := hp
          refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
          have hpn1 : x i < p / n := by rw [lt_div_iff₀ hn0]; exact hp1
          have hpn2 : p / n ≤ x (i + 1) := by rw [div_le_iff₀ hn0]; exact hp2
          have hmem : (p : ℝ) / n ∈ Set.Icc a b := ⟨hxi.1.trans hpn1.le, hpn2.trans hxi1.2⟩
          have := hg _ hmem _ hxi1
          have hd : |(p : ℝ) / n - x (i + 1)| ≤ h := by
            rw [abs_le]; simp only [x] at hpn1 hpn2 ⊢; push_cast at hpn1 hpn2 ⊢
            constructor <;> linarith
          have := (abs_le.1 this).2
          simp only [c]
          nlinarith [mul_le_mul_of_nonneg_left hd hL]
      _ = c i * ∑ p ∈ Pi i, Real.log p := by rw [mul_sum]; exact sum_congr rfl fun p _ => mul_comm _ _
      _ ≤ c i * (θ (x (i + 1) * n) - θ (x i * n)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hc0 i (mem_range.2 hi))
          refine Hankel2.sum_log_le_theta_sub _ hle fun p hp => ?_
          simp only [Pi, mem_filter] at hp
          exact ⟨(hP p hp.1).1, hp.2.1, hp.2.2⟩
      _ ≤ c i * (h * n + η' * (2 * b * n)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hc0 i (mem_range.2 hi))
          have hy1 : y0 ≤ x i * n := by
            have : y0 ≤ a * n := by
              have : y0 / a ≤ n := by linarith
              rwa [div_le_iff₀ ha, mul_comm] at this
            exact this.trans (mul_le_mul_of_nonneg_right hxi.1 hn0.le)
          have hy2 : y0 ≤ x (i + 1) * n := hy1.trans hle
          have e1 := (abs_le.1 (hθa _ hy2)).2
          have e2 := (abs_le.1 (hθa _ hy1)).1
          have e3 : x (i + 1) * n - x i * n = h * n := by simp only [x]; push_cast; ring
          have hb1 : x (i + 1) * n ≤ b * n := mul_le_mul_of_nonneg_right hxi1.2 hn0.le
          have hb2 : x i * n ≤ b * n := mul_le_mul_of_nonneg_right hxi.2 hn0.le
          have hxi0 : 0 ≤ x i * n := mul_nonneg (by linarith [hxi.1]) hn0.le
          nlinarith [mul_le_mul_of_nonneg_left hb1 hη'.le, mul_le_mul_of_nonneg_left hb2 hη'.le]
  refine hsplit.trans ((sum_le_sum hpiece).trans ?_)
  rw [show ∑ i ∈ range m, c i * (h * n + η' * (2 * b * n)) =
      n * ∑ i ∈ range m, h * c i + (η' * (2 * b * n)) * ∑ i ∈ range m, c i by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring]
  have h1 : ∑ i ∈ range m, h * c i ≤ (∫ t in a..b, g t) + 2 * L * h ^ 2 * m := by
    have := hsum_int
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at this
    linarith
  have h2 : ∑ i ∈ range m, c i ≤ m * Cmax := by
    have := sum_le_sum hcmax
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have h3 : 2 * L * h ^ 2 * m ≤ η / 2 := by
    have e : 2 * L * h ^ 2 * m = 2 * L * (b - a) ^ 2 / m := by rw [hhdef]; field_simp
    rw [e, div_le_iff₀ hmR]
    have := hm
    rw [div_lt_iff₀ hη] at this
    nlinarith
  have h4 : η' * (2 * b) * (m * Cmax) ≤ η / 2 := by
    exact aux_eta_bound (by linarith) hmR hCmax0 hη
  have hsc : 0 ≤ ∑ i ∈ range m, c i := sum_nonneg hc0
  calc n * ∑ i ∈ range m, h * c i + η' * (2 * b * n) * ∑ i ∈ range m, c i
      ≤ n * ((∫ t in a..b, g t) + 2 * L * h ^ 2 * m) + η' * (2 * b * n) * (m * Cmax) := by
        have e1 := mul_le_mul_of_nonneg_left h1 hn0.le
        have hb0 : 0 ≤ η' * (2 * b * n) := by
          have : 0 < b := by linarith
          positivity
        have e2 := mul_le_mul_of_nonneg_left h2 hb0
        linarith
    _ = n * ((∫ t in a..b, g t) + 2 * L * h ^ 2 * m + η' * (2 * b) * (m * Cmax)) := by ring
    _ ≤ n * ((∫ t in a..b, g t) + η) :=
        mul_le_mul_of_nonneg_left (by linarith) hn0.le

end Riemann

end TwoAdicWin.Asm
