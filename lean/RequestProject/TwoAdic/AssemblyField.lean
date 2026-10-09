import RequestProject.TwoAdic.AsmLow
import RequestProject.TwoAdic.AsmChain
import RequestProject.TwoAdic.MainR2

/-!
# Field `assembly` of `TwoAdicInputsR2`, discharged (II, Cor. 5.4)

**`assembly_field`** is the field `assembly` of `TwoAdicInputsR2` verbatim (with `circ = circCert`):
under the Mertens hypothesis `M(Y) − ln Y → M₀` and `θ(x)/x → 1`, for every admissible `(q, d)` and
`ε > 0`, for all large even `n` and every finite set `S` of odd primes,

  `∑_{ℓ ∈ S} T⁺_ℓ log₂ ℓ ≤ q² n² log₂ n + q² C̃(δ) n² + ε n²`.

The primes are split into `ℓ ≤ n/20` (`low_sum`: small primes by II Lemma A.5, middle primes by
II Prop. A.7, Mertens' sum up to `n/20`), `n/20 < ℓ ≤ 7n/2` (`large_primes_sum`: the homogeneous
relaxation II Lemma 5.3, exact counting of the class types of the certificate cells, prime Riemann
sums of the Lipschitz integrand, `circCert` = sum of the cell integrals) and `ℓ > 7n/2`
(`TPplus_eq_zero_of_large`).
-/

open Finset Filter Topology Chebyshev

namespace TwoAdicWin

open Asm

theorem delta_le_one {q d : ℕ} (h : Admissible q d) : deltaOf q d ≤ 1 := by
  obtain ⟨hq4, _, _, _, h7⟩ := h
  unfold deltaOf
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h7' : (7 : ℝ) * (d + 2) ≤ 10 * q := by exact_mod_cast h7
  rw [sub_le_iff_le_add, div_le_iff₀ hq]
  linarith

/-- The split of a sum over `S` at `ℓ ≤ n/20` and `ℓ ≤ 7n/2`. -/
theorem sum_split3 (S : Finset ℕ) (F : ℕ → ℝ) (n : ℝ) :
    ∑ ℓ ∈ S, F ℓ = ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ n / 20), F ℓ +
      ∑ ℓ ∈ S.filter (fun ℓ : ℕ => n / 20 < ℓ ∧ (ℓ : ℝ) ≤ 7 / 2 * n), F ℓ +
      ∑ ℓ ∈ S.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ n / 20 ∧ ¬ (ℓ : ℝ) ≤ 7 / 2 * n), F ℓ := by
  rw [← sum_filter_add_sum_filter_not S (fun ℓ : ℕ => (ℓ : ℝ) ≤ n / 20)]
  rw [← sum_filter_add_sum_filter_not (S.filter fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ n / 20)
    (fun ℓ : ℕ => (ℓ : ℝ) ≤ 7 / 2 * n)]
  rw [filter_filter, filter_filter, add_assoc]
  have e : S.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ n / 20 ∧ (ℓ : ℝ) ≤ 7 / 2 * n) =
      S.filter (fun ℓ : ℕ => n / 20 < ℓ ∧ (ℓ : ℝ) ≤ 7 / 2 * n) :=
    filter_congr fun ℓ _ => by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_not_ge h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨not_le.2 h1, h2⟩
  rw [e]

theorem aux_half (E : ℝ) (q n : ℝ) (hq : 0 < q) :
    E / (6 * q ^ 2) * n = 2 * (E / (12 * q ^ 2) * n) := by
  field_simp; ring

theorem aux_cancel (E : ℝ) (q n : ℝ) (hq : 0 < q) :
    q ^ 2 * n * (E / (6 * q ^ 2) * n) = E / 6 * n ^ 2 := by
  field_simp

set_option maxHeartbeats 2000000 in
/-- **Field (iii-b) `assembly` of `TwoAdicInputsR2`, discharged** (II, Cor. 5.4), with
`circ = circCert`. -/
theorem assembly_field : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertensOddSum Y - Real.log Y) atTop (𝓝 M₀) →
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) →
    ∀ q d : ℕ, Admissible q d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
        ∑ ℓ ∈ S, (TPplus q d n ℓ (q * n) : ℝ) * Real.logb 2 ℓ ≤
          (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.logb 2 n
            + (q : ℝ) ^ 2 * Ctil M₀ circCert (deltaOf q d) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2 := by
  intro M₀ hM hθ q d hadm ε hε
  have hq4 : 4 ≤ q := hadm.1
  have hq : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hδ1 := delta_le_one hadm
  set δ := deltaOf q d with hδdef
  have hqδ : (q : ℝ) * (1 + δ) = d + 2 := q_one_add_delta hq
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 < 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith
  have hl4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  set E : ℝ := ε * Real.log 2 with hEdef
  have hE : 0 < E := by positivity
  -- the small parameters
  set K1 : ℝ := 6 * ((q : ℝ) ^ 2 + (d + 2) * q + 1) with hK1
  have hK1p : 0 < K1 := by positivity
  set ε' : ℝ := min 1 (E / K1) with hε'def
  have hε'0 : 0 < ε' := lt_min one_pos (div_pos hE hK1p)
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'2 : ε' ≤ E / K1 := min_le_right _ _
  have hε'3 : (q : ℝ) ^ 2 * ε' ≤ E / 6 ∧ (d + 2) * q * ε' / 20 ≤ E / 6 := by
    have h := mul_le_mul_of_nonneg_left hε'2 hK1p.le
    rw [mul_div_cancel₀ _ hK1p.ne'] at h
    have hK : K1 * ε' = 6 * ((q : ℝ) ^ 2 * ε') + 6 * ((d + 2) * q * ε') + 6 * ε' := by
      rw [hK1]; ring
    have h1 : 0 ≤ (d + 2) * (q : ℝ) * ε' := by positivity
    have h2 : 0 ≤ (q : ℝ) ^ 2 * ε' := by positivity
    constructor <;> linarith
  set η : ℝ := E / (6 * ((q : ℝ) ^ 2 + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hqη : (q : ℝ) ^ 2 * η ≤ E / 6 := by
    have e : ((q : ℝ) ^ 2 + 1) * η = E / 6 := by
      rw [hηdef]; field_simp
    linarith
  -- Mertens
  obtain ⟨Y0, hY0⟩ := eventually_atTop.1 (hM.eventually (gt_mem_nhds (show M₀ < M₀ + ε' by linarith)))
  -- θ
  obtain ⟨y0, hy01, hy0⟩ := Hankel2.theta_approx hθ hε'0
  -- the large primes
  obtain ⟨C, N3, hlarge⟩ := large_primes_sum hθ hq hδ1 hη
  -- the small-prime error
  set K0 : ℝ := (2 * q + d + 1) * q + (q : ℝ) ^ 2 with hK0
  have hK0p : 0 < K0 := by positivity
  obtain ⟨N4, hN4⟩ := Hankel2.log_le_eps_sqrt (show 0 < E / (48 * K0) by positivity)
  obtain ⟨N5, hN5⟩ := Hankel2.log_le_eps_sqrt (show 0 < E / (12 * (q : ℝ) ^ 2) by positivity)
  have hK0n : ∀ x : ℝ, K0 * x = (2 * q + d + 1) * q * x + (q : ℝ) ^ 2 * x := fun x => by
    rw [hK0]; ring
  clear_value E K1 ε' η K0 δ
  set T : ℝ := max (max (max (20 * Y0) (20 * y0)) (max N3 3))
    (max (6 * |C| / E) (12 * (q : ℝ) ^ 2 * (|M₀| + 1) / E)) with hT
  refine ⟨max (max ⌈T⌉₊ N4) N5 + 1, fun n hn hev S hS => ?_⟩
  have hnT : T ≤ n := by
    have : ⌈T⌉₊ ≤ n := by omega
    exact (Nat.le_ceil T).trans (by exact_mod_cast this)
  have hn4 : N4 ≤ n := by omega
  have hn5 : N5 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hT1 : 20 * Y0 ≤ n := le_trans (by simp [hT]) hnT
  have hT2 : 20 * y0 ≤ n := le_trans (by simp [hT]) hnT
  have hT3 : N3 ≤ n := le_trans (by simp [hT]) hnT
  have hT4 : (3 : ℝ) ≤ n := le_trans (by simp [hT]) hnT
  have hT5 : 6 * |C| / E ≤ n := le_trans (by simp [hT]) hnT
  have hT6 : 12 * (q : ℝ) ^ 2 * (|M₀| + 1) / E ≤ n := le_trans (by simp [hT]) hnT
  clear_value T
  -- Mertens at `n/20`
  have hMer : mertensOddSum (n / 20) ≤ Real.log n - Real.log 20 + M₀ + ε' := by
    have h := hY0 (n / 20) (by linarith)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  -- θ at `n/20`
  have hθn : θ (n / 20) ≤ (1 + ε') * (n / 20) := by
    have := (abs_le.1 (hy0 (n / 20) (by linarith))).2
    linarith
  have hθ0 : 0 ≤ θ (n / 20) := theta_nonneg _
  -- the small-prime error
  have hW : Wsm q d n * (2 * Real.log 4 * Real.sqrt n) ≤ E / 6 * (n : ℝ) ^ 2 := by
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hlog := hN4 n hn4
    have hnl : (Nat.log 2 (4 * n) : ℝ) ≤ 2 * Real.log (4 * n) := by
      have := natLog_two_le (4 * n) (by omega)
      push_cast at this
      have hl0 : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
      refine this.trans ?_
      rw [div_le_iff₀ hl2]
      have h9 := Real.log_two_gt_d9
      have : Real.log (4 * n) * (1 / 2) ≤ Real.log (4 * n) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hl0
      linarith
    have hWle : Wsm q d n ≤ K0 * n * (2 * (E / (48 * K0) * Real.sqrt n)) := by
      unfold Wsm
      have h1 : ((2 * q + d + 1) * q * n + (3 * n + 1) * (q : ℝ) ^ 2 / 4) ≤ K0 * n := by
        have hh : (3 * n + 1) * (q : ℝ) ^ 2 / 4 ≤ (q : ℝ) ^ 2 * n := by
          have := mul_le_mul_of_nonneg_left hnR (sq_nonneg (q : ℝ))
          linarith
        have := hK0n n
        linarith
      have h2 : (Nat.log 2 (4 * n) : ℝ) ≤ 2 * (E / (48 * K0) * Real.sqrt n) := by linarith
      have h3 : 0 ≤ ((2 * q + d + 1) * q * n + (3 * n + 1) * (q : ℝ) ^ 2 / 4) := by positivity
      have h4 : (0 : ℝ) ≤ Nat.log 2 (4 * n) := Nat.cast_nonneg _
      calc ((2 * q + d + 1) * q * n + (3 * n + 1) * (q : ℝ) ^ 2 / 4) * (Nat.log 2 (4 * n) : ℝ)
          ≤ (K0 * n) * (2 * (E / (48 * K0) * Real.sqrt n)) :=
            mul_le_mul h1 h2 h4 (by positivity)
        _ = K0 * n * (2 * (E / (48 * K0) * Real.sqrt n)) := by ring
    have : K0 * n * (2 * (E / (48 * K0) * Real.sqrt n)) * (2 * Real.log 4 * Real.sqrt n) ≤
        E / 6 * (n : ℝ) ^ 2 := by
      have e : K0 * n * (2 * (E / (48 * K0) * Real.sqrt n)) * (2 * Real.log 4 * Real.sqrt n) =
          E / 12 * Real.log 4 * (n : ℝ) ^ 2 := by
        field_simp
        rw [show Real.sqrt n ^ 2 = n by rw [sq]; exact hsq]
        ring
      rw [e]
      have h0 : 0 ≤ E * (n : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hl4.le h0
      have e' : E / 12 * Real.log 4 * (n : ℝ) ^ 2 = E * (n : ℝ) ^ 2 * Real.log 4 / 12 := by ring
      rw [e']
      linarith
    have hpos : 0 ≤ 2 * Real.log 4 * Real.sqrt n := by positivity
    have := mul_le_mul_of_nonneg_right hWle hpos
    linarith
  -- the `n`-term of `n (n+1)`
  have hnX : (q : ℝ) ^ 2 * n * (Real.log n - Real.log 20 + M₀ + ε') ≤ E / 6 * (n : ℝ) ^ 2 := by
    have hlog := hN5 n hn5
    have hln : Real.log n ≤ E / (12 * (q : ℝ) ^ 2) * n := by
      have h1 : Real.log n ≤ Real.log (4 * n) := Real.log_le_log hn0 (by linarith)
      have h2 : Real.sqrt n ≤ n := by
        rw [Real.sqrt_le_left (by linarith), sq]
        linarith [mul_le_mul_of_nonneg_left hnR hn0.le]
      have h3 : 0 ≤ E / (12 * (q : ℝ) ^ 2) := by positivity
      linarith [mul_le_mul_of_nonneg_left h2 h3]
    have hM1 : |M₀| + 1 ≤ E / (12 * (q : ℝ) ^ 2) * n := by
      rw [div_le_iff₀ hE] at hT6
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hX : Real.log n - Real.log 20 + M₀ + ε' ≤ E / (6 * (q : ℝ) ^ 2) * n := by
      have := le_abs_self M₀
      rw [aux_half E q n hqR]; linarith
    have hq2n : 0 ≤ (q : ℝ) ^ 2 * n := by positivity
    have := mul_le_mul_of_nonneg_left hX hq2n
    rw [aux_cancel E q n hqR] at this
    exact this
  -- the constant `C`
  have hCn : C * n ≤ E / 6 * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hE] at hT5
    have : C * n ≤ |C| * n := mul_le_mul_of_nonneg_right (le_abs_self C) hn0.le
    have h' := mul_le_mul_of_nonneg_right hT5 hn0.le
    have e : E / 6 * (n : ℝ) ^ 2 = n * E * n / 6 := by ring
    rw [e]
    linarith
  have h1 : (q : ℝ) ^ 2 * n * (n + 1) * mertensOddSum (n / 20) ≤
      (q : ℝ) ^ 2 * n * (n + 1) * (Real.log n - Real.log 20 + M₀ + ε') :=
    mul_le_mul_of_nonneg_left hMer (by positivity)
  have h2 : (d + 2) * q * n * θ (n / 20) ≤ (d + 2) * q * n * ((1 + ε') * (n / 20)) :=
    mul_le_mul_of_nonneg_left hθn (by positivity)
  have h3 : (q : ℝ) ^ 2 / 4 * (n / 20) * θ (n / 20) ≤
      (q : ℝ) ^ 2 / 4 * (n / 20) * ((1 + ε') * (n / 20)) :=
    mul_le_mul_of_nonneg_left hθn (by positivity)
  have e2 : (d + 2) * q * n * ((1 + ε') * (n / 20)) =
      (q : ℝ) ^ 2 * ((1 + δ) * epsC) * (n : ℝ) ^ 2 + (d + 2) * q * ε' / 20 * (n : ℝ) ^ 2 := by
    unfold epsC
    have : (d + 2 : ℝ) * q = (q : ℝ) ^ 2 * (1 + δ) := by rw [← hqδ]; ring
    rw [show (d + 2 : ℝ) * q * n * ((1 + ε') * (n / 20)) = (d + 2) * q * (n ^ 2 / 20) +
      (d + 2) * q * ε' / 20 * n ^ 2 by ring, this]
    ring
  have e3 : (q : ℝ) ^ 2 / 4 * (n / 20) * ((1 + ε') * (n / 20)) ≤
      (q : ℝ) ^ 2 * (epsC ^ 2 / 2) * (n : ℝ) ^ 2 := by
    unfold epsC
    have h0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (show 1 + ε' ≤ 2 by linarith) h0
    have e : (q : ℝ) ^ 2 / 4 * (n / 20) * ((1 + ε') * (n / 20)) =
        (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * (1 + ε') / 1600 := by ring
    rw [e]
    have e' : (q : ℝ) ^ 2 * ((1 / 20) ^ 2 / 2) * (n : ℝ) ^ 2 = (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * 2 / 1600 := by
      ring
    rw [e']
    linarith
  have e1 : (q : ℝ) ^ 2 * n * (n + 1) * (Real.log n - Real.log 20 + M₀ + ε') =
      (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n + (q : ℝ) ^ 2 * (M₀ - Real.log 20) * (n : ℝ) ^ 2 +
        (q : ℝ) ^ 2 * ε' * (n : ℝ) ^ 2 +
        (q : ℝ) ^ 2 * n * (Real.log n - Real.log 20 + M₀ + ε') := by ring
  have hη2 : (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * (circCert δ + η) =
      (q : ℝ) ^ 2 * circCert δ * (n : ℝ) ^ 2 + (q : ℝ) ^ 2 * η * (n : ℝ) ^ 2 := by ring
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have f1 := mul_le_mul_of_nonneg_right hε'3.1 hn2
  have f2 := mul_le_mul_of_nonneg_right hε'3.2 hn2
  have f3 := mul_le_mul_of_nonneg_right hqη hn2
  -- the three ranges
  set F : ℕ → ℝ := fun ℓ => (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ
  have hsplit := sum_split3 S F n
  have hhuge : ∑ ℓ ∈ S.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ n / 20 ∧ ¬ (ℓ : ℝ) ≤ 7 / 2 * n), F ℓ = 0 := by
    refine sum_eq_zero fun ℓ hℓ => ?_
    simp only [mem_filter, not_le] at hℓ
    obtain ⟨hp, h2⟩ := hS ℓ hℓ.1
    haveI : Fact ℓ.Prime := ⟨hp⟩
    have : 3 * n + 1 < ℓ := by
      have : (3 * n + 1 : ℝ) < ℓ := by linarith [hℓ.2.2]
      exact_mod_cast this
    simp only [F, TPplus_eq_zero_of_large hev hn1 h2 hq this, Int.cast_zero, zero_mul]
  have hlow := low_sum (q := q) (d := d) hev hn1 S hS
  have hlg := hlarge n hT3 hev S hS
  rw [← hδdef] at hlg
  -- combine (natural logarithms)
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hmain : ∑ ℓ ∈ S, F ℓ ≤ (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n +
      (q : ℝ) ^ 2 * (M₀ - Real.log 20 + circCert δ + (1 + δ) * epsC + epsC ^ 2 / 2) * (n : ℝ) ^ 2 +
        E * (n : ℝ) ^ 2 := by
    rw [hsplit, hhuge, add_zero]
    simp only [F] at hlow hlg ⊢
    linarith only [hlow, hlg, h1, h2, h3, e1, e2, e3, hη2, f1, f2, f3, hW, hnX, hCn]
  -- base 2
  have hlogb : ∀ x : ℝ, Real.logb 2 x = Real.log x / Real.log 2 := fun x => rfl
  simp only [hlogb]
  have eL : ∑ ℓ ∈ S, (TPplus q d n ℓ (q * n) : ℝ) * (Real.log ℓ / Real.log 2) =
      (∑ ℓ ∈ S, F ℓ) / Real.log 2 := by
    rw [sum_div]; exact sum_congr rfl fun ℓ _ => by simp only [F]; ring
  rw [eL, div_le_iff₀ hl2]
  have eR : ((q : ℝ) ^ 2 * (n : ℝ) ^ 2 * (Real.log n / Real.log 2) +
      (q : ℝ) ^ 2 * Ctil M₀ circCert δ * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2) * Real.log 2 =
      (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * Real.log n +
        (q : ℝ) ^ 2 * (M₀ - Real.log 20 + circCert δ + (1 + δ) * epsC + epsC ^ 2 / 2) * (n : ℝ) ^ 2 +
          E * (n : ℝ) ^ 2 := by
    unfold Ctil
    rw [hEdef]
    field_simp
  rw [eR]
  exact hmain

end TwoAdicWin
