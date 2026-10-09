import RequestProject.TwoAdic.AsmLevels
import RequestProject.TwoAdic.AsmMiddle

/-!
# Small primes

For every odd prime `ℓ`, `n` even, `K = qn` (**`small_bound`**):

  `T⁺_ℓ ≤ q² n (n+1)/(ℓ − 1) + (2q + d + 1) q n L_ℓ + λ_ℓ (3n + 1) q²/4`,

with `L_ℓ = ⌊log_ℓ(4n − 1)⌋` and `λ_ℓ = ⌊log_ℓ(3n + 1)⌋`.  Proof: the leaf bound, the
level decomposition `sum_D_sub_penalty`, and per level `M = ℓ^j`: `E_c ≤ S_c q (N_c − z_c) − S_c²`,
weak duality over the `M` classes (mean `q(2n+1)/M`, spread `2q`) when `M ≤ 3n + 1`, and `E_c ≤ 0`
when `M > 3n + 1` (every class has at most one node).
-/

open Finset

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin

variable {q d n ℓ : ℕ}

theorem Ecl_le (M c : ℕ) (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ q) :
    Ecl q n M c s ≤ ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) * q * (((cls n M c).card : ℤ) - zc n M c) -
      ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) ^ 2 := by
  unfold Ecl
  have h1 : ∑ i ∈ cls n M c, s i ^ 2 ≤ ∑ i ∈ cls n M c, q * s i :=
    sum_le_sum fun i _ => by rw [sq]; exact Nat.mul_le_mul_right _ (hs i)
  have h1' : ((∑ i ∈ cls n M c, s i ^ 2 : ℕ) : ℤ) ≤ q * ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) := by
    rw [← mul_sum] at h1; exact_mod_cast h1
  have h2 : ∑ i ∈ cls n M c, (s i : ℤ) * q * (((cls n M c).card : ℤ) - 1 - zc n M c) =
      ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) * q * (((cls n M c).card : ℤ) - 1 - zc n M c) := by
    push_cast; rw [sum_mul, sum_mul]
  rw [h2]
  nlinarith

theorem Ecl_nonpos (hn : Even n) {M : ℕ} (hM : 3 * n + 1 < M) (c : ℕ) (hc : c < M)
    (s : Fin (2 * R n + 1) → ℕ) : Ecl q n M c s ≤ 0 := by
  have hN := (card_cls_bounds n M c (by omega) hc).2
  have hR := R_of_even hn
  have hdiv : (2 * R n + 1) / M = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv] at hN
  unfold Ecl
  have h1 : ∀ i ∈ cls n M c, (s i : ℤ) * q * (((cls n M c).card : ℤ) - 1 - zc n M c) ≤ 0 := by
    intro i _
    have : ((cls n M c).card : ℤ) - 1 - zc n M c ≤ 0 := by
      have : ((cls n M c).card : ℤ) ≤ 1 := by exact_mod_cast hN
      have : (0 : ℤ) ≤ zc n M c := Nat.cast_nonneg _
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have h2 := sum_nonpos h1
  have h3 : ((∑ i ∈ cls n M c, s i ^ 2 : ℕ) : ℤ) ≤ ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast sq_sum_ge_sum_sq _ s
  linarith

/-- **One level by weak duality.** -/
theorem level_dual (hn : Even n) {M : ℕ} (hM : Odd M) {s : Fin (2 * R n + 1) → ℕ}
    (hs : s ∈ profiles q n (q * n)) :
    ((∑ c ∈ range M, Ecl q n M c s : ℤ) : ℝ) ≤
      (q : ℝ) ^ 2 * n * (n + 1) / M + M * (q : ℝ) ^ 2 / 4 := by
  have hM0 : 0 < M := hM.pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hsq := profile_le hs
  set S : ℕ → ℝ := fun c => ((∑ i ∈ cls n M c, s i : ℕ) : ℝ) with hSdef
  set β : ℕ → ℝ := fun c => q * (((cls n M c).card : ℝ) - zc n M c) with hβdef
  have step1 : ((∑ c ∈ range M, Ecl q n M c s : ℤ) : ℝ) ≤ ∑ c ∈ range M, (S c * β c - S c ^ 2) := by
    push_cast
    refine sum_le_sum fun c _ => ?_
    have h := Ecl_le M c s hsq
    have h' : ((Ecl q n M c s : ℤ) : ℝ) ≤ ((((∑ i ∈ cls n M c, s i : ℕ) : ℤ) * q *
        (((cls n M c).card : ℤ) - zc n M c) - ((∑ i ∈ cls n M c, s i : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simp only [hSdef, hβdef]
    push_cast
    linarith
  have hC : 0 < (range M).card := by rw [card_range]; exact hM0
  have hSsum : ∑ c ∈ range M, S c = ((q * n : ℕ) : ℝ) := sum_S_cls hM0 hs
  have step2 := weak_duality (range M) S β ((q * n : ℕ) : ℝ) hC hSsum
  rw [card_range] at step2
  have hN : ∑ c ∈ range M, ((cls n M c).card : ℝ) = 3 * n + 1 := by
    have := sum_card_cls n M hM0
    have h3 := R_of_even hn
    have : ((∑ c ∈ range M, (cls n M c).card : ℕ) : ℝ) = ((2 * R n + 1 : ℕ) : ℝ) := by rw [this]
    push_cast at this
    rw [this]
    have : ((2 * R n : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [h3]
    push_cast at this
    linarith
  have hZ : ∑ c ∈ range M, (zc n M c : ℝ) = n := by
    have := sum_zc n M hM
    exact_mod_cast this
  have hβsum : ∑ c ∈ range M, β c = q * (2 * n + 1) := by
    simp only [hβdef]
    rw [← mul_sum, sum_sub_distrib, hN, hZ]
    ring
  set m : ℝ := q * (((3 * n + 1) / M : ℕ) : ℝ) - q * (((n / M : ℕ) : ℝ) + 1) with hmdef
  have hβb : ∀ c ∈ range M, m ≤ β c ∧ β c ≤ m + 2 * q := by
    intro c hc
    have hc' := mem_range.1 hc
    obtain ⟨n1, n2⟩ := card_cls_bounds n M c hM0 hc'
    obtain ⟨z1, z2⟩ := zc_bounds n M c hM
    have e : 2 * R n + 1 = 3 * n + 1 := by have := R_of_even hn; omega
    have n1a : (3 * n + 1) / M ≤ (cls n M c).card := by rw [← e]; exact n1
    have n2a : (cls n M c).card ≤ (3 * n + 1) / M + 1 := by rw [← e]; exact n2
    have n1' : (((3 * n + 1) / M : ℕ) : ℝ) ≤ (cls n M c).card := by exact_mod_cast n1a
    have n2' : ((cls n M c).card : ℝ) ≤ (((3 * n + 1) / M : ℕ) : ℝ) + 1 := by exact_mod_cast n2a
    have z1' : ((n / M : ℕ) : ℝ) ≤ zc n M c := by exact_mod_cast z1
    have z2' : (zc n M c : ℝ) ≤ ((n / M : ℕ) : ℝ) + 1 := by exact_mod_cast z2
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    simp only [hmdef, hβdef]
    constructor
    · nlinarith
    · nlinarith
  have step3 := popoviciu (range M) β m (2 * q) hC hβb
  rw [card_range] at step3
  refine step1.trans (step2.trans ?_)
  rw [hβsum]
  have e1 : ((q * n : ℕ) : ℝ) * ((q * (2 * n + 1)) / M) - ((q * n : ℕ) : ℝ) ^ 2 / M =
      (q : ℝ) ^ 2 * n * (n + 1) / M := by
    push_cast; field_simp; ring
  have e2 : ∑ c ∈ range M, (β c - (q * (2 * n + 1)) / M) ^ 2 / 4 =
      (∑ c ∈ range M, (β c - (∑ c ∈ range M, β c) / M) ^ 2) / 4 := by
    rw [hβsum, sum_div]
  rw [e1, e2]
  have : (M : ℝ) * (2 * q) ^ 2 / 4 / 4 = M * (q : ℝ) ^ 2 / 4 := by ring
  linarith [div_le_div_of_nonneg_right step3 (by norm_num : (0 : ℝ) ≤ 4)]

theorem fP_le_leaf (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) [hp : Fact ℓ.Prime] {k : ℤ}
    (hk : k ∈ nodes n) (s : ℕ) :
    fP q d n ℓ k s ≤ ((s * Dk q n ℓ k + ((2 * q + d + 1) * s : ℕ) * (Lell n ℓ : ℤ) : ℤ) : WithBot ℤ) := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; unfold fP; simp
  · exact leaf_bound hn hn1 h2 hk h0

theorem card_levels_le (hℓ : 1 < ℓ) (X J : ℕ) (hX : X ≠ 0) :
    ((Icc 1 J).filter fun j => ℓ ^ j ≤ X).card ≤ Nat.log ℓ X := by
  have : (Icc 1 J).filter (fun j => ℓ ^ j ≤ X) ⊆ Icc 1 (Nat.log ℓ X) := by
    intro j hj
    simp only [mem_filter, mem_Icc] at hj ⊢
    exact ⟨hj.1.1, (Nat.le_log_iff_pow_le hℓ hX).2 hj.2⟩
  exact (card_le_card this).trans (by simp)

theorem geom_levels (hℓ : 1 < ℓ) (J : ℕ) :
    ∑ j ∈ Icc 1 J, (1 / (ℓ : ℝ)) ^ j ≤ 1 / ((ℓ : ℝ) - 1) := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h0 : (0 : ℝ) ≤ 1 / ℓ := by positivity
  have h1 : 1 / (ℓ : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hℓR
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := J + 1) h0 h1
  have e : Icc 1 J = Ico 1 (J + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
  rw [e]
  refine this.trans (le_of_eq ?_)
  rw [pow_one]
  have : (ℓ : ℝ) - 1 ≠ 0 := by linarith
  have : (ℓ : ℝ) ≠ 0 := by linarith
  field_simp

/-- **Small primes, `A = q`**, for every odd prime. -/
theorem small_bound [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2) :
    (TPplus q d n ℓ (q * n) : ℝ) ≤
      (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) + (2 * q + d + 1) * q * n * Lell n ℓ +
        Nat.log ℓ (3 * n + 1) * (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by
  have hℓ1 : 1 < ℓ := hp.out.one_lt
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hℓodd : Odd ℓ := hp.out.odd_of_ne_two h2
  have hB : 0 ≤ (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) + (2 * q + d + 1) * q * n * Lell n ℓ +
      Nat.log ℓ (3 * n + 1) * (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by
    have : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    positivity
  refine TPplus_le_of hB fun s hs => ?_
  set L := Lell n ℓ
  refine ⟨∑ i, ((s i : ℤ) * Dk q n ℓ (nodeOf n i) + ((2 * q + d + 1) * s i : ℕ) * (L : ℤ)) -
    penalty n ℓ s, ?_, ?_⟩
  · have h1 : ∑ i, fP q d n ℓ (nodeOf n i) (s i) ≤
        ((∑ i, ((s i : ℤ) * Dk q n ℓ (nodeOf n i) + ((2 * q + d + 1) * s i : ℕ) * (L : ℤ)) : ℤ) :
          WithBot ℤ) := by
      rw [WithBot.coe_sum]
      exact sum_le_sum fun i _ => fP_le_leaf hn hn1 h2 (nodeOf_mem_nodes' n i) (s i)
    calc (∑ i, fP q d n ℓ (nodeOf n i) (s i)) + (((-penalty n ℓ s : ℤ)) : WithBot ℤ)
        ≤ ((∑ i, ((s i : ℤ) * Dk q n ℓ (nodeOf n i) + ((2 * q + d + 1) * s i : ℕ) * (L : ℤ)) : ℤ) :
          WithBot ℤ) + (((-penalty n ℓ s : ℤ)) : WithBot ℤ) := add_le_add h1 le_rfl
      _ = _ := by rw [← WithBot.coe_add]; congr 1
  · -- the value
    have hsum := profile_sum hs
    have e1 : ∑ i, ((s i : ℤ) * Dk q n ℓ (nodeOf n i) + ((2 * q + d + 1) * s i : ℕ) * (L : ℤ)) -
        penalty n ℓ s = (∑ i, (s i : ℤ) * Dk q n ℓ (nodeOf n i) - penalty n ℓ s) +
          (2 * q + d + 1) * (q * n) * L := by
      rw [sum_add_distrib]
      have : ∑ i, (((2 * q + d + 1) * s i : ℕ) : ℤ) * (L : ℤ) = (2 * q + d + 1) * (q * n) * L := by
        rw [← sum_mul]; push_cast; rw [← mul_sum]
        have : (∑ i, (s i : ℤ)) = ((q * n : ℕ) : ℤ) := by rw [← hsum]; push_cast; rfl
        rw [this]; push_cast; ring
      rw [this]; ring
    rw [e1, sum_D_sub_penalty hn hn1 h2 s]
    push_cast
    -- the levels
    have hlev : ∀ j ∈ Icc 1 (2 * R n + 1), ((∑ c ∈ range (ℓ ^ j), Ecl q n (ℓ ^ j) c s : ℤ) : ℝ) ≤
        (q : ℝ) ^ 2 * n * (n + 1) * (1 / (ℓ : ℝ)) ^ j +
          (if ℓ ^ j ≤ 3 * n + 1 then (3 * n + 1) * (q : ℝ) ^ 2 / 4 else 0) := by
      intro j _
      have hM : Odd (ℓ ^ j) := hℓodd.pow
      split_ifs with hj
      · have := level_dual hn hM hs
        have hMle : ((ℓ ^ j : ℕ) : ℝ) ≤ 3 * n + 1 := by exact_mod_cast hj
        have e : (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ ^ j : ℕ) : ℝ) =
            (q : ℝ) ^ 2 * n * (n + 1) * (1 / (ℓ : ℝ)) ^ j := by
          rw [one_div_pow, mul_one_div]; push_cast; rfl
        rw [e] at this
        have : ((ℓ ^ j : ℕ) : ℝ) * (q : ℝ) ^ 2 / 4 ≤ (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by
          have := mul_le_mul_of_nonneg_right hMle (sq_nonneg (q : ℝ)); linarith
        linarith
      · push_neg at hj
        have : (∑ c ∈ range (ℓ ^ j), Ecl q n (ℓ ^ j) c s : ℤ) ≤ 0 :=
          sum_nonpos fun c hc => Ecl_nonpos hn hj c (mem_range.1 hc) s
        have : ((∑ c ∈ range (ℓ ^ j), Ecl q n (ℓ ^ j) c s : ℤ) : ℝ) ≤ 0 := by exact_mod_cast this
        have : (0 : ℝ) ≤ (q : ℝ) ^ 2 * n * (n + 1) * (1 / (ℓ : ℝ)) ^ j := by positivity
        linarith
    have hs1 := sum_le_sum hlev
    push_cast at hs1
    rw [sum_add_distrib, ← mul_sum] at hs1
    have hg := geom_levels hℓ1 (2 * R n + 1)
    have hc : ∑ j ∈ Icc 1 (2 * R n + 1), (if ℓ ^ j ≤ 3 * n + 1 then (3 * n + 1) * (q : ℝ) ^ 2 / 4 else 0)
        ≤ Nat.log ℓ (3 * n + 1) * (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have := card_levels_le hℓ1 (3 * n + 1) (2 * R n + 1) (by omega)
      have h' : (((Icc 1 (2 * R n + 1)).filter fun j => ℓ ^ j ≤ 3 * n + 1).card : ℝ) ≤
          Nat.log ℓ (3 * n + 1) := by exact_mod_cast this
      have : (0 : ℝ) ≤ (3 * n + 1) * (q : ℝ) ^ 2 / 4 := by positivity
      nlinarith
    have hA : (0 : ℝ) ≤ (q : ℝ) ^ 2 * n * (n + 1) := by positivity
    have e3 : (q : ℝ) ^ 2 * n * (n + 1) / ((ℓ : ℝ) - 1) = (q : ℝ) ^ 2 * n * (n + 1) * (1 / ((ℓ : ℝ) - 1)) := by
      ring
    rw [e3]
    nlinarith [mul_le_mul_of_nonneg_left hg hA]

end TwoAdicWin.Asm
