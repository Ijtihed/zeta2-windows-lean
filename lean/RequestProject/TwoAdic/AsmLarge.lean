import RequestProject.TwoAdic.AsmCellCover
import RequestProject.TwoAdic.AsmIntegrand
import RequestProject.TwoAdic.AsmRiemann

/-!
# Large primes `ℓ > n/20` (II, Cor. 5.4)

* `large_prime_bound`: for a single-level prime `ℓ` with `u = ℓ/n` in a certificate cell `c` with
  checked arcs `D` and `n ≤ 20ℓ`:
  `T⁺_ℓ ≤ q² n g_c(u) + q² E`, `g_c = integrandT c.types δ`, `E = 2 m · 7936` (`m` arcs);
  this is the relaxation `relax_bound` at every `τ ≥ 0`, the exact counting `cell_cover`, and the
  infimum over `τ`.
* `cell_sum`: summing over the primes `ℓ ∈ (a n, b n]` of one cell with weights `ln ℓ`, with the
  prime Riemann sums of the Lipschitz function `g_c` (`riemann_upper`):
  `∑ T⁺_ℓ ln ℓ ≤ q² n² (∫_a^b g_c + η) + C n` for all large `n`.
-/

open Finset Filter Topology Chebyshev MeasureTheory

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin Arc Cert

variable {q d n ℓ : ℕ}

/-- The measures of the types of a checked cell are nonnegative on the cell. -/
theorem cell_meas_nonneg {c : CellD} {D : ArcsD} (hok : cellArcsOK c D = true) :
    ∀ ty ∈ c.types, ∀ u ∈ Set.Icc (c.a : ℝ) c.b, 0 ≤ measR ty u := by
  intro ty hty u hu
  unfold cellArcsOK at hok
  simp only [Bool.and_eq_true] at hok
  have hm := hok.2
  unfold measOK at hm
  rw [List.all_eq_true] at hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hty
  have := hm i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨_, h1⟩, h2⟩ := this
  rw [List.getD_eq_getElem _ _ hi] at h1 h2
  have h1' : (0 : ℝ) ≤ measR c.types[i] c.a := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    simpa [measQ, measR] using this
  have h2' : (0 : ℝ) ≤ measR c.types[i] c.b := by
    have := (Rat.cast_le (K := ℝ)).2 h2
    simpa [measQ, measR] using this
  unfold measR at h1' h2' ⊢
  rcases le_total 0 (c.types[i].m1 : ℝ) with h0 | h0
  · nlinarith [mul_le_mul_of_nonneg_left hu.1 h0]
  · nlinarith [mul_le_mul_of_nonpos_left hu.2 h0]

/-- **One large prime.** -/
theorem large_prime_bound [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n) (h2 : ℓ ≠ 2)
    (hsl : 4 * n < ℓ ^ 2) (hq : 0 < q) (hδ : deltaOf q d ≤ 1) {c : CellD} {D : ArcsD}
    (hok : cellArcsOK c D = true) (hs : Setting c.a c.b n ℓ) (hℓn : n ≤ 20 * ℓ) :
    (TPplus q d n ℓ (q * n) : ℝ) ≤
      (q : ℝ) ^ 2 * n * integrandT c.types (deltaOf q d) ((ℓ : ℝ) / n) +
        (q : ℝ) ^ 2 * (2 * D.arcs.length * 7936) := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  have hℓodd : Odd ℓ := hp.out.odd_of_ne_two h2
  set δ := deltaOf q d
  set u : ℝ := (ℓ : ℝ) / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the error constant
  have hNb : (3 * n + 1) / ℓ + 1 ≤ 62 := by
    have : (3 * n + 1) / ℓ ≤ 61 := Nat.div_le_of_le_mul (by nlinarith)
    omega
  have hKb : 2 * (((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) * ((((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) + 2) ≤ 7936 := by
    have h : (((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) ≤ 62 := by exact_mod_cast hNb
    have h0 : (0 : ℝ) ≤ (((3 * n + 1) / ℓ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hlen : (0 : ℝ) ≤ D.arcs.length := Nat.cast_nonneg _
  set E : ℝ := 2 * D.arcs.length * 7936
  -- the bound for every `τ`
  have hτ : ∀ τ : ℝ, 0 ≤ τ → ((TPplus q d n ℓ (q * n) : ℝ) - q ^ 2 * E) / (q ^ 2 * n) ≤
      fTau c.types δ u τ := by
    intro τ hτ
    have h1 := relax_bound (d := d) hn hn1 h2 hsl hq hτ
    have h2' := cell_cover (δ := δ) hn hℓodd hok hs (by simpa [δ] using hδ) hτ
    have h3 : ∑ r ∈ range ℓ, knap (classAlphas n ℓ δ r) τ ≤
        n * (c.types.map fun t => measR t u * knap (alphasR t δ) τ).sum + E := by
      refine h2'.trans (add_le_add_right ?_ _)
      simp only [E]
      exact mul_le_mul_of_nonneg_left hKb (by positivity)
    rw [div_le_iff₀ (by positivity)]
    unfold fTau
    have : (TPplus q d n ℓ (q * n) : ℝ) ≤ q ^ 2 * (τ * n + (n *
        (c.types.map fun t => measR t u * knap (alphasR t δ) τ).sum + E)) :=
      h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    nlinarith
  have := le_integrandT c.types δ u hτ
  rw [div_le_iff₀ (by positivity)] at this
  nlinarith

section CellSum

variable (hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
include hθ

/-- **The primes of one cell.** -/
theorem cell_sum (hq : 0 < q) (hδ : deltaOf q d ≤ 1) {c : CellD} {D : ArcsD}
    (hok : cellArcsOK c D = true) (hc20 : 1 / 20 ≤ c.a) {η : ℝ} (hη : 0 < η) :
    ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → Even n → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
      ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (c.a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ c.b * n),
          (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
        (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * ((∫ u in (c.a : ℝ)..c.b, integrandT c.types (deltaOf q d) u) + η) +
          C * n := by
  set δ := deltaOf q d
  have hok' := hok
  unfold cellArcsOK at hok'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
  have ha0 : (0 : ℚ) < c.a := hok'.1.1.1.1.1
  have hab : c.a ≤ c.b := hok'.1.1.1.1.2
  have ha0R : (0 : ℝ) < c.a := by exact_mod_cast ha0
  have habR : (c.a : ℝ) ≤ c.b := by exact_mod_cast hab
  have hmeas := cell_meas_nonneg hok
  have hg0 : ∀ x ∈ Set.Icc (c.a : ℝ) c.b, 0 ≤ integrandT c.types δ x :=
    fun x hx => integrandT_nonneg _ _ _ fun t ht => hmeas t ht x hx
  have hgL : ∀ x ∈ Set.Icc (c.a : ℝ) c.b, ∀ y ∈ Set.Icc (c.a : ℝ) c.b,
      |integrandT c.types δ x - integrandT c.types δ y| ≤ Lc c.types δ * |x - y| :=
    fun x hx y hy => integrandT_lipschitz _ _ _ _ (fun t ht => hmeas t ht x hx)
      (fun t ht => hmeas t ht y hy)
  have hint : IntervalIntegrable (integrandT c.types δ) volume c.a c.b :=
    integrandT_intervalIntegrable _ _ fun t ht u hu => hmeas t ht u (by rwa [Set.uIcc_of_le habR] at hu)
  obtain ⟨N₀, hN₀, hR⟩ := riemann_upper hθ ha0R habR (Lc_nonneg c.types δ) hg0 hgL hint hη
  set E : ℝ := 2 * D.arcs.length * 7936
  have hE : 0 ≤ E := by positivity
  refine ⟨(q : ℝ) ^ 2 * E * (Real.log 4 * c.b), max N₀ 1601, fun n hn hev S hS => ?_⟩
  have hn1601 : (1601 : ℝ) ≤ n := (le_max_right _ _).trans hn
  have hnN : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hnR : (0 : ℝ) < n := by linarith
  set P := S.filter (fun ℓ : ℕ => (c.a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ c.b * n)
  have hPmem : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ≠ 2 ∧ (c.a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ c.b * n := by
    intro ℓ hℓ
    simp only [P, mem_filter] at hℓ
    exact ⟨(hS ℓ hℓ.1).1, (hS ℓ hℓ.1).2, hℓ.2⟩
  -- each prime
  have hone : ∀ ℓ ∈ P, (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
      ((q : ℝ) ^ 2 * n) * (Real.log ℓ * integrandT c.types δ ((ℓ : ℝ) / n)) +
        (q : ℝ) ^ 2 * E * Real.log ℓ := by
    intro ℓ hℓ
    obtain ⟨hp, h2, h1, h3⟩ := hPmem ℓ hℓ
    haveI : Fact ℓ.Prime := ⟨hp⟩
    have hc20R : (1 / 20 : ℝ) ≤ c.a := by
      have := (Rat.cast_le (K := ℝ)).2 hc20; push_cast at this; exact this
    have hl20 : (n : ℝ) / 20 < ℓ := by nlinarith [mul_le_mul_of_nonneg_right hc20R hnR.le]
    have hℓn : n ≤ 20 * ℓ := by
      have : (n : ℝ) ≤ 20 * ℓ := by linarith
      exact_mod_cast this
    have hsl : 4 * n < ℓ ^ 2 := by
      have : (4 : ℝ) * n < (ℓ : ℝ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ n / 20 := by positivity
        nlinarith [mul_lt_mul'' hl20 hl20 h0 h0]
      exact_mod_cast this
    have hs : Setting c.a c.b n ℓ := by
      refine ⟨by omega, ?_, ?_⟩
      · rw [le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))]
        have : ((c.a : ℚ) : ℝ) * n ≤ ((ℓ : ℚ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · rw [div_le_iff₀ (by exact_mod_cast (show 0 < n by omega))]
        have : ((ℓ : ℚ) : ℝ) ≤ ((c.b : ℚ) : ℝ) * n := by push_cast; linarith
        exact_mod_cast this
    have hb := large_prime_bound hev hn1 h2 hsl hq hδ hok hs hℓn
    have hlog : 0 ≤ Real.log ℓ := Real.log_natCast_nonneg ℓ
    calc (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ
        ≤ ((q : ℝ) ^ 2 * n * integrandT c.types δ ((ℓ : ℝ) / n) + (q : ℝ) ^ 2 * E) * Real.log ℓ :=
          mul_le_mul_of_nonneg_right hb hlog
      _ = _ := by ring
  refine (sum_le_sum hone).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hRn := hR n hnN P fun p hp => ⟨(hPmem p hp).1, (hPmem p hp).2.2⟩
  have hθP : ∑ p ∈ P, Real.log p ≤ Real.log 4 * (c.b * n) := by
    have h1 := Hankel2.sum_log_le_theta_sub P (x := c.a * n) (y := c.b * n)
      (mul_le_mul_of_nonneg_right habR hnR.le) (fun p hp => ⟨(hPmem p hp).1, (hPmem p hp).2.2⟩)
    have h2 := theta_nonneg (c.a * n)
    have h3 := theta_le_log4_mul_x (x := c.b * n) (mul_nonneg (by linarith) hnR.le)
    linarith
  have hqn : (0 : ℝ) ≤ (q : ℝ) ^ 2 * n := by positivity
  have hqE : (0 : ℝ) ≤ (q : ℝ) ^ 2 * E := by positivity
  calc (q : ℝ) ^ 2 * n * ∑ p ∈ P, Real.log p * integrandT c.types δ ((p : ℝ) / n) +
        (q : ℝ) ^ 2 * E * ∑ p ∈ P, Real.log p
      ≤ (q : ℝ) ^ 2 * n * (n * ((∫ u in (c.a : ℝ)..c.b, integrandT c.types δ u) + η)) +
          (q : ℝ) ^ 2 * E * (Real.log 4 * (c.b * n)) :=
        add_le_add (mul_le_mul_of_nonneg_left hRn hqn) (mul_le_mul_of_nonneg_left hθP hqE)
    _ = _ := by ring

end CellSum

end TwoAdicWin.Asm
