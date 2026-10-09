import RequestProject.TwoAdic.AsmLarge
import RequestProject.TwoAdic.ArcAll
import RequestProject.TwoAdic.CertFinal

/-!
# The chain of certificate cells: the integral `circCert` and the large primes

* `chain_integral`: along a checked chain of cells, `cellVal` is interval integrable and its integral
  is the sum of the integrals of the cell integrands; hence (`circCert_eq`)
  `circCert δ = ∑_cells ∫_a^b integrandT c.types δ`.
* `chain_prime_sum`: the primes `ℓ ∈ (a n, e n]` of a chain of cells:
  `∑ T⁺_ℓ ln ℓ ≤ q² n² (∑_cells ∫ + m η) + C n` for large `n`.
* **`large_primes_sum`**: the primes `ℓ ∈ (n/20, 7n/2]`:
  `∑ T⁺_ℓ ln ℓ ≤ q² n² (circCert δ + η) + C n` for large `n`.
-/

open Finset Filter Topology Chebyshev MeasureTheory

namespace TwoAdicWin.Asm

open Dom Leaf Lev PadicWin Arc Cert

variable {q d : ℕ}

theorem TPplus_nonneg (q d n ℓ K : ℕ) : 0 ≤ TPplus q d n ℓ K := by
  unfold TPplus
  induction h : max (TP q d n ℓ K) 0 using WithBot.recBotCoe with
  | bot => simp
  | coe t =>
    simp only [WithBot.unbotD_coe]
    have : (0 : WithBot ℤ) ≤ (t : WithBot ℤ) := h ▸ le_max_right _ _
    exact_mod_cast this

theorem cell_a_le_b {c : CellD} {D : ArcsD} (hok : cellArcsOK c D = true) : c.a ≤ c.b := by
  unfold cellArcsOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1.1.1.2

theorem le_lastCell : ∀ (cs : List CellD) (a : ℚ), cellsOK a cs = true →
    (∀ c ∈ cs, ∃ D, cellArcsOK c D = true) → a ≤ lastCell a cs
  | [], a, _, _ => by simp [lastCell]
  | c :: cs, a, h, hD => by
    simp only [cellsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨D, hc⟩ := hD c (List.mem_cons_self ..)
    have := le_lastCell cs c.b h.2 fun c' hc' => hD c' (List.mem_cons_of_mem _ hc')
    simp only [lastCell]
    have := cell_a_le_b hc
    rw [← h.1.1]; linarith

theorem ae_ne (x : ℝ) : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ x := by
  rw [ae_iff]; simp

/-- **The integral along a chain of cells.** -/
theorem chain_integral (δ : ℝ) : ∀ (cs : List CellD) (a : ℚ), cellsOK a cs = true →
    (∀ c ∈ cs, ∃ D, cellArcsOK c D = true) →
    IntervalIntegrable (cellVal cs δ) volume (a : ℝ) (lastCell a cs) ∧
      ∫ u in (a : ℝ)..(lastCell a cs), cellVal cs δ u =
        (cs.map fun c => ∫ u in (c.a : ℝ)..c.b, integrandT c.types δ u).sum
  | [], a, _, _ => by simp [lastCell]
  | c :: cs, a, h, hD => by
    simp only [cellsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca, _⟩, hrest⟩ := h
    obtain ⟨D, hc⟩ := hD c (List.mem_cons_self ..)
    have hD' : ∀ c' ∈ cs, ∃ D, cellArcsOK c' D = true := fun c' hc' => hD c' (List.mem_cons_of_mem _ hc')
    obtain ⟨ih1, ih2⟩ := chain_integral δ cs c.b hrest hD'
    have hab : (c.a : ℝ) ≤ c.b := by exact_mod_cast cell_a_le_b hc
    have hbl : (c.b : ℝ) ≤ lastCell c.b cs := by exact_mod_cast le_lastCell cs c.b hrest hD'
    have hmeas := cell_meas_nonneg hc
    have I1 : IntervalIntegrable (integrandT c.types δ) volume c.a c.b :=
      integrandT_intervalIntegrable _ _ fun t ht u hu =>
        hmeas t ht u (by rwa [Set.uIcc_of_le hab] at hu)
    rw [← hca] at *
    simp only [lastCell]
    -- the first cell
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (c.a : ℝ) c.b →
        integrandT c.types δ x = cellVal (c :: cs) δ x := by
      filter_upwards [ae_ne (c.b : ℝ)] with x hx hxI
      rw [Set.uIoc_of_le hab] at hxI
      simp only [cellVal]
      rw [if_pos (lt_of_le_of_ne hxI.2 hx)]
    have J1 : IntervalIntegrable (cellVal (c :: cs) δ) volume c.a c.b := by
      refine I1.congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      exact hae
    have heq : Set.EqOn (cellVal (c :: cs) δ) (cellVal cs δ) (Set.uIcc (c.b : ℝ) (lastCell c.b cs)) := by
      intro x hx
      rw [Set.uIcc_of_le hbl] at hx
      simp only [cellVal]
      rw [if_neg (not_lt.2 hx.1)]
    have J2 : IntervalIntegrable (cellVal (c :: cs) δ) volume c.b (lastCell c.b cs) :=
      (intervalIntegrable_congr fun x hx => heq (Set.uIoc_subset_uIcc hx)).2 ih1
    refine ⟨J1.trans J2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals J1 J2]
    rw [intervalIntegral.integral_congr heq, ih2]
    rw [← intervalIntegral.integral_congr_ae hae]
    simp

/-- `circCert` is the sum of the cell integrals. -/
theorem circCert_eq (δ : ℝ) :
    circCert δ = (certCells.map fun c => ∫ u in (c.a : ℝ)..c.b, integrandT c.types δ u).sum := by
  obtain ⟨hok, hlast, _⟩ := certCells_blk
  have := (chain_integral δ certCells (1 / 20) hok certCells_arcs).2
  rw [hlast] at this
  unfold circCert
  have e1 : ((1 / 20 : ℚ) : ℝ) = 1 / 20 := by norm_num
  have e2 : ((7 / 2 : ℚ) : ℝ) = 7 / 2 := by norm_num
  rw [e1, e2] at this
  exact this

section Primes

variable (hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
include hθ

/-- **The primes of a chain of cells.** -/
theorem chain_prime_sum (hq : 0 < q) (hδ : deltaOf q d ≤ 1) :
    ∀ (cs : List CellD) (a : ℚ), cellsOK a cs = true → (∀ c ∈ cs, ∃ D, cellArcsOK c D = true) →
      1 / 20 ≤ a → ∀ η : ℝ, 0 < η →
      ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → Even n → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
        ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ (lastCell a cs : ℝ) * n),
            (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
          (q : ℝ) ^ 2 * (n : ℝ) ^ 2 *
            ((cs.map fun c => ∫ u in (c.a : ℝ)..c.b, integrandT c.types (deltaOf q d) u).sum +
              cs.length * η) + C * n
  | [], a, _, _, _, η, hη => by
    refine ⟨0, 0, fun n _ _ S _ => ?_⟩
    have : S.filter (fun ℓ : ℕ => (a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ (lastCell a [] : ℝ) * n) = ∅ := by
      ext ℓ; simp only [lastCell, mem_filter, notMem_empty, iff_false, not_and, not_le]
      intro _ h; exact h
    rw [this]; simp
  | c :: cs, a, h, hD, ha20, η, hη => by
    simp only [cellsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca, _⟩, hrest⟩ := h
    obtain ⟨D, hc⟩ := hD c (List.mem_cons_self ..)
    have hD' : ∀ c' ∈ cs, ∃ D, cellArcsOK c' D = true := fun c' hc' => hD c' (List.mem_cons_of_mem _ hc')
    have hab := cell_a_le_b hc
    obtain ⟨C1, N1, h1⟩ := cell_sum hθ hq hδ hc (hca ▸ ha20) hη
    obtain ⟨C2, N2, h2⟩ := chain_prime_sum hq hδ cs c.b hrest hD' (by rw [hca] at hab; linarith) η hη
    refine ⟨C1 + C2, max N1 N2, fun n hn hev S hS => ?_⟩
    have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
    have hn2 : N2 ≤ n := (le_max_right _ _).trans hn
    have hF0 : ∀ ℓ, 0 ≤ (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ := fun ℓ =>
      mul_nonneg (by exact_mod_cast TPplus_nonneg _ _ _ _ _) (Real.log_natCast_nonneg ℓ)
    set A := S.filter (fun ℓ : ℕ => (a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ (lastCell a (c :: cs) : ℝ) * n)
    rw [← sum_filter_add_sum_filter_not A (fun ℓ : ℕ => (ℓ : ℝ) ≤ c.b * n)]
    have s1 : ∑ ℓ ∈ A.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ c.b * n), (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
        ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (c.a : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ c.b * n),
          (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ := by
      refine sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) (fun ℓ _ _ => hF0 ℓ)
      simp only [A, mem_filter] at hℓ ⊢
      exact ⟨hℓ.1.1, by rw [← hca] at hℓ; exact hℓ.1.2.1, hℓ.2⟩
    have s2 : ∑ ℓ ∈ A.filter (fun ℓ : ℕ => ¬ (ℓ : ℝ) ≤ c.b * n), (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
        ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (c.b : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ (lastCell c.b cs : ℝ) * n),
          (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ := by
      refine sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) (fun ℓ _ _ => hF0 ℓ)
      simp only [A, mem_filter, lastCell, not_le] at hℓ ⊢
      exact ⟨hℓ.1.1, hℓ.2, hℓ.1.2.2⟩
    have e1 := h1 n hn1 hev S hS
    have e2 := h2 n hn2 hev S hS
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    nlinarith [e1, e2, s1, s2]

/-- **The primes `ℓ ∈ (n/20, 7n/2]`.** -/
theorem large_primes_sum (hq : 0 < q) (hδ : deltaOf q d ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → Even n → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2) →
      ∑ ℓ ∈ S.filter (fun ℓ : ℕ => (n : ℝ) / 20 < ℓ ∧ (ℓ : ℝ) ≤ 7 / 2 * n),
          (TPplus q d n ℓ (q * n) : ℝ) * Real.log ℓ ≤
        (q : ℝ) ^ 2 * (n : ℝ) ^ 2 * (circCert (deltaOf q d) + η) + C * n := by
  obtain ⟨hok, hlast, _⟩ := certCells_blk
  have hL : (0 : ℝ) < certCells.length + 1 := by positivity
  obtain ⟨C, N, h⟩ := chain_prime_sum hθ hq hδ certCells (1 / 20) hok certCells_arcs le_rfl
    (η / (certCells.length + 1)) (div_pos hη hL)
  refine ⟨C, N, fun n hn hev S hS => ?_⟩
  have e := h n hn hev S hS
  rw [hlast, ← circCert_eq] at e
  have e1 : ((1 / 20 : ℚ) : ℝ) = 1 / 20 := by norm_num
  have e2 : ((7 / 2 : ℚ) : ℝ) = 7 / 2 := by norm_num
  have hS : S.filter (fun ℓ : ℕ => (n : ℝ) / 20 < ℓ ∧ (ℓ : ℝ) ≤ 7 / 2 * n) =
      S.filter (fun ℓ : ℕ => ((1 / 20 : ℚ) : ℝ) * n < ℓ ∧ (ℓ : ℝ) ≤ ((7 / 2 : ℚ) : ℝ) * n) := by
    rw [e1, e2]; congr 1; ext ℓ; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
  rw [hS]
  refine e.trans ?_
  have : (certCells.length : ℝ) * (η / (certCells.length + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ hL]; nlinarith
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hq2]

end Primes

/-- **Primes `ℓ > 3n + 1` contribute nothing**: every class has at most one node, no node is hs and
none is kept, so the relaxation at `τ = 0` gives `T⁺_ℓ ≤ 0`. -/
theorem TPplus_eq_zero_of_large {n ℓ : ℕ} [hp : Fact ℓ.Prime] (hn : Even n) (hn1 : 1 ≤ n)
    (h2 : ℓ ≠ 2) (hq : 0 < q) (hℓ : 3 * n + 1 < ℓ) : TPplus q d n ℓ (q * n) = 0 := by
  have hℓ0 : 0 < ℓ := hp.out.pos
  have hsl : 4 * n < ℓ ^ 2 := by nlinarith
  have hR := R_of_even hn
  have hnil : ∀ r ∈ range ℓ, classAlphas n ℓ (deltaOf q d) r = [] := by
    intro r hr
    have hN := (card_cls_bounds n ℓ r hℓ0 (mem_range.1 hr)).2
    have hdiv : (2 * R n + 1) / ℓ = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv] at hN
    have hnh : nhs n ℓ r = 0 := by
      unfold nhs
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i _
      have := nodeOf_mem_nodes' n i
      simp only [nodes, mem_Icc] at this
      have : |nodeOf n i| ≤ R n := abs_le.2 ⟨this.1, this.2⟩
      omega
    unfold classAlphas
    rw [hnh, alphasR_runsOf]
    simp only [List.replicate_zero, List.nil_append, List.replicate_eq_nil_iff]
    split_ifs with h
    · omega
    · rfl
  have h := relax_bound (d := d) hn hn1 h2 hsl hq (le_refl (0 : ℝ))
  rw [sum_congr rfl fun r hr => by rw [hnil r hr, knap_nil]] at h
  simp only [sum_const_zero, zero_mul, add_zero, mul_zero] at h
  have h0 := TPplus_nonneg q d n ℓ (q * n)
  have : (TPplus q d n ℓ (q * n) : ℝ) ≤ 0 := h
  exact le_antisymm (by exact_mod_cast this) h0

end TwoAdicWin.Asm
