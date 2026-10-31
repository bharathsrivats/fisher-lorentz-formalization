/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The positive expansion that drives the area law. Nothing here mentions a lattice.
Write the weight of each expandable term as `1 + h i` with `0 ≤ h i ≤ p * (1 + h i)`,
expand the product over subsets, and keep only the subsets that contain one of a given
family of sets. The rest vanish by hypothesis, in the application by a centre twist.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Finset

namespace Confinement

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
variable {ι κ : Type*} [DecidableEq ι] [Fintype κ]

/-- Pointwise: the terms of the expansion over subsets containing `S` sum to at most
`p ^ S.card` times the whole product. -/
lemma sum_superset_prod_le (P S : Finset ι) (hS : S ⊆ P) (h : ι → ℝ) {p : ℝ}
    (h0 : ∀ i ∈ P, 0 ≤ h i) (hp : ∀ i ∈ P, h i ≤ p * (1 + h i)) :
    ∑ A ∈ P.powerset.filter (S ⊆ ·), ∏ i ∈ A, h i ≤ p ^ S.card * ∏ i ∈ P, (1 + h i) := by
  classical
  -- the indicator trick: `g i = 0` on `S`, `g i = 1` off `S`
  have key := Finset.prod_add h (fun i => if i ∈ S then (0 : ℝ) else 1) P
  have hterm : ∀ A ∈ P.powerset,
      (∏ i ∈ A, h i) * ∏ i ∈ P \ A, (if i ∈ S then (0 : ℝ) else 1)
        = if S ⊆ A then ∏ i ∈ A, h i else 0 := by
    intro A hA
    have hA' := Finset.mem_powerset.mp hA
    split_ifs with hSA
    · have : ∏ i ∈ P \ A, (if i ∈ S then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hi' : i ∉ S := fun hiS => (Finset.mem_sdiff.mp hi).2 (hSA hiS)
        simp [hi']
      rw [this, mul_one]
    · obtain ⟨i, hiS, hiA⟩ := Finset.not_subset.mp hSA
      have : ∏ i ∈ P \ A, (if i ∈ S then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hS hiS, hiA⟩)
        simp [hiS]
      rw [this, mul_zero]
  have hsum : ∑ A ∈ P.powerset.filter (S ⊆ ·), ∏ i ∈ A, h i
      = ∏ i ∈ P, (h i + if i ∈ S then (0 : ℝ) else 1) := by
    rw [key, Finset.sum_filter]
    exact (Finset.sum_congr rfl hterm).symm
  rw [hsum]
  have hle : ∏ i ∈ P, (h i + if i ∈ S then (0 : ℝ) else 1)
      ≤ ∏ i ∈ P, ((if i ∈ S then p else 1) * (1 + h i)) := by
    apply Finset.prod_le_prod
    · intro i hi
      have := h0 i hi
      split_ifs <;> linarith
    · intro i hi
      have := hp i hi
      split_ifs <;> linarith
  refine hle.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hS, Finset.prod_const]

/-- **The expansion bound.** Let `W` be bounded by one, `H ≥ 0` bounded, and `0 ≤ h i ≤ M` with
`h i ≤ p (1 + h i)`. Suppose every subset `A ⊆ P` either contains some `S k` or its term
vanishes. Then the expectation of `W` under the weight `H ∏ (1 + h)` is at most
`∑ k, p ^ (S k).card` in modulus, in the cross-multiplied form below. -/
theorem expansion_bound (P : Finset ι) (S : κ → Finset ι) (hSP : ∀ k, S k ⊆ P)
    (h : ι → Ω → ℝ) (H : Ω → ℝ) (W : Ω → ℂ) {p M C : ℝ}
    (hm : ∀ i ∈ P, Measurable (h i)) (hHm : Measurable H) (hWm : Measurable W)
    (h0 : ∀ i ∈ P, ∀ ω, 0 ≤ h i ω) (hM : ∀ i ∈ P, ∀ ω, h i ω ≤ M)
    (hle : ∀ i ∈ P, ∀ ω, h i ω ≤ p * (1 + h i ω))
    (hH0 : ∀ ω, 0 ≤ H ω) (hHC : ∀ ω, H ω ≤ C) (hW : ∀ ω, ‖W ω‖ ≤ 1)
    (hvanish : ∀ A ∈ P.powerset, (∃ k, S k ⊆ A) ∨
      ∫ ω, W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ) ∂ν = 0) :
    ‖∫ ω, W ω * ((H ω * ∏ i ∈ P, (1 + h i ω) : ℝ) : ℂ) ∂ν‖
      ≤ (∑ k, p ^ (S k).card) * ∫ ω, H ω * ∏ i ∈ P, (1 + h i ω) ∂ν := by
  classical
  -- integrability of every bounded measurable integrand
  have hprodm : ∀ A : Finset ι, A ⊆ P → Measurable fun ω => ∏ i ∈ A, h i ω := fun A hA =>
    Finset.measurable_prod _ (fun i hi => hm i (hA hi))
  have hM0 : ∀ A : Finset ι, A ⊆ P → ∀ ω, 0 ≤ ∏ i ∈ A, h i ω := fun A hA ω =>
    Finset.prod_nonneg (fun i hi => h0 i (hA hi) ω)
  have hMb : ∀ A : Finset ι, A ⊆ P → ∀ ω, ∏ i ∈ A, h i ω ≤ ∏ _i ∈ A, M := fun A hA ω =>
    Finset.prod_le_prod (fun i hi => h0 i (hA hi) ω) (fun i hi => hM i (hA hi) ω)
  have hint : ∀ A : Finset ι, A ⊆ P → Integrable (fun ω => H ω * ∏ i ∈ A, h i ω) ν := by
    intro A hA
    refine Integrable.of_bound ((hHm.mul (hprodm A hA)).aestronglyMeasurable)
      (C * ∏ _i ∈ A, M) (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hH0 ω
    have h2 := hM0 A hA ω
    rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
    exact mul_le_mul (hHC ω) (hMb A hA ω) h2 ((hH0 ω).trans (hHC ω))
  have hintW : ∀ A : Finset ι, A ⊆ P →
      Integrable (fun ω => W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ)) ν := by
    intro A hA
    refine (hint A hA).ofReal.bdd_mul (c := 1) hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall hW)
  -- expand the product
  have hexp : ∀ ω, ∏ i ∈ P, (1 + h i ω) = ∑ A ∈ P.powerset, ∏ i ∈ A, h i ω := fun ω =>
    Finset.prod_one_add P
  have hZ : ∫ ω, H ω * ∏ i ∈ P, (1 + h i ω) ∂ν
      = ∑ A ∈ P.powerset, ∫ ω, H ω * ∏ i ∈ A, h i ω ∂ν := by
    simp_rw [hexp, Finset.mul_sum]
    exact integral_finsetSum _ fun A hA => hint A (Finset.mem_powerset.mp hA)
  have hN : ∫ ω, W ω * ((H ω * ∏ i ∈ P, (1 + h i ω) : ℝ) : ℂ) ∂ν
      = ∑ A ∈ P.powerset, ∫ ω, W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ) ∂ν := by
    have : ∀ ω, W ω * ((H ω * ∏ i ∈ P, (1 + h i ω) : ℝ) : ℂ)
        = ∑ A ∈ P.powerset, W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ) := by
      intro ω
      rw [hexp ω, Finset.mul_sum]
      push_cast
      rw [Finset.mul_sum]
    simp_rw [this]
    exact integral_finsetSum _ fun A hA => hintW A (Finset.mem_powerset.mp hA)
  -- each term is bounded by the positive weight of `A`
  set w : Finset ι → ℝ := fun A => ∫ ω, H ω * ∏ i ∈ A, h i ω ∂ν with hw
  have hw0 : ∀ A ∈ P.powerset, 0 ≤ w A := fun A hA =>
    integral_nonneg fun ω => mul_nonneg (hH0 ω) (hM0 A (Finset.mem_powerset.mp hA) ω)
  have hterm : ∀ A ∈ P.powerset,
      ‖∫ ω, W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ) ∂ν‖ ≤ w A := by
    intro A hA
    have hA' := Finset.mem_powerset.mp hA
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
        (hint A hA') (Filter.Eventually.of_forall fun ω => ?_))
    have hnn := mul_nonneg (hH0 ω) (hM0 A hA' ω)
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
    calc ‖W ω‖ * (H ω * ∏ i ∈ A, h i ω)
        ≤ 1 * (H ω * ∏ i ∈ A, h i ω) := mul_le_mul_of_nonneg_right (hW ω) hnn
      _ = _ := one_mul _
  -- the good subsets
  set good := P.powerset.filter fun A => ∃ k, S k ⊆ A with hgood
  have hnum : ‖∫ ω, W ω * ((H ω * ∏ i ∈ P, (1 + h i ω) : ℝ) : ℂ) ∂ν‖ ≤ ∑ A ∈ good, w A := by
    rw [hN, ← Finset.sum_filter_add_sum_filter_not P.powerset (fun A => ∃ k, S k ⊆ A)]
    have hzero : ∑ A ∈ P.powerset.filter (fun A => ¬ ∃ k, S k ⊆ A),
        ∫ ω, W ω * ((H ω * ∏ i ∈ A, h i ω : ℝ) : ℂ) ∂ν = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      obtain ⟨hAP, hAn⟩ := Finset.mem_filter.mp hA
      exact (hvanish A hAP).resolve_left hAn
    rw [hzero, add_zero]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A hA => ?_)
    exact hterm A (Finset.mem_filter.mp hA).1
  -- union bound over `k`
  have hunion : ∑ A ∈ good, w A
      ≤ ∑ k, ∑ A ∈ P.powerset.filter (S k ⊆ ·), w A := by
    simp_rw [hgood, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun A hA => ?_
    have hnn : ∀ j ∈ (Finset.univ : Finset κ), 0 ≤ if S j ⊆ A then w A else 0 := fun j _ => by
      split_ifs
      · exact hw0 A hA
      · exact le_rfl
    split_ifs with hex
    · obtain ⟨k, hk⟩ := hex
      have := Finset.single_le_sum hnn (Finset.mem_univ k)
      simpa [hk] using this
    · exact Finset.sum_nonneg hnn
  -- each superset sum is at most `p ^ |S k|` times the partition function
  have hsup : ∀ k, ∑ A ∈ P.powerset.filter (S k ⊆ ·), w A
      ≤ p ^ (S k).card * ∫ ω, H ω * ∏ i ∈ P, (1 + h i ω) ∂ν := by
    intro k
    have hswap : ∑ A ∈ P.powerset.filter (S k ⊆ ·), w A
        = ∫ ω, H ω * ∑ A ∈ P.powerset.filter (S k ⊆ ·), ∏ i ∈ A, h i ω ∂ν := by
      simp_rw [hw, Finset.mul_sum]
      exact (integral_finsetSum _ fun A hA =>
        hint A (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)).symm
    rw [hswap, ← integral_const_mul]
    have hint2 : Integrable (fun ω => H ω * ∏ i ∈ P, (1 + h i ω)) ν := by
      simp_rw [hexp, Finset.mul_sum]
      exact integrable_finsetSum _ fun A hA => hint A (Finset.mem_powerset.mp hA)
    have hint1 : Integrable
        (fun ω => H ω * ∑ A ∈ P.powerset.filter (S k ⊆ ·), ∏ i ∈ A, h i ω) ν := by
      simp_rw [Finset.mul_sum]
      exact integrable_finsetSum _ fun A hA =>
        hint A (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
    refine integral_mono hint1 (hint2.const_mul _) fun ω => ?_
    have hb := sum_superset_prod_le P (S k) (hSP k) (fun i => h i ω)
      (fun i hi => h0 i hi ω) (fun i hi => hle i hi ω)
    calc H ω * ∑ A ∈ P.powerset.filter (S k ⊆ ·), ∏ i ∈ A, h i ω
        ≤ H ω * (p ^ (S k).card * ∏ i ∈ P, (1 + h i ω)) :=
          mul_le_mul_of_nonneg_left hb (hH0 ω)
      _ = p ^ (S k).card * (H ω * ∏ i ∈ P, (1 + h i ω)) := by ring
  calc _ ≤ ∑ A ∈ good, w A := hnum
    _ ≤ _ := hunion
    _ ≤ ∑ k, p ^ (S k).card * ∫ ω, H ω * ∏ i ∈ P, (1 + h i ω) ∂ν :=
        Finset.sum_le_sum fun k _ => hsup k
    _ = _ := by rw [Finset.sum_mul]

end Confinement
