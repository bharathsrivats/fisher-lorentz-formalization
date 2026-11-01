/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

`SU(N)` as a gauge group: compactness, its Haar probability measure, the normalised trace, and
the central element `exp (2 π i / N) · 1`.
-/
import Confinement.Clustering
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary

open MeasureTheory Matrix

namespace Confinement

variable (N : ℕ)

/-- The special unitary group. -/
abbrev SU := Matrix.specialUnitaryGroup (Fin N) ℂ

instance : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

instance : SecondCountableTopology (SU N) :=
  Topology.IsInducing.secondCountableTopology (f := Subtype.val) ⟨rfl⟩

instance : IsTopologicalGroup (SU N) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.star

instance : CompactSpace (SU N) := by
  have hclosed : IsClosed ((Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
    have h1 : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      isClosed_unitary
    have h2 : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
      isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    have : ((Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)))
        = {A | A ∈ Matrix.unitaryGroup (Fin N) ℂ} ∩ {A | A.det = 1} := by
      ext A; simp [Matrix.mem_specialUnitaryGroup_iff]
    rw [this]; exact h1.inter h2
  have hsub : ((Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)))
      ⊆ (Metric.closedBall (0 : ℂ) 1).matrix := by
    intro A hA i j
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact entry_norm_bound_of_unitary ((Matrix.mem_specialUnitaryGroup_iff.mp hA).1) i j
  exact isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 1).matrix hclosed hsub)

noncomputable instance : MeasurableSpace (SU N) := borel _
instance : BorelSpace (SU N) := ⟨rfl⟩

/-- The whole group as a positive compact set. -/
noncomputable def suUniv : TopologicalSpace.PositiveCompacts (SU N) where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by rw [interior_univ]; exact Set.univ_nonempty

/-- The Haar probability measure of `SU(N)`. -/
noncomputable def haarSU : Measure (SU N) := Measure.haarMeasure (suUniv N)

instance : IsProbabilityMeasure (haarSU N) :=
  ⟨by
    have h := Measure.haarMeasure_self (K₀ := suUniv N)
    simpa [haarSU, suUniv] using h⟩

instance : (haarSU N).IsMulLeftInvariant := by unfold haarSU; infer_instance

variable {N}

/-- The normalised trace `Tr / N`. -/
noncomputable def normTr (g : SU N) : ℂ := Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ) / N

lemma normTr_le (hN : 0 < N) (g : SU N) : ‖normTr g‖ ≤ 1 := by
  have hb : ‖Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)‖ ≤ N := by
    unfold Matrix.trace
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ (Finset.univ : Finset (Fin N)), ‖Matrix.diag (g : Matrix (Fin N) (Fin N) ℂ) i‖ ≤ 1 :=
      fun i _ => entry_norm_bound_of_unitary ((Matrix.mem_specialUnitaryGroup_iff.mp g.2).1) i i
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [normTr, norm_div, Complex.norm_natCast]
  exact (div_le_one hN').mpr hb

lemma measurable_normTr : Measurable (normTr : SU N → ℂ) := by
  refine Continuous.measurable ?_
  unfold normTr
  exact (Continuous.matrix_trace continuous_subtype_val).div_const _

/-- The root of unity `exp (2 π i / N)`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma omega_ne_one (hN : 2 ≤ N) : omega N ≠ 1 :=
  (Complex.isPrimitiveRoot_exp N (by omega)).ne_one (by omega)

lemma omega_pow (hN : 2 ≤ N) : omega N ^ N = 1 :=
  (Complex.isPrimitiveRoot_exp N (by omega)).pow_eq_one

/-- The central element `ω · 1` of `SU(N)`. -/
noncomputable def centre (hN : 2 ≤ N) : SU N :=
  ⟨omega N • (1 : Matrix (Fin N) (Fin N) ℂ), by
    have hnorm : omega N * star (omega N) = 1 := by
      have h : ‖omega N‖ = 1 := (Complex.isPrimitiveRoot_exp N (by omega)).norm'_eq_one (by omega)
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one, hnorm,
        one_smul]
    · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      exact omega_pow hN⟩

lemma coe_centre (hN : 2 ≤ N) :
    ((centre hN : SU N) : Matrix (Fin N) (Fin N) ℂ) = omega N • 1 := rfl

lemma centre_comm (hN : 2 ≤ N) (g : SU N) : centre hN * g = g * centre hN := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, coe_centre, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

lemma normTr_centre_mul (hN : 2 ≤ N) (g : SU N) : normTr (centre hN * g) = omega N * normTr g := by
  simp only [normTr, Submonoid.coe_mul, coe_centre, smul_mul_assoc, one_mul, Matrix.trace_smul,
    smul_eq_mul]
  ring

/-- **Wilson's area law for `SU(N)`, every `N ≥ 2`, in every spacetime dimension `n + 1 ≥ 2`.**
The weight is `exp (β_W ∑ₚ Re Tr Qₚ / N)`, on the torus `(ℤ/L)ⁿ × ℤ/Lₜ`, `L ≥ 3`. With
`p = 1 - exp (-2 |β_W|)` and `2 n p < 1`, the `R × T` rectangle, `R ≤ L / 2`, `T ≤ Lₜ`, satisfies
`‖⟨Tr Q_ℓ / N⟩‖ ≤ ((2 n p) ^ R / (1 - 2 n p)) ^ T`. -/
theorem area_law_SU {n L Lt R T : ℕ} [NeZero L] [NeZero Lt] (hN : 2 ≤ N) (hL : 3 ≤ L)
    (hR : R ≤ L / 2) (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (βW : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))) < 1) :
    ‖gibbs (haarSU N) normTr βW
        (fun U : Link n L Lt → SU N => normTr (rectangle U x t₀ μ R T))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))))) ^ T :=
  area_law_general measurable_normTr (normTr_le (by omega)) (centre_comm hN) (omega_ne_one hN)
    (normTr_centre_mul hN) hL hR hT x t₀ μ βW hq

/-- **Polyakov loop correlators for `SU(N)`, every temporal extent.** -/
theorem polyakov_SU {n L Lt R : ℕ} [NeZero L] [NeZero Lt] (hN : 2 ≤ N) (hL : 3 ≤ L)
    (hR : R ≤ L / 2) (x : Space n L) (μ : Fin n) (βW : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))) < 1) :
    ‖gibbs (haarSU N) normTr βW
        (fun U : Link n L Lt → SU N => normTr (polyakov U x) *
          (starRingEnd ℂ) (normTr (polyakov U (x + (R : ZMod L) • (e μ : Space n L)))))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))))) ^ Lt :=
  polyakov_general measurable_normTr (normTr_le (by omega)) (centre_comm hN) (omega_ne_one hN)
    (normTr_centre_mul hN) hL hR x μ βW hq

/-- The same bound in the closed window `4 n |β_W| < 1`, that is `|β_W| < 1 / (4 (d - 1))`. -/
theorem area_law_SU_window {n L Lt R T : ℕ} [NeZero L] [NeZero Lt] (hN : 2 ≤ N) (hL : 3 ≤ L)
    (hR : R ≤ L / 2) (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (βW : ℝ)
    (hq : 4 * (n : ℝ) * |βW| < 1) :
    ‖gibbs (haarSU N) normTr βW
        (fun U : Link n L Lt → SU N => normTr (rectangle U x t₀ μ R T))‖
      ≤ ((4 * (n : ℝ) * |βW|) ^ R / (1 - 4 * (n : ℝ) * |βW|)) ^ T := by
  have hp : 1 - Real.exp (-(2 * |βW|)) ≤ 2 * |βW| := by
    have := Real.add_one_le_exp (-(2 * |βW|))
    linarith
  have hp0 : 0 ≤ 1 - Real.exp (-(2 * |βW|)) := by
    have : Real.exp (-(2 * |βW|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg βW])
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))) ≤ 4 * (n : ℝ) * |βW| := by nlinarith
  have h20 : 0 ≤ 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))) := by positivity
  refine (area_law_SU hN hL hR hT x t₀ μ βW (h2.trans_lt hq)).trans ?_
  have hd : 0 < 1 - 4 * (n : ℝ) * |βW| := by linarith
  refine pow_le_pow_left₀ (by have : 0 < 1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |βW|))) := by linarith
                              positivity) ?_ T
  exact div_le_div₀ (by positivity) (pow_le_pow_left₀ h20 h2 R) hd (by linarith)

/-- **The area law as an exponential of the area.** For `0 < 4 n |β_W| < 1` the string tension is
at least `σ = -log (4 n |β_W|) > 0`: `‖⟨Tr Q_ℓ / N⟩‖ ≤ exp (-σ R T + κ T)`, with
`κ = -log (1 - 4 n |β_W|) ≥ 0` a perimeter term. -/
theorem area_law_SU_exp {n L Lt R T : ℕ} [NeZero L] [NeZero Lt] (hN : 2 ≤ N) (hL : 3 ≤ L)
    (hR : R ≤ L / 2) (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (βW : ℝ)
    (h0 : 0 < 4 * (n : ℝ) * |βW|) (hq : 4 * (n : ℝ) * |βW| < 1) :
    ‖gibbs (haarSU N) normTr βW
        (fun U : Link n L Lt → SU N => normTr (rectangle U x t₀ μ R T))‖
      ≤ Real.exp (Real.log (4 * (n : ℝ) * |βW|) * ((R : ℝ) * T) -
          Real.log (1 - 4 * (n : ℝ) * |βW|) * T) := by
  refine (area_law_SU_window hN hL hR hT x t₀ μ βW hq).trans (le_of_eq ?_)
  have hd : 0 < 1 - 4 * (n : ℝ) * |βW| := by linarith
  rw [Real.exp_sub, Real.exp_mul, Real.exp_log h0, Real.exp_mul, Real.exp_log hd,
    Real.rpow_mul h0.le, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, ← div_pow]

/-- The partition function is positive, so the Gibbs expectation in `area_law_SU` is a genuine
expectation and the theorem is not vacuous. -/
theorem partition_pos {n L Lt : ℕ} [NeZero L] [NeZero Lt] (N : ℕ) (hN : 0 < N) (βW : ℝ) :
    0 < ∫ U : Link n L Lt → SU N, wilsonWeight normTr βW U ∂(linkMeasure (haarSU N)) := by
  have hm : Measurable (wilsonWeight normTr βW : (Link n L Lt → SU N) → ℝ) := by
    unfold wilsonWeight
    exact (((measurable_actionH measurable_normTr).add (measurable_actionV measurable_normTr)).const_mul
      βW).exp
  have hbd : ∀ U : Link n L Lt → SU N,
      |βW * (actionH normTr U + actionV normTr U)| ≤
        |βW| * (((Finset.univ : Finset (HP n L Lt)).filter
          (fun p => p.2.2.1 < p.2.2.2)).card + (Finset.univ : Finset (VP n L Lt)).card) := by
    intro U
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
    · unfold actionH
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ))
        fun q _ => abs_le.mpr (re_bounds (normTr_le hN) (Qh U q))).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · unfold actionV
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ))
        fun q _ => abs_le.mpr (re_bounds (normTr_le hN) (Qv U q))).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  set B : ℝ := |βW| * (((Finset.univ : Finset (HP n L Lt)).filter
    (fun p => p.2.2.1 < p.2.2.2)).card + (Finset.univ : Finset (VP n L Lt)).card) with hB
  have hint : Integrable (wilsonWeight normTr βW : (Link n L Lt → SU N) → ℝ)
      (linkMeasure (haarSU N)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp B)
      (Filter.Eventually.of_forall fun U => ?_)
    simp only [wilsonWeight]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbd U))
  have hlow : ∫ _U : Link n L Lt → SU N, Real.exp (-B) ∂(linkMeasure (haarSU N))
      ≤ ∫ U : Link n L Lt → SU N, wilsonWeight normTr βW U ∂(linkMeasure (haarSU N)) := by
    refine integral_mono (integrable_const _) hint fun U => ?_
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hbd U)).1])
  have hconst : ∫ _U : Link n L Lt → SU N, Real.exp (-B) ∂(linkMeasure (haarSU N)) = Real.exp (-B) := by
    simp
  linarith [Real.exp_pos (-B)]

/-- **Exponential clustering in Euclidean time for `SU(N)`, every `N ≥ 1`, in the closed window
`q = 16 (2 n - 1) |β_W| < 1`.** For observables bounded by one, depending on the links of `X` and
`Y` at time distance at least `D ≥ 1`, the connected correlation is at most
`2 (2 n |X|) (2 n |Y|) q ^ (D - 2) / (1 - q)`, uniformly in the size of the torus. -/
theorem clustering_SU {n L Lt : ℕ} [NeZero L] [NeZero Lt] (hN : 0 < N)
    (f g : (Link n L Lt → SU N) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf1 : ∀ U, ‖f U‖ ≤ 1) (hg1 : ∀ U, ‖g U‖ ≤ 1)
    (X Y : Finset (Link n L Lt))
    (hfX : ∀ U V : Link n L Lt → SU N, (∀ l ∈ X, U l = V l) → f U = f V)
    (hgY : ∀ U V : Link n L Lt → SU N, (∀ l ∈ Y, U l = V l) → g U = g V)
    {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ∀ x ∈ X, ∀ y ∈ Y, D ≤ (linkTime y - linkTime x).valMinAbs.natAbs)
    (βW : ℝ) (hq : ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|) < 1) :
    ‖gibbs (haarSU N) normTr βW (fun U => f U * g U)
        - gibbs (haarSU N) normTr βW f * gibbs (haarSU N) normTr βW g‖
      ≤ 2 * (((X.card * (2 * n) : ℕ) : ℝ) * ((Y.card * (2 * n) : ℕ) : ℝ)) *
        ((((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|)) ^ (D - 2) /
          (1 - ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|))) := by
  set Δ : ℝ := ((4 * (2 * n - 1) : ℕ) : ℝ) with hΔ
  have hΔ0 : 0 ≤ Δ := Nat.cast_nonneg _
  set p : ℝ := 1 - Real.exp (-(4 * |βW|)) with hp
  have hp0 : 0 ≤ p := by
    have : Real.exp (-(4 * |βW|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg βW])
    linarith
  have hp1 : p ≤ 1 := by linarith [Real.exp_pos (-(4 * |βW|))]
  have hp4 : p ≤ 4 * |βW| := by
    have := Real.add_one_le_exp (-(4 * |βW|))
    linarith
  have hle : Δ * p ≤ Δ * (4 * |βW|) := mul_le_mul_of_nonneg_left hp4 hΔ0
  have hle0 : 0 ≤ Δ * p := mul_nonneg hΔ0 hp0
  have hq' : Δ * p < 1 := hle.trans_lt hq
  refine (clustering_general (haarSU N) measurable_normTr (normTr_le hN) f g hfm hgm hf1 hg1 X Y
    hfX hgY hD1 hD βW hq').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hd : 0 < 1 - Δ * (4 * |βW|) := by linarith
  have hd' : 0 < 1 - Δ * p := by linarith
  have h1 : (Δ * p) ^ (D - 2) / (1 - Δ * p) ≤ (Δ * (4 * |βW|)) ^ (D - 2) / (1 - Δ * (4 * |βW|)) :=
    div_le_div₀ (pow_nonneg (hle0.trans hle) _) (pow_le_pow_left₀ hle0 hle _) hd (by linarith)
  have h2 : 0 ≤ (Δ * p) ^ (D - 2) / (1 - Δ * p) := div_nonneg (pow_nonneg hle0 _) hd'.le
  nlinarith

/-- **A mass gap in lattice units for `SU(N)`.** The connected correlation of two plaquettes at time
distance at least `D` decays exponentially in `D`, with rate at least `m = -log q`,
`q = 16 (2 n - 1) |β_W|`, uniformly in `N` and in the size of the torus. -/
theorem mass_gap_plaquette_SU {n L Lt : ℕ} [NeZero L] [NeZero Lt] (hN : 0 < N)
    (a b : Plaq n L Lt) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ∀ x ∈ links a, ∀ y ∈ links b, D ≤ (linkTime y - linkTime x).valMinAbs.natAbs)
    (βW : ℝ) (h0 : 0 < ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|))
    (hq : ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|) < 1) :
    ‖gibbs (haarSU N) normTr βW
          (fun U : Link n L Lt → SU N => normTr (hol U a) * normTr (hol U b))
        - gibbs (haarSU N) normTr βW (fun U : Link n L Lt → SU N => normTr (hol U a))
          * gibbs (haarSU N) normTr βW (fun U : Link n L Lt → SU N => normTr (hol U b))‖
      ≤ (2 * (((4 * (2 * n) : ℕ) : ℝ) * ((4 * (2 * n) : ℕ) : ℝ)) /
            (1 - ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|))) *
          Real.exp (((D - 2 : ℕ) : ℝ) * Real.log (((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|))) := by
  set q : ℝ := ((4 * (2 * n - 1) : ℕ) : ℝ) * (4 * |βW|) with hqdef
  have hmain := clustering_SU hN (fun U : Link n L Lt → SU N => normTr (hol U a))
    (fun U => normTr (hol U b)) (measurable_normTr.comp (measurable_hol a))
    (measurable_normTr.comp (measurable_hol b)) (fun _ => normTr_le hN _) (fun _ => normTr_le hN _)
    (links a) (links b) (fun U V h => congrArg _ (hol_congr a h))
    (fun U V h => congrArg _ (hol_congr b h)) hD1 hD βW hq
  refine hmain.trans ?_
  have hd : 0 < 1 - q := by linarith
  have hexp : Real.exp (((D - 2 : ℕ) : ℝ) * Real.log q) = q ^ (D - 2) := by
    rw [Real.exp_nat_mul, Real.exp_log h0]
  rw [hexp]
  have hca : (((links a).card * (2 * n) : ℕ) : ℝ) ≤ ((4 * (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right _ (card_links_le a)
  have hcb : (((links b).card * (2 * n) : ℕ) : ℝ) ≤ ((4 * (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right _ (card_links_le b)
  have hqp : 0 ≤ q ^ (D - 2) / (1 - q) := div_nonneg (pow_nonneg h0.le _) hd.le
  have hprod : (((links a).card * (2 * n) : ℕ) : ℝ) * (((links b).card * (2 * n) : ℕ) : ℝ)
      ≤ ((4 * (2 * n) : ℕ) : ℝ) * ((4 * (2 * n) : ℕ) : ℝ) :=
    mul_le_mul hca hcb (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc _ ≤ 2 * (((4 * (2 * n) : ℕ) : ℝ) * ((4 * (2 * n) : ℕ) : ℝ)) * (q ^ (D - 2) / (1 - q)) :=
        mul_le_mul_of_nonneg_right (by linarith) hqp
    _ = _ := by ring

end Confinement
