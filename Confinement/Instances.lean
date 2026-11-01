/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The general theorems for other gauge groups: any compact group with a continuous bounded character
that sees its centre, with `U(1)` and `ℤ₂` as worked instances. `SU(N)` is in `SpecialUnitary`.
Groups with trivial centre are excluded from the area law by its hypotheses and are covered by
`clustering_general`, which needs no centre.
-/
import Confinement.SpecialUnitary
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.Count

open MeasureTheory

namespace Confinement

section Compact

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The whole group as a positive compact set. -/
noncomputable def univCompacts : TopologicalSpace.PositiveCompacts G where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by rw [interior_univ]; exact Set.univ_nonempty

/-- The Haar probability measure of a compact group. -/
noncomputable def haarProb : Measure G := Measure.haarMeasure (univCompacts G)

instance : IsProbabilityMeasure (haarProb G) :=
  ⟨by
    have h := Measure.haarMeasure_self (K₀ := univCompacts G)
    simpa [haarProb, univCompacts] using h⟩

instance : (haarProb G).IsMulLeftInvariant := by unfold haarProb; infer_instance

variable {G}

/-- **The area law for a compact gauge group whose character sees the centre.** -/
theorem area_law_compact [SecondCountableTopology G] {n L Lt R T : ℕ} [NeZero L] [NeZero Lt]
    {χ : G → ℂ} (hχc : Continuous χ) (hχ : ∀ g, ‖χ g‖ ≤ 1) {z : G} (hz : ∀ g : G, z * g = g * z)
    {ζ : ℂ} (hζ : ζ ≠ 1) (hχz : ∀ g, χ (z * g) = ζ * χ g) (hL : 3 ≤ L) (hR : R ≤ L / 2)
    (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (J : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs (haarProb G) χ J (fun U : Link n L Lt → G => χ (rectangle U x t₀ μ R T))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ T :=
  area_law_general hχc.measurable hχ hz hζ hχz hL hR hT x t₀ μ J hq

end Compact

section U1

noncomputable instance : MeasurableSpace Circle := borel _
instance : BorelSpace Circle := ⟨rfl⟩

/-- The element `-1` of the circle. -/
noncomputable def circleMinusOne : Circle := Circle.exp Real.pi

lemma coe_circleMinusOne : ((circleMinusOne : Circle) : ℂ) = -1 := by
  simp [circleMinusOne, Circle.coe_exp, Complex.exp_pi_mul_I]

/-- **Wilson's area law for `U(1)`.** -/
theorem area_law_U1 {n L Lt R T : ℕ} [NeZero L] [NeZero Lt] (hL : 3 ≤ L) (hR : R ≤ L / 2)
    (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (J : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs (haarProb Circle) (fun g : Circle => (g : ℂ)) J
        (fun U : Link n L Lt → Circle => ((rectangle U x t₀ μ R T : Circle) : ℂ))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ T := by
  have hc : Continuous (fun g : Circle => (g : ℂ)) := continuous_subtype_val
  exact area_law_compact (G := Circle) (χ := fun g : Circle => (g : ℂ)) (z := circleMinusOne)
    (ζ := -1) hc (fun g => (Circle.norm_coe g).le) (fun g => mul_comm _ _) (by norm_num)
    (fun g => by simp [coe_circleMinusOne]) hL hR hT x t₀ μ J hq

end U1

section Z2

noncomputable instance : MeasurableSpace ℤˣ := ⊤
instance : DiscreteMeasurableSpace ℤˣ := ⟨fun _ => trivial⟩
instance : MeasurableMul₂ ℤˣ := ⟨Measurable.of_discrete⟩
instance : MeasurableInv ℤˣ := ⟨Measurable.of_discrete⟩

/-- The uniform probability measure on `ℤ₂ = {1, -1}`. -/
noncomputable def uniformZ2 : Measure ℤˣ := (2 : ENNReal)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniformZ2 :=
  ⟨by
    have h : (Measure.count (Set.univ : Set ℤˣ)) = 2 := by
      rw [Measure.count_apply MeasurableSet.univ]
      simp [Set.encard_univ, Fintype.card_units_int]
    simp only [uniformZ2, Measure.smul_apply, smul_eq_mul, h]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

instance : uniformZ2.IsMulLeftInvariant := by unfold uniformZ2; infer_instance

/-- The sign character of `ℤ₂`. -/
def signZ2 (g : ℤˣ) : ℂ := (((g : ℤˣ) : ℤ) : ℂ)

/-- **Wilson's area law for the `ℤ₂` gauge theory.** -/
theorem area_law_Z2 {n L Lt R T : ℕ} [NeZero L] [NeZero Lt] (hL : 3 ≤ L) (hR : R ≤ L / 2)
    (hT : T ≤ Lt) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (J : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs uniformZ2 signZ2 J (fun U : Link n L Lt → ℤˣ => signZ2 (rectangle U x t₀ μ R T))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ T :=
  area_law_general (χ := signZ2) (z := (-1 : ℤˣ)) (ζ := -1) Measurable.of_discrete
    (fun g => by
      rcases Int.units_eq_one_or g with rfl | rfl <;> simp [signZ2])
    (fun g => mul_comm _ _) (by norm_num)
    (fun g => by simp [signZ2]) hL hR hT x t₀ μ J hq

end Z2

end Confinement
