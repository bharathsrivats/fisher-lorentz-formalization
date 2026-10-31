/-
# Where the conformal factor comes from: the hemisphere model

The factor `4γ²` in `ds²_BK = 4 γ² ds²_Bures` is classical in substance.
Two known facts compose to give it:

* the Bures metric of a qubit is one quarter of the round metric on the upper
  hemisphere of `S³`, pulled back to the Bloch ball by the height map
  `y ↦ (y, √(1 - |y|²))` (Uhlmann 1992; Hübner 1992);
* the Beltrami-Klein metric is that same round metric divided by the squared
  height, `ds²_K = |dx|² / x₄²`: vertical projection from the Klein model to the
  hemisphere model `J` is an isometry (Cannon, Floyd, Kenyon, Parry,
  "Hyperbolic Geometry", Flavors of Geometry, MSRI Publ. 31 (1997), §7,
  pp. 70-71).

Since `x₄² = 1 - r² = 1/γ²(r)`, the ratio is `4γ²`. This module proves the
height-map derivative, both classical identities in the coordinates of
`FisherLorentz.Conformal`, and Theorem 1 again as their corollary.

A tangent vector at `y` with `|y|² = R2` enters only through `N2 = |v|²` and
`D = y · v`; in spherical coordinates `R2 = r²`, `N2 = dr² + r²(dθ² + sin²θ dφ²)`
and `D = r dr`.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import FisherLorentz.Basic
import FisherLorentz.Conformal

namespace FisherLorentz

open Real Set

/-- The round metric of the unit 3-sphere, pulled back to the open unit ball by
the height map `y ↦ (y, √(1 - |y|²))`, written through `R2 = |y|²`,
`N2 = |v|²` and `D = y · v`. -/
noncomputable def hemRound (R2 N2 D : ℝ) : ℝ := N2 + D ^ 2 / (1 - R2)

/-- The height `x₄(t) = √(1 - |y + t v|²)` moves at rate `-(y·v)/√(1 - |y|²)`
at `t = 0`. -/
theorem hasDerivAt_height (y1 y2 y3 v1 v2 v3 : ℝ)
    (hy : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 < 1) :
    HasDerivAt
      (fun t : ℝ => Real.sqrt (1 - ((y1 + t * v1) ^ 2 + (y2 + t * v2) ^ 2 + (y3 + t * v3) ^ 2)))
      (-(y1 * v1 + y2 * v2 + y3 * v3) / Real.sqrt (1 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2))) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => y1 + t * v1) v1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v1).const_add y1
  have h2 : HasDerivAt (fun t : ℝ => y2 + t * v2) v2 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v2).const_add y2
  have h3 : HasDerivAt (fun t : ℝ => y3 + t * v3) v3 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v3).const_add y3
  have hf : HasDerivAt
      (fun t : ℝ => 1 - ((y1 + t * v1) ^ 2 + (y2 + t * v2) ^ 2 + (y3 + t * v3) ^ 2))
      (-(2 * (y1 * v1 + y2 * v2 + y3 * v3))) 0 := by
    refine ((((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).const_sub 1).congr_deriv ?_
    norm_num
    ring
  have hpos : (0:ℝ) < 1 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by linarith
  have hne : (1 - ((y1 + 0 * v1) ^ 2 + (y2 + 0 * v2) ^ 2 + (y3 + 0 * v3) ^ 2)) ≠ 0 := by
    simp only [zero_mul, add_zero]; exact ne_of_gt hpos
  have hs := hf.sqrt hne
  convert hs using 1
  simp only [zero_mul, add_zero]
  have hsq : 0 < Real.sqrt (1 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) := Real.sqrt_pos.mpr hpos
  field_simp

/-- The pull-back of the round metric is `hemRound`: the flat part `|v|²`
plus the square of the height's rate of change. -/
theorem round_pullback (R2 N2 D : ℝ) (h : R2 < 1) :
    N2 + (-D / Real.sqrt (1 - R2)) ^ 2 = hemRound R2 N2 D := by
  have hpos : (0:ℝ) < 1 - R2 := by linarith
  have hsq : Real.sqrt (1 - R2) ^ 2 = 1 - R2 := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 - R2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  simp only [hemRound]
  rw [div_pow, neg_sq, hsq]

/-- **Uhlmann-Hübner, in the coordinates of `Conformal`.** The Bures metric is one
quarter of the hemisphere metric. -/
theorem buresForm_eq_quarter_hemRound {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) (θ dr dθ dφ : ℝ) :
    buresForm r θ dr dθ dφ
      = (1/4) * hemRound (r ^ 2) (dr ^ 2 + r ^ 2 * (dθ ^ 2 + Real.sin θ ^ 2 * dφ ^ 2)) (r * dr) := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [buresForm, hemRound]
  field_simp
  ring

/-- **Cannon-Floyd-Kenyon-Parry §7 (hemisphere model `J`).** The Beltrami-Klein
metric is the hemisphere metric divided by the squared height `x₄² = 1 - r²`. -/
theorem bkForm_eq_hemRound_div_height {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) (θ dr dθ dφ : ℝ) :
    bkForm r θ dr dθ dφ
      = hemRound (r ^ 2) (dr ^ 2 + r ^ 2 * (dθ ^ 2 + Real.sin θ ^ 2 * dφ ^ 2)) (r * dr)
          / (1 - r ^ 2) := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [bkForm, hemRound]
  field_simp
  ring

/-- **Theorem 1 re-derived from the two classical facts.** Dividing the
hemisphere-model identity by the Uhlmann-Hübner identity gives the factor
`4 / x₄² = 4γ²(r)`. -/
theorem bkForm_eq_four_gammaSq_mul_buresForm_via_hemisphere
    {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) (θ dr dθ dφ : ℝ) :
    bkForm r θ dr dθ dφ = 4 * gammaSq r * buresForm r θ dr dθ dφ := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  rw [bkForm_eq_hemRound_div_height hr, buresForm_eq_quarter_hemRound hr]
  simp only [gammaSq]
  field_simp

end FisherLorentz
