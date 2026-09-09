/-
# The Bures / Beltrami-Klein conformal equivalence

Formalisation of the central geometric theorem of

  B. G. Srivats, "Fisher Information as the Squared Lorentz Factor:
  Conformal Equivalence of the Bures and Beltrami-Klein Metrics on the
  Qubit Bloch Ball", Quantum Reports 8(3), 68 (2026), Theorem 1.

    ds²_BK = 4 γ²(r) · ds²_Bures      on the open Bloch ball.

The metrics are written in spherical coordinates `(r, θ, φ)` on the open
ball. A tangent vector is a triple `(dr, dθ, dφ)`. Both metrics are
encoded as the quadratic form they assign to that tangent vector, so the
theorem below is a genuine *tensor-level* statement: it holds for every
tangent vector at every point, hence as an identity of bilinear forms.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import FisherLorentz.Basic
import FisherLorentz.Gudermannian

namespace FisherLorentz

open Real Set

/-! ## The two metrics as quadratic forms -/

/-- The Bures (quantum Fisher / 2) metric at Bloch radius `r`, polar angle
`θ`, evaluated on the tangent vector `(dr, dθ, dφ)`:
`ds² = dr²/(4(1-r²)) + (r²/4)(dθ² + sin²θ dφ²)`. -/
noncomputable def buresForm (r θ dr dθ dφ : ℝ) : ℝ :=
  dr ^ 2 / (4 * (1 - r ^ 2)) + (r ^ 2 / 4) * (dθ ^ 2 + Real.sin θ ^ 2 * dφ ^ 2)

/-- The Beltrami-Klein metric at Bloch radius `r`, polar angle `θ`,
evaluated on the tangent vector `(dr, dθ, dφ)`:
`ds² = dr²/(1-r²)² + r²/(1-r²) · (dθ² + sin²θ dφ²)`. -/
noncomputable def bkForm (r θ dr dθ dφ : ℝ) : ℝ :=
  dr ^ 2 / (1 - r ^ 2) ^ 2 + (r ^ 2 / (1 - r ^ 2)) * (dθ ^ 2 + Real.sin θ ^ 2 * dφ ^ 2)

/-! ## The conformal equivalence -/

/-- **Theorem 1 (conformal equivalence), tensor level.**
On the open Bloch ball, for every point `(r, θ)` with `r ∈ (-1,1)` and every
tangent vector `(dr, dθ, dφ)`,
`ds²_BK = 4 γ²(r) · ds²_Bures`. -/
theorem bkForm_eq_four_gammaSq_mul_buresForm
    {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) (θ dr dθ dφ : ℝ) :
    bkForm r θ dr dθ dφ = 4 * gammaSq r * buresForm r θ dr dθ dφ := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [bkForm, buresForm, gammaSq]
  field_simp

/-- The radial components alone: `g^BK_rr = 4 γ² · g^Bures_rr`. -/
theorem conformal_radial {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) :
    1 / (1 - r ^ 2) ^ 2 = 4 * gammaSq r * (1 / (4 * (1 - r ^ 2))) := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [gammaSq]; field_simp

/-- The angular components alone: `g^BK_ang = 4 γ² · g^Bures_ang`.
This is the component where a factor error would hide. -/
theorem conformal_angular {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) :
    r ^ 2 / (1 - r ^ 2) = 4 * gammaSq r * (r ^ 2 / 4) := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [gammaSq]; field_simp

/-- The conformal factor is exactly `4γ²`, and no other constant works.
If `ds²_BK = c · ds²_Bures` holds for one nonzero radial vector at a point
with `r ≠ 0`, then `c = 4γ²(r)`. -/
theorem conformal_factor_unique
    {r c : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1)
    (h : bkForm r 0 1 0 0 = c * buresForm r 0 1 0 0) :
    c = 4 * gammaSq r := by
  have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hne : (1:ℝ) - r ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [bkForm, buresForm, gammaSq] at h ⊢
  field_simp at h ⊢
  nlinarith [h, hpos, sq_nonneg (1 - r ^ 2)]

/-! ## Radial distances, and the Gudermannian link -/

/-- The Bures radial arclength from the centre, `s_B(r) = (1/2) arcsin r`,
has the derivative prescribed by the Bures metric, `1 / (2 √(1-r²))`. -/
theorem hasDerivAt_buresDist {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun t => (1/2 : ℝ) * arcsin t)
      (1 / (2 * Real.sqrt (1 - r ^ 2))) r := by
  have hval : 1 / (2 * Real.sqrt (1 - r ^ 2))
      = (1/2 : ℝ) * (1 / Real.sqrt (1 - r ^ 2)) := by
    rw [mul_comm (2:ℝ), ← div_div]; ring
  rw [hval]
  exact (Real.hasDerivAt_arcsin (ne_of_gt hr.1) (ne_of_lt hr.2)).const_mul (1/2 : ℝ)

/-- `artanh` has derivative `1/(1-r²)` on the open interval, which is the
Beltrami-Klein radial speed. -/
theorem hasDerivAt_artanh {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - r ^ 2)) r := by
  have h1 : (0:ℝ) < 1 + r := by linarith [hr.1]
  have h2 : (0:ℝ) < 1 - r := by linarith [hr.2]
  have key : HasDerivAt (fun t : ℝ => (1/2 : ℝ) * (Real.log (1 + t) - Real.log (1 - t)))
      (1 / (1 - r ^ 2)) r := by
    have hA : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + r)) r := by
      simpa using ((hasDerivAt_id r).const_add 1).log (ne_of_gt h1)
    have hB : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 / (1 - r))) r := by
      have := ((hasDerivAt_id r).const_sub 1).log (ne_of_gt h2)
      simpa [div_eq_inv_mul] using this
    have hne1 : (1:ℝ) + r ≠ 0 := ne_of_gt h1
    have hne2 : (1:ℝ) - r ≠ 0 := ne_of_gt h2
    have hval : (1:ℝ) / (1 - r ^ 2) = (1/2 : ℝ) * (1 / (1 + r) - -(1 / (1 - r))) := by
      have : (1:ℝ) - r ^ 2 = (1 + r) * (1 - r) := by ring
      rw [this]; field_simp; ring
    rw [hval]
    exact (hA.sub hB).const_mul (1/2 : ℝ)
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self ht)]
  rw [Real.log_div (by linarith [ht.1]) (by linarith [ht.2])]

/-- **The Gudermannian bridge in geometric form.**
Twice the Bures radial distance is the Gudermannian of the Beltrami-Klein
radial distance: `2 s_B(r) = gd(s_BK(r))`, i.e. `arcsin r = gd(artanh r)`.
(Srivats, "Three Fisher-Rao Identities", EJPAM, Theorem 2.) -/
theorem two_buresDist_eq_gd_bkDist {r : ℝ} (hr : r ∈ Ioo (-1:ℝ) 1) :
    2 * ((1/2 : ℝ) * arcsin r) = gd (Real.artanh r) := by
  rw [← arcsin_eq_gd_artanh hr]; ring

end FisherLorentz
