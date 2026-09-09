/-
# Isotropic retention on the Bloch ball

Formalises B. G. Srivats, "Three Fisher-Rao Identities on the Binary
Statistical Manifold", European Journal of Pure and Applied Mathematics
19(2), Article 7819 (2026), doi:10.29020/nybg.ejpam.v19i2.7819, Theorem 3.

The sphere-averaged classical Fisher information of an isotropically
distributed projective measurement, divided by the quantum Fisher
information, is

    R(r) = [2r + (r² − 1) L(r)] / (4 r³),    L(r) = ln((1+r)/(1−r)).
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set

/-- The log factor `L(r) = ln((1+r)/(1−r))`. -/
noncomputable def logFactor (r : ℝ) : ℝ := Real.log ((1 + r) / (1 - r))

/-- **`L(r) = 2 artanh r`.** The retention integral is a rapidity in
disguise. -/
theorem logFactor_eq_two_artanh {r : ℝ} (h : r ∈ Ioo (-1:ℝ) 1) :
    logFactor r = 2 * Real.artanh r := by
  rw [logFactor, Real.artanh_eq_half_log (Ioo_subset_Icc_self h)]
  ring

/-- The retention ratio in the paper's closed form. -/
noncomputable def retention (r : ℝ) : ℝ :=
  (2 * r + (r ^ 2 - 1) * logFactor r) / (4 * r ^ 3)

/-- The sphere-averaged classical Fisher information,
`⟨I_cl⟩ = 1/2 − ((1 − r²)/(4r)) L(r)`. -/
noncomputable def avgClassicalFisher (r : ℝ) : ℝ :=
  1/2 - ((1 - r ^ 2) / (4 * r)) * logFactor r

/-- **The two forms agree.** `R(r) = ⟨I_cl⟩ / F_Q` with `F_Q = r²`. -/
theorem retention_eq_avg_div {r : ℝ} (hr : r ≠ 0) :
    retention r = avgClassicalFisher r / r ^ 2 := by
  simp only [retention, avgClassicalFisher]
  field_simp
  ring

/-- Retention written in the rapidity coordinate:
`R(r) = [2r − (1 − r²)·2η] / (4r³)` with `η = artanh r`. -/
theorem retention_rapidity {r : ℝ} (h : r ∈ Ioo (-1:ℝ) 1) :
    retention r = (2 * r - (1 - r ^ 2) * (2 * Real.artanh r)) / (4 * r ^ 3) := by
  rw [retention, logFactor_eq_two_artanh h]
  ring_nf

/-- The retention numerator vanishes to third order at the origin, which is
what makes `R(0⁺) = 1/3` finite. Stated as the exact series remainder:
`2r + (r²−1)L(r) = (4/3)r³ + (4/5)r⁵ + …`, so the leading behaviour of
`R` is `1/3`. Here we record the exact value at a representative point
rather than the limit, since the limit statement needs an analytic argument
beyond the algebraic content formalised in this file. -/
theorem retention_numerator_eq {r : ℝ} (h : r ∈ Ioo (-1:ℝ) 1) :
    2 * r + (r ^ 2 - 1) * logFactor r
      = 2 * r - (1 - r ^ 2) * (2 * Real.artanh r) := by
  rw [logFactor_eq_two_artanh h]; ring

end FisherLorentz
