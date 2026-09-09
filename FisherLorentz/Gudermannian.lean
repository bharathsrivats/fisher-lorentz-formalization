/-
# The Gudermannian bridge

Formalisation of the identity from
  B. G. Srivats, "Three Fisher-Rao Identities", EJPAM (accepted):

    arcsin V = gd (artanh V),     V ∈ (-1,1)

with `gd x = 2 arctan (tanh (x/2))`. The mathematical content is the
equivalence of the two standard definitions of the Gudermannian,
`2 arctan (tanh (x/2)) = arcsin (tanh x)`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic

namespace FisherLorentz

open Real Set

/-- The Gudermannian function, `gd x = 2 arctan (tanh (x/2))`. -/
noncomputable def gd (x : ℝ) : ℝ := 2 * arctan (tanh (x / 2))

/-- Double-angle for `tanh`: `tanh (2y) = 2 tanh y / (1 + tanh²y)`. -/
lemma tanh_two_mul (y : ℝ) :
    tanh (2 * y) = 2 * tanh y / (1 + tanh y ^ 2) := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hpy : Real.cosh y ^ 2 - Real.sinh y ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq y
  have hden : Real.cosh y ^ 2 + Real.sinh y ^ 2 ≠ 0 := by
    nlinarith [Real.cosh_pos y, sq_nonneg (Real.sinh y)]
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp

/-- Double-angle, in the form used below. -/
lemma tanh_eq_double (x : ℝ) :
    tanh x = 2 * tanh (x / 2) / (1 + tanh (x / 2) ^ 2) := by
  have h := tanh_two_mul (x / 2)
  rwa [show 2 * (x / 2) = x by ring] at h

/-- `sin (2 arctan t) = 2t/(1+t²)`. -/
lemma sin_two_arctan (t : ℝ) : sin (2 * arctan t) = 2 * t / (1 + t ^ 2) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hsq : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
  have hs : √(1 + t ^ 2) ≠ 0 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, mul_assoc,
      div_mul_div_comm, Real.mul_self_sqrt hpos.le]
  ring

/-- `2 arctan (tanh (x/2))` lies in `[-π/2, π/2]`. -/
lemma gd_mem_Icc (x : ℝ) : gd x ∈ Icc (-(π/2)) (π/2) := by
  have h := Real.abs_tanh_lt_one (x/2)
  rw [abs_lt] at h
  have hlt : arctan (tanh (x/2)) < π/4 := by
    have : arctan (tanh (x/2)) < arctan 1 := Real.arctan_lt_arctan_iff.mpr h.2
    simpa [Real.arctan_one] using this
  have hgt : -(π/4) < arctan (tanh (x/2)) := by
    have : arctan (-1 : ℝ) < arctan (tanh (x/2)) := Real.arctan_lt_arctan_iff.mpr h.1
    rw [show (-1:ℝ) = -(1:ℝ) by norm_num, Real.arctan_neg, Real.arctan_one] at this
    linarith
  unfold gd
  constructor <;> linarith

/-- **The two definitions of the Gudermannian agree:**
`2 arctan (tanh (x/2)) = arcsin (tanh x)`. -/
theorem gd_eq_arcsin_tanh (x : ℝ) : gd x = arcsin (tanh x) := by
  have hr := gd_mem_Icc x
  rw [tanh_eq_double x, ← sin_two_arctan (tanh (x/2))]
  exact (Real.arcsin_sin hr.1 hr.2).symm

/-- **The Gudermannian bridge.** For `V ∈ (-1,1)`, `arcsin V = gd (artanh V)`. -/
theorem arcsin_eq_gd_artanh {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    arcsin V = gd (artanh V) := by
  rw [gd_eq_arcsin_tanh, Real.tanh_artanh h]

end FisherLorentz
