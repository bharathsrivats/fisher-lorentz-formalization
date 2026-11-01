import Mathlib
import YMStatement.Statement

/-!
# Review experiment R1: a Gaussian-type kernel escapes the kernel-level anti-toy lemmas

`gffKernel x = (‖x‖ ^ 8 * (log ‖x‖) ^ 2)⁻¹` is, up to the constant `48 / π ^ 2`, the short-distance
form of the two-point kernel of a generalized free field with Kallen-Lehmann density
`s ^ 2 / log ^ 2 s` on `[e, ∞)` (checked numerically in the review, `compute/gff_kernel.py`).
It meets `AFProfile` with `c = 1`, and it satisfies neither hypothesis of the free-field
anti-toy lemmas `not_AFProfile_of_le_rpow` and `not_AFProfile_of_ge_pow`. So those lemmas
cannot exclude generalized free fields; only the lattice clause can.
-/

open Filter Topology

noncomputable section

namespace YMReview

open YMStatement

/-- Leading short-distance kernel of the generalized free field (normalised to `c = 1`). -/
def gffKernel (x : E4) : ℝ := (‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2)⁻¹

theorem eventually_norm_lt_one : ∀ᶠ x in 𝓝[≠] (0 : E4), ‖x‖ < 1 := by
  have h : Tendsto (fun x : E4 => ‖x‖) (𝓝[≠] (0 : E4)) (𝓝 0) := by
    have := (continuous_norm (E := E4)).tendsto (0 : E4)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact h.eventually (gt_mem_nhds one_pos)

theorem gffKernel_AFProfile : AFProfile gffKernel 1 := by
  unfold AFProfile
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_norm_lt_one, self_mem_nhdsWithin] with x hx hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : Real.log ‖x‖ ≠ 0 := (Real.log_neg hpos hx).ne
  have h8 : ‖x‖ ^ 8 ≠ 0 := pow_ne_zero 8 hpos.ne'
  have hprod : ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 ≠ 0 := mul_ne_zero h8 (pow_ne_zero 2 hlog)
  simp only [gffKernel]
  rw [mul_inv_cancel₀ hprod]

/-- The sub-AF anti-toy hypothesis fails for the GFF kernel. -/
theorem gffKernel_not_le :
    ¬ ∃ B p : ℝ, p < 8 ∧ ∀ᶠ x in 𝓝[≠] (0 : E4), |gffKernel x| ≤ B * ‖x‖ ^ (-p) := by
  rintro ⟨B, p, hp, hb⟩
  exact not_AFProfile_of_le_rpow one_ne_zero hp hb gffKernel_AFProfile

/-- The scale-invariant anti-toy hypothesis fails for the GFF kernel. -/
theorem gffKernel_not_ge :
    ¬ ∃ b : ℝ, 0 < b ∧ ∀ᶠ x in 𝓝[≠] (0 : E4), b ≤ ‖x‖ ^ 8 * gffKernel x := by
  rintro ⟨b, hb, h⟩
  exact not_AFProfile_of_ge_pow hb h gffKernel_AFProfile

end YMReview
