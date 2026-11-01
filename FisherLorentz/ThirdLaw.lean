/-
# The cooling-cost divergence

Cooling to ground-state fidelity `F = 1 − ε` places the state at Bloch
radius `r = 1 − 2ε`. The Beltrami-Klein radial distance from the centre
diverges as `ε → 0`, while the Bures radial distance stays bounded by `π/4`.
The first distance is the rapidity, half the required gap in units of `kT`,
and the second is half the thermodynamic length. See `StepEquilibration`
for the entropy produced.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set

/-- Beltrami-Klein radial distance from the centre to radius `r`. -/
noncomputable def bkDist (r : ℝ) : ℝ := Real.artanh r

/-- Bures radial distance from the centre to radius `r`. -/
noncomputable def buresDist (r : ℝ) : ℝ := (1/2 : ℝ) * Real.arcsin r

/-- **The Bures distance is bounded by `π/4`, uniformly.**
The pure state is at finite Bures distance. -/
theorem buresDist_le_pi_div_four (r : ℝ) : buresDist r ≤ Real.pi / 4 := by
  have h := Real.arcsin_le_pi_div_two r
  simp only [buresDist]
  linarith

/-- The bound is attained in the limit: `s_B(1) = π/4`. -/
@[simp] theorem buresDist_one : buresDist 1 = Real.pi / 4 := by
  simp [buresDist, Real.arcsin_one]; ring

/-- **The Beltrami-Klein cooling cost, in closed form.**
At fidelity `F = 1 − ε`, i.e. `r = 1 − 2ε`,
`L_BK(ε) = (1/2) log((1 − ε)/ε)`. -/
theorem bkDist_cooling {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1/2) :
    bkDist (1 - 2*ε) = (1/2 : ℝ) * Real.log ((1 - ε) / ε) := by
  have hmem : (1 - 2*ε) ∈ Icc (-1:ℝ) 1 := by constructor <;> linarith
  rw [bkDist, Real.artanh_eq_half_log hmem]
  congr 2
  have hne : (2:ℝ) * ε ≠ 0 := by positivity
  field_simp
  ring

/-- **The divergence, with an explicit witness.**
For any target `M`, taking `ε = 1/(2 + e^{2M})` gives a Beltrami-Klein
cooling cost of at least `M`. The cost is therefore unbounded. -/
theorem bkDist_cooling_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ M ≤ bkDist (1 - 2*ε) := by
  set E := Real.exp (2*M) with hE
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨1 / (2 + E), by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  · have h0 : (0:ℝ) < 1 / (2 + E) := by positivity
    have h1 : 1 / (2 + E) < 1/2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    rw [bkDist_cooling h0 h1]
    have hden : (0:ℝ) < 1 / (2 + E) := h0
    have hratio : (1 - 1/(2+E)) / (1/(2+E)) = 1 + E := by
      field_simp; ring
    rw [hratio]
    have hlog : 2*M ≤ Real.log (1 + E) := by
      have : Real.log E ≤ Real.log (1 + E) :=
        Real.log_le_log hEpos (by linarith)
      simpa [hE, Real.log_exp] using this
    linarith

/-- **The contrast, in one statement.**
The Bures cooling distance is bounded by `π/4` for every `ε`, while the
Beltrami-Klein cooling distance is unbounded. The pure state lies at finite
statistical distance and infinite thermodynamic distance. -/
theorem cooling_cost_contrast (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧
      M ≤ bkDist (1 - 2*ε) ∧ buresDist (1 - 2*ε) ≤ Real.pi / 4 := by
  obtain ⟨ε, h0, h1, hM⟩ := bkDist_cooling_unbounded M
  exact ⟨ε, h0, h1, hM, buresDist_le_pi_div_four _⟩

/-- **Halving the residual costs a fixed increment.**
`L_BK(ε) − L_BK(2ε) = (1/2) log( ε(1−ε) / (2ε(1−2ε)) )`, which tends to
`(1/2) log 2` as `ε → 0`. Stated here as the exact algebraic identity. -/
theorem bkDist_halving {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1/4) :
    bkDist (1 - 2*ε) - bkDist (1 - 2*(2*ε))
      = (1/2 : ℝ) * Real.log (((1 - ε) / ε) / ((1 - 2*ε) / (2*ε))) := by
  have hA : (0:ℝ) < (1 - ε) / ε := by
    apply div_pos <;> linarith
  have hB : (0:ℝ) < (1 - 2*ε) / (2*ε) := by
    apply div_pos <;> linarith
  rw [bkDist_cooling h0 (by linarith), bkDist_cooling (by linarith) (by linarith),
      Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
  ring

end FisherLorentz
