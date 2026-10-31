/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

A check that the definitions are the right ones. Under a gauge transformation `g`, every plaquette
holonomy and the rectangle holonomy conjugate at their base point. A path that failed to close, or
an orientation slip in `Qh`, `Qv` or `rectangle`, would break these statements.
-/
import Confinement.Lattice

namespace Confinement

variable {n L Lt : ℕ} {G : Type*} [Group G]

/-- The action of a gauge transformation on a configuration. -/
def gaugeAct (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) : Link n L Lt → G
  | Sum.inl (x, t, μ) => g (x, t) * U (Sum.inl (x, t, μ)) * (g (x + e μ, t))⁻¹
  | Sum.inr (x, t) => g (x, t) * U (Sum.inr (x, t)) * (g (x, t + 1))⁻¹

theorem Qh_gauge (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) (x t μ ν) :
    Qh (gaugeAct g U) (x, t, μ, ν) = g (x, t) * Qh U (x, t, μ, ν) * (g (x, t))⁻¹ := by
  have hcomm : x + e μ + e ν = x + e ν + e μ := by abel
  simp only [Qh, hor, gaugeAct, hcomm]
  group

theorem Qv_gauge (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) (x t μ) :
    Qv (gaugeAct g U) (x, t, μ) = g (x, t) * Qv U (x, t, μ) * (g (x, t))⁻¹ := by
  simp only [Qv, hor, ver, gaugeAct]
  group

lemma vline_gauge (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) (x t₀) (T : ℕ) :
    vline (gaugeAct g U) x t₀ T =
      g (x, t₀) * vline U x t₀ T * (g (x, t₀ + (T : ZMod Lt)))⁻¹ := by
  induction T with
  | zero => simp [vline]
  | succ T ih =>
    have hsplit : ∀ V : Link n L Lt → G, vline V x t₀ (T + 1) = vline V x t₀ T * ver V x (t₀ + (T : ZMod Lt)) := by
      intro V
      simp [vline, List.range_succ]
    rw [hsplit, hsplit, ih]
    have hcast : t₀ + ((T + 1 : ℕ) : ZMod Lt) = t₀ + (T : ZMod Lt) + 1 := by push_cast; ring
    simp only [ver, gaugeAct, hcast]
    group

lemma hline_gauge (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) (x t μ) (R : ℕ) :
    hline (gaugeAct g U) x t μ R =
      g (x, t) * hline U x t μ R * (g (x + (R : ZMod L) • e μ, t))⁻¹ := by
  induction R with
  | zero => simp [hline]
  | succ R ih =>
    have hsplit : ∀ V : Link n L Lt → G, hline V x t μ (R + 1) =
        hline V x t μ R * hor V (x + (R : ZMod L) • e μ) t μ := by
      intro V
      simp [hline, List.range_succ]
    rw [hsplit, hsplit, ih]
    have hcast : x + ((R + 1 : ℕ) : ZMod L) • (e μ : Space n L) = x + (R : ZMod L) • e μ + e μ := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    simp only [hor, gaugeAct, hcast]
    group

/-- **The rectangle closes.** Its holonomy conjugates at the corner, so its trace is gauge
invariant. -/
theorem rectangle_gauge (g : Space n L × ZMod Lt → G) (U : Link n L Lt → G) (x t₀ μ) (R T : ℕ) :
    rectangle (gaugeAct g U) x t₀ μ R T = g (x, t₀) * rectangle U x t₀ μ R T * (g (x, t₀))⁻¹ := by
  simp only [rectangle, vline_gauge, hline_gauge]
  group

end Confinement
