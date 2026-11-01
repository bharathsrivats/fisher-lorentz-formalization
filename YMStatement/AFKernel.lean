import Mathlib

/-!
# Short-distance (asymptotic freedom) profile and three kernel-level anti-toy lemmas

Clay (Jaffe-Witten, section 4, clay_ym.txt lines 267-271) asks that correlation functions match
asymptotic freedom and perturbative renormalization at short distances. For the renormalised Lagrangian density `Tr F²` (dimension 4) the leading-log
prediction for the connected two-point kernel is `K(x) ~ c / (‖x‖⁸ (log ‖x‖)²)`, `c > 0`.

Derivation chain (sound inference, not a literature quotation): the trace-anomaly combination
`(β(g)/g) F²` is renormalisation-group invariant; its tree-level two-point function is
`∝ dim G / ‖x‖⁸`; evaluating at the running coupling `ḡ²(1/‖x‖) ≈ 1/(2 b₀ log(1/‖x‖))` and using
`β(g)/g ≈ -b₀ g²` gives `(b₀ ḡ²)² ≈ 1/(4 (log ‖x‖)²)`, with `b₀` cancelling. Any fixed
normalisation of the field changes only `c`.
-/

open Filter Topology

noncomputable section

namespace YMStatement

section Profile

variable {E : Type*} [NormedAddCommGroup E]

/-- Leading-log short-distance profile predicted by asymptotic freedom:
`‖x‖⁸ (log ‖x‖)² K x → c` as `x → 0`, `x ≠ 0`. -/
def AFProfile (K : E → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun x : E => ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 * K x) (𝓝[≠] (0 : E)) (𝓝 c)

theorem tendsto_rpow_mul_log_sq_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => r ^ a * (Real.log r) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := a / 2) (by positivity)
  have h2 : Tendsto (fun r : ℝ => (Real.log r * r ^ (a / 2)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using h.pow 2
  refine Tendsto.congr' ?_ h2
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hsq : (r ^ (a / 2)) ^ 2 = r ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr'.le]
    norm_num
  calc (Real.log r * r ^ (a / 2)) ^ 2 = (r ^ (a / 2)) ^ 2 * (Real.log r) ^ 2 := by ring
    _ = r ^ a * (Real.log r) ^ 2 := by rw [hsq]

theorem tendsto_log_norm_sq_atTop [NormedSpace ℝ E] :
    Tendsto (fun x : E => (Real.log ‖x‖) ^ 2) (𝓝[≠] (0 : E)) atTop := by
  have hlog : Tendsto (fun x : E => Real.log ‖x‖) (𝓝[≠] (0 : E)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero
  have hneg : Tendsto (fun x : E => -Real.log ‖x‖) (𝓝[≠] (0 : E)) atTop :=
    tendsto_neg_atBot_atTop.comp hlog
  have hsq := (tendsto_pow_atTop (two_ne_zero)).comp hneg
  refine hsq.congr' (Eventually.of_forall fun x => ?_)
  simp [Function.comp, neg_sq]

/-- **Anti-toy (sub-AF singularities).** A kernel bounded by `B ‖x‖^{-p}` with `p < 8` near the
origin (free field `p = 2`, Wick square `p = 4`) has profile tending to `0`, so it cannot have
the AF profile with `c ≠ 0`. -/
theorem not_AFProfile_of_le_rpow [NormedSpace ℝ E] [Nontrivial E] {K : E → ℝ} {c B p : ℝ}
    (hc : c ≠ 0) (hp : p < 8)
    (hK : ∀ᶠ x in 𝓝[≠] (0 : E), |K x| ≤ B * ‖x‖ ^ (-p)) : ¬ AFProfile K c := by
  intro hAF
  have hbound : Tendsto (fun x : E => B * (‖x‖ ^ (8 - p) * (Real.log ‖x‖) ^ 2))
      (𝓝[≠] (0 : E)) (𝓝 0) := by
    have := (tendsto_rpow_mul_log_sq_nhdsGT (a := 8 - p) (by linarith)).comp
      (tendsto_norm_nhdsNE_zero (E := E))
    simpa using this.const_mul B
  have hzero : Tendsto (fun x : E => ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 * K x)
      (𝓝[≠] (0 : E)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hK, self_mem_nhdsWithin] with x hx hx0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have h8 : (‖x‖ : ℝ) ^ (8 : ℕ) = ‖x‖ ^ (8 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    have hsplit : ‖x‖ ^ (8 : ℝ) * ‖x‖ ^ (-p) = ‖x‖ ^ (8 - p) := by
      rw [← Real.rpow_add hxpos]; ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have e1 : |‖x‖ ^ 8| = ‖x‖ ^ 8 := abs_of_nonneg (by positivity)
    have e2 : |(Real.log ‖x‖) ^ 2| = (Real.log ‖x‖) ^ 2 := abs_of_nonneg (by positivity)
    rw [e1, e2]
    calc ‖x‖ ^ 8 * Real.log ‖x‖ ^ 2 * |K x|
        ≤ ‖x‖ ^ 8 * Real.log ‖x‖ ^ 2 * (B * ‖x‖ ^ (-p)) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = B * ((‖x‖ ^ (8 : ℝ) * ‖x‖ ^ (-p)) * Real.log ‖x‖ ^ 2) := by rw [h8]; ring
      _ = B * (‖x‖ ^ (8 - p) * Real.log ‖x‖ ^ 2) := by rw [hsplit]
  exact hc (tendsto_nhds_unique hAF hzero)

/-- **Anti-toy (conformal / free-like singularities).** A kernel with `‖x‖⁸ K x ≥ b > 0` near the
origin (Wick fourth power of a free field, free Maxwell `Tr F²`) has profile tending to `+∞`,
so it cannot have any finite AF profile. -/
theorem not_AFProfile_of_ge_pow [NormedSpace ℝ E] [Nontrivial E] {K : E → ℝ} {c b : ℝ}
    (hb : 0 < b) (hK : ∀ᶠ x in 𝓝[≠] (0 : E), b ≤ ‖x‖ ^ 8 * K x) : ¬ AFProfile K c := by
  intro hAF
  have htop : Tendsto (fun x : E => b * (Real.log ‖x‖) ^ 2) (𝓝[≠] (0 : E)) atTop :=
    (tendsto_log_norm_sq_atTop (E := E)).const_mul_atTop hb
  have h1 : ∀ᶠ x in 𝓝[≠] (0 : E), c + 1 ≤ b * (Real.log ‖x‖) ^ 2 :=
    htop.eventually_ge_atTop (c + 1)
  have h2 : ∀ᶠ x in 𝓝[≠] (0 : E), ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 * K x < c + 1 :=
    hAF.eventually (gt_mem_nhds (by linarith))
  obtain ⟨x, hx1, hx2, hx3⟩ := (h1.and (h2.and hK)).exists
  have hsq : 0 ≤ (Real.log ‖x‖) ^ 2 := by positivity
  have : b * (Real.log ‖x‖) ^ 2 ≤ ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 * K x := by
    calc b * (Real.log ‖x‖) ^ 2 ≤ (‖x‖ ^ 8 * K x) * (Real.log ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hx3 hsq
      _ = ‖x‖ ^ 8 * (Real.log ‖x‖) ^ 2 * K x := by ring
  linarith

end Profile

/-- **Anti-toy (bounded Hamiltonian), kernel-level core.** If `H` is bounded, `‖H‖ ≤ M`, the
spectral theorem gives `⟨ψ, e^{-(t+s)H} ψ⟩ ≥ e^{-Ms} ⟨ψ, e^{-tH} ψ⟩`; on the Euclidean time
axis this reads `k (r + s) ≥ e^{-Ms} k r` for the two-point profile `k`. No profile with the AF
behaviour `r⁸ (log r)² k r → c > 0` satisfies this, because the AF profile forces
`k (2r) / k r → 2⁻⁸`. (The reduction from operators to the kernel inequality uses the spectral
theorem and approximate identities; it is documented, not formalised, here.) -/
theorem not_bounded_generator_of_AFProfile {k : ℝ → ℝ} {c M r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (hAF : Tendsto (fun r : ℝ => r ^ 8 * (Real.log r) ^ 2 * k r) (𝓝[>] 0) (𝓝 c))
    (hbd : ∀ r s : ℝ, 0 < r → 0 ≤ s → r + s < r₀ → Real.exp (-M * s) * k r ≤ k (r + s)) :
    False := by
  set φ : ℝ → ℝ := fun r => r ^ 8 * (Real.log r) ^ 2 * k r with hφ
  have h2r : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos two_pos (Set.mem_Ioi.1 hr)
  have hφ2 : Tendsto (fun r : ℝ => φ (2 * r)) (𝓝[>] 0) (𝓝 c) := hAF.comp h2r
  have hlog : Tendsto Real.log (𝓝[>] (0 : ℝ)) atBot := Real.tendsto_log_nhdsGT_zero
  have hratio : Tendsto (fun r : ℝ => Real.log (2 * r) / Real.log r) (𝓝[>] 0) (𝓝 1) := by
    have hdiv : Tendsto (fun r : ℝ => Real.log 2 / Real.log r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atBot hlog
    have hsum : Tendsto (fun r : ℝ => 1 + Real.log 2 / Real.log r) (𝓝[>] 0) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hdiv
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log r < 0 := hlog.eventually_lt_atBot 0
    filter_upwards [hlt, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    rw [Real.log_mul two_ne_zero hr0'.ne']
    field_simp [hr.ne]
    ring
  have hexp : Tendsto (fun r : ℝ => Real.exp (-M * r)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => Real.exp (-M * r)) (𝓝 0) (𝓝 (Real.exp (-M * 0))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hrhs : Tendsto (fun r : ℝ => 256 * Real.exp (-M * r) *
      (Real.log (2 * r) / Real.log r) ^ 2 * φ r) (𝓝[>] 0) (𝓝 (256 * 1 * 1 ^ 2 * c)) :=
    ((tendsto_const_nhds.mul hexp).mul (hratio.pow 2)).mul hAF
  have hineq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      256 * Real.exp (-M * r) * (Real.log (2 * r) / Real.log r) ^ 2 * φ r ≤ φ (2 * r) := by
    have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log r < 0 := hlog.eventually_lt_atBot 0
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < r₀ / 2 := by
      have : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_id
      exact this.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hlt, hsmall, self_mem_nhdsWithin] with r hr hr' hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hb := hbd r r hr0' hr0'.le (by linarith)
    have hrr : r + r = 2 * r := by ring
    rw [hrr] at hb
    have hw : 0 ≤ (2 * r) ^ 8 * (Real.log (2 * r)) ^ 2 := by positivity
    have key : (2 * r) ^ 8 * (Real.log (2 * r)) ^ 2 * (Real.exp (-M * r) * k r) ≤
        (2 * r) ^ 8 * (Real.log (2 * r)) ^ 2 * k (2 * r) := mul_le_mul_of_nonneg_left hb hw
    have hlogne : Real.log r ≠ 0 := hr.ne
    have eq1 : 256 * Real.exp (-M * r) * (Real.log (2 * r) / Real.log r) ^ 2 * φ r =
        (2 * r) ^ 8 * (Real.log (2 * r)) ^ 2 * (Real.exp (-M * r) * k r) := by
      simp only [hφ]
      field_simp
      ring
    simp only [hφ] at key ⊢
    rw [eq1]
    exact key
  have hle : 256 * 1 * 1 ^ 2 * c ≤ c := le_of_tendsto_of_tendsto hrhs hφ2 hineq
  linarith

end YMStatement
