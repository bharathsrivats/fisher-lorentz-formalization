import Mathlib
import YMStatement.Tensor
import YMStatement.AFKernel

/-!
# Euclidean Green's functions, Osterwalder-Schrader axioms, Euclidean mass gap

Clay (Jaffe-Witten, section 4, clay_ym.txt lines 279-280) requires axiomatic properties at least as
strong as Streater-Wightman [45] and Osterwalder-Schrader [35] (CMP 31 (1973), CMP 42 (1975)).

The Schwinger functions of the Yang-Mills Lagrangian density `Tr F²` have two-point singularity
`~ ‖x‖⁻⁸ (log ‖x‖)⁻²`, which is not locally integrable in four dimensions. They are therefore NOT
moments of a probability measure on `𝒮'(ℝ⁴)`, and we follow OS I in taking `S n` to be a
distribution on `°𝒮(ℝ^{4n})`, test functions vanishing with all derivatives at coincident points.
`S n` is a function on all test functions, but every axiom below constrains it only on `°𝒮`
(or on `𝒮₊ ⊂ °𝒮`), so values at other test functions are irrelevant.
-/

open scoped SchwartzMap
open Filter Topology MeasureTheory

noncomputable section

namespace YMStatement

/-- Euclidean space-time `ℝ⁴`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Configurations of `n` space-time points. -/
abbrev Config (n : ℕ) := Fin n → E4

/-- Real Schwartz test functions of `n` space-time points. -/
abbrev TestFn (n : ℕ) := 𝓢(Config n, ℝ)

/-- Euclidean time `x⁰`. -/
def time (x : E4) : ℝ := x 0

/-- Unit vector in the Euclidean time direction. -/
def e0 : E4 := EuclideanSpace.single 0 1

/-- `F ∈ °𝒮(ℝ^{4n})`: `F` and all its derivatives vanish wherever two arguments coincide (OS I, §2). -/
def VanishesAtCoincidences {n : ℕ} (F : TestFn n) : Prop :=
  ∀ x : Config n, (∃ i j : Fin n, i ≠ j ∧ x i = x j) → ∀ k : ℕ, iteratedFDeriv ℝ k (⇑F) x = 0

/-- `F ∈ 𝒮₊(ℝ^{4n})`: `F` and all derivatives vanish unless `0 < x₁⁰ < ⋯ < xₙ⁰` (OS I, §2). -/
def IsOrderedPositiveTime {n : ℕ} (F : TestFn n) : Prop :=
  ∀ x : Config n, ¬ ((∀ i, 0 < time (x i)) ∧ StrictMono fun i => time (x i)) →
    ∀ k : ℕ, iteratedFDeriv ℝ k (⇑F) x = 0

/-- A sequence of Euclidean Green's functions for one real scalar field. -/
abbrev SchwingerFamily := (n : ℕ) → TestFn n → ℝ

/-- Time reflection `θ(x⁰, x⃗) = (-x⁰, x⃗)`. -/
def timeReflection : E4 ≃L[ℝ] E4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).trans
    ((ContinuousLinearEquiv.piCongrRight fun i : Fin 4 =>
        if i = 0 then ContinuousLinearEquiv.neg ℝ else ContinuousLinearEquiv.refl ℝ ℝ).trans
      (EuclideanSpace.equiv (Fin 4) ℝ).symm)

/-- A linear map of `ℝ⁴` applied to every point of a configuration. -/
def diagCLE (n : ℕ) (L : E4 ≃L[ℝ] E4) : Config n ≃L[ℝ] Config n :=
  ContinuousLinearEquiv.piCongrRight fun _ : Fin n => L

/-- Relabelling the points of a configuration. -/
def permCLE {n : ℕ} (σ : Equiv.Perm (Fin n)) : Config n ≃L[ℝ] Config n :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => E4) σ

/-- `(Θ F*)(x₁, …, xₙ) = F(θ xₙ, …, θ x₁)` (real test functions: no complex conjugation). -/
def thetaStar {n : ℕ} (F : TestFn n) : TestFn n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ ((permCLE Fin.revPerm).trans (diagCLE n timeReflection)) F

/-- `F_{(a,R)}(x₁, …, xₙ) = F(R x₁ + a, …, R xₙ + a)` (OS I, §2). -/
def euclideanMotion {n : ℕ} (R : E4 ≃L[ℝ] E4) (a : E4) (F : TestFn n) : TestFn n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (diagCLE n R)
    (SchwartzMap.compSubConstCLM ℝ (fun _ : Fin n => -a) F)

/-- `F_π(x₁, …, xₙ) = F(x_{π 1}, …, x_{π n})` up to the direction convention for `π`. -/
def permuteTest {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : TestFn n) : TestFn n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (permCLE σ) F

/-- Translation of all arguments: `x ↦ F(x₁ - a, …, xₙ - a)`. -/
def translateTest {n : ℕ} (a : E4) (F : TestFn n) : TestFn n :=
  SchwartzMap.compSubConstCLM ℝ (fun _ : Fin n => a) F

/-- `R ∈ SO(4)`. -/
def IsSpecialOrthogonal (R : E4 ≃ₗᵢ[ℝ] E4) : Prop :=
  LinearMap.det (R.toLinearEquiv : E4 →ₗ[ℝ] E4) = 1

/-- A Schwartz norm of order `m`, equivalent to OS's `|F|_m` up to factors of factorial growth. -/
def schwartzNorm {n : ℕ} (m : ℕ) (F : TestFn n) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1), SchwartzMap.seminorm ℝ k l F

/-- The Osterwalder-Schrader axioms E0' (OS II, (4.1)), E1-E3 (OS I, §3) and E4 (OS I, §3),
for real test functions. The real positivity condition is paired with symmetry of the OS form,
which together are equivalent to OS's complex condition E2. -/
structure SatisfiesOS (S : SchwingerFamily) : Prop where
  /-- E0: `𝔖₀ = 1`. -/
  normalized : ∀ F : TestFn 0, S 0 F = F 0
  /-- E0: each `𝔖ₙ` is linear on `°𝒮(ℝ^{4n})`. -/
  linear : ∀ (n : ℕ) (F G : TestFn n) (a b : ℝ), VanishesAtCoincidences F →
    VanishesAtCoincidences G → S n (a • F + b • G) = a * S n F + b * S n G
  /-- E0' (linear growth condition): `|𝔖ₙ(F)| ≤ σₙ |F|_{n s}` with `σₙ ≤ α (n!)^β`. -/
  growth : ∃ (s : ℕ) (α β : ℝ), ∀ (n : ℕ) (F : TestFn n), VanishesAtCoincidences F →
    |S n F| ≤ α * (n.factorial : ℝ) ^ β * schwartzNorm (n * s) F
  /-- E1: Euclidean invariance under `SO(4) ⋉ ℝ⁴`. -/
  euclidean_invariant : ∀ (n : ℕ) (R : E4 ≃ₗᵢ[ℝ] E4) (a : E4), IsSpecialOrthogonal R →
    ∀ F : TestFn n, VanishesAtCoincidences F →
      S n (euclideanMotion R.toContinuousLinearEquiv a F) = S n F
  /-- E2: reflection positivity, `∑ₖ ∑ₗ 𝔖_{k+l}(Θ Fₖ* ⊗ Fₗ) ≥ 0` for `F ∈ 𝒮₊`. -/
  reflection_positive : ∀ (N : ℕ) (F : (k : Fin (N + 1)) → TestFn k),
    (∀ k, IsOrderedPositiveTime (F k)) →
      0 ≤ ∑ k : Fin (N + 1), ∑ l : Fin (N + 1), S (k + l) (tensor (thetaStar (F k)) (F l))
  /-- E2 (real form): the OS form is symmetric. -/
  reflection_symmetric : ∀ (n m : ℕ) (F : TestFn n) (G : TestFn m), IsOrderedPositiveTime F →
    IsOrderedPositiveTime G → S (n + m) (tensor (thetaStar F) G) = S (m + n) (tensor (thetaStar G) F)
  /-- E3: permutation symmetry. -/
  permutation_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (F : TestFn n),
    VanishesAtCoincidences F → S n (permuteTest σ F) = S n F
  /-- E4: cluster property along spatial directions `a = (0, a⃗)`. -/
  cluster : ∀ (n m : ℕ) (F : TestFn n) (G : TestFn m) (a : E4), IsOrderedPositiveTime F →
    IsOrderedPositiveTime G → time a = 0 → a ≠ 0 →
      Tendsto (fun lam : ℝ => S (n + m) (tensor (thetaStar F) (translateTest (lam • a) G))) atTop
        (𝓝 (S n (thetaStar F) * S m G))

/-- The Osterwalder-Schrader form `⟨F, G⟩ = ∑ₖ ∑ₗ 𝔖_{k+l}(Θ Fₖ* ⊗ Gₗ)`. -/
def osForm (S : SchwingerFamily) {N M : ℕ} (F : (k : Fin (N + 1)) → TestFn k)
    (G : (l : Fin (M + 1)) → TestFn l) : ℝ :=
  ∑ k : Fin (N + 1), ∑ l : Fin (M + 1), S (k + l) (tensor (thetaStar (F k)) (G l))

/-- `⟨F, Ω⟩ = ∑ₖ 𝔖ₖ(Θ Fₖ*)`. -/
def osLeftVacuum (S : SchwingerFamily) {N : ℕ} (F : (k : Fin (N + 1)) → TestFn k) : ℝ :=
  ∑ k : Fin (N + 1), S k (thetaStar (F k))

/-- `⟨Ω, G⟩ = ∑ₗ 𝔖ₗ(Gₗ)`. -/
def osRightVacuum (S : SchwingerFamily) {M : ℕ} (G : (l : Fin (M + 1)) → TestFn l) : ℝ :=
  ∑ l : Fin (M + 1), S l (G l)

/-- Euclidean time translation by `t ≥ 0`, which preserves `𝒮₊`. -/
def timeShift {M : ℕ} (t : ℝ) (G : (l : Fin (M + 1)) → TestFn l) : (l : Fin (M + 1)) → TestFn l :=
  fun l => translateTest (t • e0) (G l)

/-- **Mass gap `Δ`.** On the reconstructed Hilbert space `e^{-tH}` acts by Euclidean time
translation, so `H` has no spectrum in `(0, Δ)` and a unique vacuum iff
`‖e^{-tH}(1 - |Ω⟩⟨Ω|)‖ ≤ e^{-Δ t}`, i.e. iff the connected OS matrix elements obey the bound
below. `H` is tied to the Euclidean group by construction, not supplied as free data. -/
def HasMassGap (S : SchwingerFamily) (Δ : ℝ) : Prop :=
  ∀ (N M : ℕ) (F : (k : Fin (N + 1)) → TestFn k) (G : (l : Fin (M + 1)) → TestFn l),
    (∀ k, IsOrderedPositiveTime (F k)) → (∀ l, IsOrderedPositiveTime (G l)) →
    ∀ t : ℝ, 0 ≤ t →
      |osForm S F (timeShift t G) - osLeftVacuum S F * osRightVacuum S G| ≤
        Real.exp (-(Δ * t)) *
          Real.sqrt (osForm S F F - osLeftVacuum S F * osRightVacuum S F) *
          Real.sqrt (osForm S G G - osLeftVacuum S G * osRightVacuum S G)

/-- **Finite mass `m < ∞`** (Clay section 4, clay_ym.txt line 276: the mass `m` is the supremum of
admissible gaps and must be finite): the orthogonal complement of the vacuum in the reconstructed Hilbert space is nonzero. -/
def HasFiniteMass (S : SchwingerFamily) : Prop :=
  ∃ (N : ℕ) (F : (k : Fin (N + 1)) → TestFn k), (∀ k, IsOrderedPositiveTime (F k)) ∧
    0 < osForm S F F - osLeftVacuum S F * osRightVacuum S F

/-- A Schwartz function of one point viewed as a test function of a one-point configuration. -/
def onePoint (f : 𝓢(E4, ℝ)) : TestFn 1 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ E4) f

/-- `K` is a continuous (off the origin) kernel of the two-point function on test functions
with disjoint compact supports. -/
def IsTwoPointKernel (S : SchwingerFamily) (K : E4 → ℝ) : Prop :=
  ContinuousOn K {0}ᶜ ∧
    ∀ f g : 𝓢(E4, ℝ), HasCompactSupport f → HasCompactSupport g →
      Disjoint (tsupport f) (tsupport g) →
        S (1 + 1) (tensor (onePoint f) (onePoint g)) = ∫ x : E4, ∫ y : E4, f x * K (x - y) * g y

/-- **Short-distance agreement with asymptotic freedom** (leading log, Lagrangian density). -/
def AgreesWithAsymptoticFreedom (S : SchwingerFamily) : Prop :=
  (∃ K, IsTwoPointKernel S K) ∧ ∀ K, IsTwoPointKernel S K → ∃ c : ℝ, 0 < c ∧ AFProfile K c

/-! ## Anti-toy lemmas -/

/-- The trivial theory: `𝔖₀ = 1` and `𝔖ₙ = 0` for `n ≥ 1`. -/
def trivialSchwinger : SchwingerFamily := fun n F => if n = 0 then F 0 else 0

theorem thetaStar_apply_zero {n : ℕ} (F : TestFn n) : thetaStar F 0 = F 0 := by
  simp [thetaStar]

theorem tensor_apply_zero {n m : ℕ} (F : TestFn n) (G : TestFn m) :
    tensor F G 0 = F 0 * G 0 := by
  simp only [tensor_apply]
  rfl

/-- **Anti-toy T1 (trivial theory).** The trivial theory has `m = ∞`. -/
theorem trivialSchwinger_not_hasFiniteMass : ¬ HasFiniteMass trivialSchwinger := by
  rintro ⟨N, F, -, hpos⟩
  have key : osForm trivialSchwinger F F =
      osLeftVacuum trivialSchwinger F * osRightVacuum trivialSchwinger F := by
    simp only [osForm, osLeftVacuum, osRightVacuum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [trivialSchwinger, tensor_apply_zero, thetaStar_apply_zero]
    by_cases hk : (k : ℕ) = 0 <;> by_cases hl : (l : ℕ) = 0 <;> simp [hk, hl]
  linarith

/-- `S` does not change when one block of arguments is translated along `v`: the defining
property of a lower-dimensional model extended trivially along `v` (for a two-dimensional model,
along a whole 2-plane, which always contains a spatial direction). -/
def IsInvariantAlong (S : SchwingerFamily) (v : E4) : Prop :=
  ∀ (n m : ℕ) (F : TestFn n) (G : TestFn m) (lam : ℝ),
    S (n + m) (tensor F (translateTest (lam • v) G)) = S (n + m) (tensor F G)

/-- **Anti-toy T2 (two-dimensional models).** A theory satisfying the cluster axiom that is
invariant along a nonzero spatial direction factorises, so it has `m = ∞`. -/
theorem not_hasFiniteMass_of_invariantAlong {S : SchwingerFamily} (hOS : SatisfiesOS S) {v : E4}
    (hv0 : time v = 0) (hv : v ≠ 0) (hinv : IsInvariantAlong S v) : ¬ HasFiniteMass S := by
  rintro ⟨N, F, hF, hpos⟩
  have hfac : ∀ k l : Fin (N + 1), S (k + l) (tensor (thetaStar (F k)) (F l)) =
      S k (thetaStar (F k)) * S l (F l) := by
    intro k l
    have hlim := hOS.cluster k l (F k) (F l) v (hF k) (hF l) hv0 hv
    have hconst : (fun lam : ℝ => S (k + l) (tensor (thetaStar (F k)) (translateTest (lam • v) (F l))))
        = fun _ => S (k + l) (tensor (thetaStar (F k)) (F l)) :=
      funext fun lam => hinv k l _ _ lam
    rw [hconst] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have key : osForm S F F = osLeftVacuum S F * osRightVacuum S F := by
    simp only [osForm, osLeftVacuum, osRightVacuum, Finset.sum_mul_sum, hfac]
  linarith

/-- **Anti-toy T4 (Gaussian free field and its Wick powers of dimension < 4).** A two-point kernel
bounded by `B ‖x‖^{-p}`, `p < 8` (free field `p = 2`, Wick square `p = 4`) is incompatible with
the asymptotic-freedom clause. -/
theorem not_agreesWithAF_of_kernel_le {S : SchwingerFamily} {K : E4 → ℝ} (hK : IsTwoPointKernel S K)
    {B p : ℝ} (hp : p < 8) (hbound : ∀ᶠ x in 𝓝[≠] (0 : E4), |K x| ≤ B * ‖x‖ ^ (-p)) :
    ¬ AgreesWithAsymptoticFreedom S := by
  rintro ⟨-, hAF⟩
  obtain ⟨c, hc, hprof⟩ := hAF K hK
  exact not_AFProfile_of_le_rpow hc.ne' hp hbound hprof

/-- **Anti-toy T4' (scale-invariant singularities).** A kernel with `‖x‖⁸ K x ≥ b > 0` near `0`
(Wick fourth power of a free field, `Tr F²` of free Maxwell fields) is excluded. -/
theorem not_agreesWithAF_of_kernel_ge {S : SchwingerFamily} {K : E4 → ℝ} (hK : IsTwoPointKernel S K)
    {b : ℝ} (hb : 0 < b) (hbound : ∀ᶠ x in 𝓝[≠] (0 : E4), b ≤ ‖x‖ ^ 8 * K x) :
    ¬ AgreesWithAsymptoticFreedom S := by
  rintro ⟨-, hAF⟩
  obtain ⟨c, -, hprof⟩ := hAF K hK
  exact not_AFProfile_of_ge_pow hb hbound hprof

theorem norm_e0 : ‖e0‖ = 1 := by
  simp [e0]

/-- **Anti-toy T5 (bounded Hamiltonian), kernel form.** If the two-point kernel along the Euclidean
time axis obeys the lower bound `K((r+s) e₀) ≥ e^{-Ms} K(r e₀)` implied by a bounded generator of
time translations, the asymptotic-freedom clause fails. -/
theorem not_agreesWithAF_of_boundedTransfer {S : SchwingerFamily} {K : E4 → ℝ}
    (hK : IsTwoPointKernel S K) {M r₀ : ℝ} (hr₀ : 0 < r₀)
    (hbd : ∀ r s : ℝ, 0 < r → 0 ≤ s → r + s < r₀ →
      Real.exp (-M * s) * K (r • e0) ≤ K ((r + s) • e0)) :
    ¬ AgreesWithAsymptoticFreedom S := by
  rintro ⟨-, hAF⟩
  obtain ⟨c, hc, hprof⟩ := hAF K hK
  have hline : Tendsto (fun r : ℝ => r • e0) (𝓝[>] 0) (𝓝[≠] (0 : E4)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => r • e0) (𝓝 0) (𝓝 ((0 : ℝ) • e0)) :=
        (continuous_id.smul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      have he : e0 ≠ 0 := by
        intro h
        have := norm_e0
        rw [h, norm_zero] at this
        exact zero_ne_one this
      exact smul_ne_zero hr'.ne' he
  have hradial : Tendsto (fun r : ℝ => r ^ 8 * (Real.log r) ^ 2 * K (r • e0)) (𝓝[>] 0) (𝓝 c) := by
    refine Tendsto.congr' ?_ (hprof.comp hline)
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    have hn : ‖r • e0‖ = r := by
      rw [norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_of_pos hr']
    simp only [Function.comp, hn]
  exact not_bounded_generator_of_AFProfile (k := fun r => K (r • e0)) hc hr₀ hradial hbd

end YMStatement
