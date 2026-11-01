# fisher-lorentz-formalization

Machine-checked proofs, in **Lean 4 + Mathlib**, by **Bharath G. Srivats**. Four libraries:

- **`Confinement`: Wilson's area law and exponential clustering at strong coupling, with no
  cluster expansion**, for `SU(N)`, every `N ≥ 2`, and other gauge groups, in every spacetime
  dimension `d ≥ 2`, with an explicit string tension and an explicit rate. See the next section.
- **`FisherLorentz`: 82 named results across thirteen modules** from the published and preprint
  corpus.
- **`YMStatement`, `YMReview`: a prototype Lean statement of the Yang-Mills problem**, with anti-toy
  lemmas and the known weakness a review found. It is a formulation, not the Clay problem. See
  below.

**Zero `sorry`.** The build itself fails unless every theorem, in all four libraries, depends only on
the three standard axioms of Lean's logic (651 theorems at this commit, the auxiliary lemmas
included).

## Wilson's area law, machine-checked

Quark confinement on the lattice is the statement that a Wilson loop decays with the **area** it
encloses. Here is the theorem, for the torus `(ℤ/L)ⁿ × ℤ/Lₜ` in spacetime dimension `d = n + 1`,
the Haar measure on each link, and the weight `exp (β_W ∑ₚ Re Tr Qₚ / N)`:

```lean
theorem Confinement.area_law_SU_exp (hN : 2 ≤ N) (hL : 3 ≤ L) (hR : R ≤ L / 2) (hT : T ≤ Lt)
    (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (βW : ℝ)
    (h0 : 0 < 4 * n * |βW|) (hq : 4 * n * |βW| < 1) :
    ‖gibbs (haarSU N) normTr βW (fun U => normTr (rectangle U x t₀ μ R T))‖
      ≤ Real.exp (Real.log (4 * n * |βW|) * (R * T) - Real.log (1 - 4 * n * |βW|) * T)
```

So for `|β_W| < 1 / (4 (d - 1))` the `R × T` loop satisfies `‖⟨Tr Q_ℓ / N⟩‖ ≤ exp (-σ R T + κ T)`,
with string tension at least `σ = -log (4 (d - 1) |β_W|) > 0`. `area_law_general` proves the same
for **any** group with a probability measure invariant under a central element `z` and a bounded
function `χ` with `χ (z g) = ζ χ (g)`, `ζ ≠ 1`.

`polyakov_SU` gives the same decay for Polyakov loop correlators at **every temporal extent** `Lₜ`, so the window contains no deconfined phase at any temperature.

**The proof** is one page and uses no cluster expansion. Each vertical plaquette weight is a constant times
`1 + h` with `0 ≤ h ≤ p (1 + h)`, `p = 1 - exp (-2 |β_W|)`. Expand over sets `A` of vertical
plaquettes. If `A` does not join the two sides of the loop in some slab, multiplying the vertical
links of that slab over one cluster by `z` preserves everything except the loop, which picks up
`ζ ≠ 1`, so the term of `A` vanishes. The surviving `A` contain a path in every slab, and the
pointwise bound counts them.

| File | Content |
|---|---|
| `Confinement/Expansion.lean` | The positive expansion, abstractly: `expansion_bound` |
| `Confinement/Lattice.lean` | Links, plaquettes, Wilson weight, Gibbs expectation, the rectangle |
| `Confinement/GaugeInvariance.lean` | Plaquettes and the rectangle conjugate under gauge transformations, so the loop closes |
| `Confinement/Bonds.lean` | Slab graphs, lifted paths, walk counting, displacement bound on the torus |
| `Confinement/Twist.lean` | The centre twist and its measure invariance |
| `Confinement/AreaLaw.lean` | `term_vanish_general`, `slab_law`, `area_law_general`, `polyakov_general` |
| `Confinement/Clustering.lean` | Plaquette graph, two copies, exchange: `term_vanish_swap`, `clustering_general` |
| `Confinement/SpecialUnitary.lean` | `SU(N)`: compactness, Haar measure, centre; `area_law_SU`, `area_law_SU_window`, `area_law_SU_exp`, `polyakov_SU`, `clustering_SU`, `mass_gap_plaquette_SU`, `partition_pos` |
| `Confinement/Instances.lean` | `area_law_compact` for any compact group with a detected centre; `area_law_U1`, `area_law_Z2` |
| `Confinement/Audit.lean` | `#print axioms` on the headline results, and the axiom gate |

**The mass gap.** `mass_gap_plaquette_SU`: for `0 < q := 16 (2 n - 1) |β_W| < 1`, the connected
correlation of two plaquette traces at time distance at least `D` is at most
`C exp (-m (D - 2))`, with `m = -log q`, uniformly in the volume. `clustering_general` proves the
same shape for **any** group, any probability measure on links and any bounded local observables,
with no centre needed: write `Cov(f, g) = ½ E[(f - f')(g - g')]` on two independent copies, expand
all plaquettes, and exchange the copies on the cluster of the support of `f`. If the expansion
does not join the two supports, the term changes sign, so it vanishes. This is a statement about
correlations. Turning it into a spectral gap of the transfer matrix needs reflection positivity,
which is not formalised.

**How to trust it.** The definitions are the short file `Lattice.lean`. `rectangle_gauge`,
`Qv_gauge` and `Qh_gauge` show the holonomies transform correctly, and `partition_pos` shows the
expectation is not vacuous. A deliberate-break pass was run: a plaquette orientation slip, a loop
that fails to close, a plaquette missing a link, a weakened window, halved constants in the
pointwise bounds, wrong degree and incidence counts, and dropped hypotheses each make the build
fail, and a planted `sorry` trips the gate.

**Scope.** These are strong-coupling theorems at fixed lattice spacing, on finite tori, uniform in
the volume. They say nothing about the continuum limit, a mass gap in physical units, or the Clay
Millennium problem.
Its window is far smaller than the best known by hand, for instance `|β_W| < 2/(d - 1)` for `SU(2)`
in the companion note, which is not formalised here.

**Prior work.** This is **not** the first machine-checked area law. L. Eriksson's
[THE-ERIKSSON-PROGRAMME](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME) has a Lean 4 proof
of a volume-uniform Wilson-loop area law for `SU(N)` (paper dated 2 July 2026), by a formalized
cluster expansion, with the standard three axioms. [lgt](https://github.com/mrdouglasny/lgt) has a
Lean strong-coupling mass gap for `U(n)`, and
[consensusframework/yang-mills-mass-gap](https://github.com/consensusframework/yang-mills-mass-gap)
and A. Novickis (Zenodo record 20547676) have related results. What this library adds is a much
shorter route with no cluster expansion, any gauge group with a nontrivial central character, an
explicit `R × T` rectangle with a closed-form string tension, Polyakov correlators at every temporal
extent, and a far larger window: at `d = 4` the hypotheses of `normalized_exp_wilson_loop_area_law`
force `β_W < 5.6 × 10⁻⁸`, against `1/12` here. An earlier version of this README said searches had
found no earlier machine-checked area law. That search missed Eriksson's work.

## A prototype statement of the Yang-Mills problem

`YMStatement.YangMillsExistenceAndMassGap : Prop` asks, for every compact simple gauge group, for
Schwinger functions of `Tr F²` that are a continuum limit of renormalised Wilson lattice
expectations, satisfy the Osterwalder-Schrader axioms, have the leading-log short-distance profile,
and have finite mass and a Euclidean gap. It uses no `opaque`, `axiom` or `sorry`, and it comes with
anti-toy lemmas (trivial theory, spatially invariant models, abelian groups, free-field kernels) and
`SO(3)` as a compact simple instance.

**Read this before using it.** It is a formulation and **not** equivalent to the Clay problem in
either direction: it is weaker in field content and stronger in fixing the Wilson route. A review
found that a generalised free field with spectral density `s² / log² s` appears to meet every clause
except the lattice clause, so all gauge-theoretic content comes from that clause alone
(`YMReview/GFFEscape.lean` checks the kernel-level part; the Osterwalder-Schrader and gap clauses for
that field are not checked in Lean). `IsInvariantAlong` ranges over test functions it should not.
It has not been proposed to any statement collection. Nothing here proves anything about the
problem.

## The Fisher-Lorentz library

The central identity is

```
I(V) = γ²(V) = 1/(1 − V²),    V = 2p − 1,    η = artanh V
```

the Fisher information of a binary measurement in the visibility coordinate,
equal to the squared Lorentz factor.

---

## The corpus

The complete published, submitted and archived record this formalisation
draws on. Peer-reviewed work first, then work under review, then preprints.

### Peer-reviewed

1. **Srivats, B. G.** "Fisher Information as the Squared Lorentz Factor:
   Conformal Equivalence of the Bures and Beltrami–Klein Metrics on the Qubit
   Bloch Ball." *Quantum Reports* **8**(3), 68 (2026).
   doi:[10.3390/quantum8030068](https://doi.org/10.3390/quantum8030068)
2. **Srivats, B. G.** "The Hill Coefficient as Fisher Information: An
   Information-Theoretic Identity for Allosteric Cooperativity."
   *BioSystems* **266**, 105847 (2026).
   doi:[10.1016/j.biosystems.2026.105847](https://doi.org/10.1016/j.biosystems.2026.105847).
   Data: doi:[10.17632/xftn8knz8t.1](https://doi.org/10.17632/xftn8knz8t.1)
3. **Srivats, B. G.** "The Squared Lorentz Factor in Quantum Computation:
   Grover Search, Quantum Batteries, and the Zeno Effect."
   *Next Research* **10**, 101888 (2026).
   doi:[10.1016/j.nexres.2026.101888](https://doi.org/10.1016/j.nexres.2026.101888)
4. **Srivats, B. G.** "Three Fisher–Rao Identities on the Binary Statistical
   Manifold: Jeffreys Uniqueness, the Gudermannian Bridge, and Isotropic
   Retention." *European Journal of Pure and Applied Mathematics* **19**(2),
   Article 7819 (2026).
   doi:[10.29020/nybg.ejpam.v19i2.7819](https://doi.org/10.29020/nybg.ejpam.v19i2.7819)

### Submitted manuscripts (status changes and is not asserted here)

5. **Srivats, B. G.** "A Modular Speed Limit on the Qubit: Bloch Precession,
   Saturation, Channel Data-Processing, and the Vanishing of Modular Flow at
   Pure States." Preprint and verification material: reference 23.
6. **Srivats, B. G.** "Lorentz Kinematics of Sequential Binary Qubit
   Measurements: Thomas–Wigner Composition and SLD Saturation from the
   Fisher–Lorentz Identity." *Journal of Mathematical Physics*.
7. **Srivats, B. G.** "Möbius Covariance, Effect Classification, and a
   Holographic Correspondence for Qubit Fisher Information."
   *Quantum Information Processing*.
8. **Srivats, B. G.** "Observer Limits and Thermodynamics of Binary Quantum
   Measurement: A Lawvere Obstruction and an Energy–Precision Bound."
   *Pramana*.
9. **Srivats, B. G.** "Fisher-Information Speed Limits: Ito, Ito–Dechant,
   Cramér–Rao and Margolus–Levitin Unified by the Squared Lorentz Factor."
   *Fluctuation and Noise Letters*.
10. **Srivats, B. G.** "An Information-Geometric Identity for the
    Wright–Fisher Diffusion: Genetic Drift as Inverse Fisher Information on
    the Allele-Frequency Manifold." *Theory in Biosciences*.
11. **Srivats, B. G.** "Thermodynamic Consequences of the Identity
    I(V) = γ²: A Cooling-Cost Divergence Theorem and a Falsifiable
    Entropy–Visibility Law."
12. **Srivats, B. G.** "Why Current AI Cannot Be Conscious: A Thermodynamic
    Criterion from the Fisher–Lorentz Identity."
    *Journal of Artificial Intelligence and Consciousness*.
13. **Srivats, B. G.** "Discriminating Thomas–Wigner from
    Pancharatnam–Berry Rotations." Earlier manuscript; its discrimination claim was
    withdrawn by the author on 2026-07-09.

### Preprints

Every Zenodo entry gives the version-independent **concept DOI** (it always
resolves to the latest version) and the **version DOI** cited by this
repository. Version chains were read from the Zenodo REST API on 2026-09-10;
SSRN DOIs were checked to resolve. The full chains are tabulated under
"A note on the DOIs" below.

14. **Srivats, B. G.** "Fisher Information Is the Squared Lorentz Factor: Why
    the Qubit Is Special." Zenodo, v2.1 (2026-03-31).
    Concept doi:[10.5281/zenodo.18870606](https://doi.org/10.5281/zenodo.18870606) ·
    Version doi:[10.5281/zenodo.19363449](https://doi.org/10.5281/zenodo.19363449) ·
    SSRN doi:[10.2139/ssrn.6555718](https://doi.org/10.2139/ssrn.6555718)
15. **Srivats, B. G.** "The Algebra of the Qubit: Fourteen Theorems on
    I(V) = γ²(V)." Zenodo, v2 (2026-04-19).
    Concept doi:[10.5281/zenodo.19639616](https://doi.org/10.5281/zenodo.19639616) ·
    Version doi:[10.5281/zenodo.19653530](https://doi.org/10.5281/zenodo.19653530)
16. **Srivats, B. G.** "From Measurement to Reality: I(V) = γ²(V) and the
    Geometry of Binary Distinction." Zenodo, v4 (2026-04-23).
    Concept doi:[10.5281/zenodo.19388803](https://doi.org/10.5281/zenodo.19388803) ·
    Version doi:[10.5281/zenodo.19722019](https://doi.org/10.5281/zenodo.19722019) ·
    SSRN doi:[10.2139/ssrn.6512663](https://doi.org/10.2139/ssrn.6512663)
17. **Srivats, B. G.** "The Squared Lorentz Factor in Quantum Computation:
    Grover Search, Quantum Batteries, and the Zeno Effect." SSRN (2026).
    doi:[10.2139/ssrn.6624079](https://doi.org/10.2139/ssrn.6624079).
    Preprint of reference 3.
18. **Srivats, B. G.** "The Hill Coefficient as Fisher Information: An
    Information-Theoretic Identity for Allosteric Cooperativity." SSRN (2026).
    doi:[10.2139/ssrn.6553826](https://doi.org/10.2139/ssrn.6553826).
    Preprint of reference 2.
19. **Srivats, B. G.** "Why Current AI Cannot Be Conscious: A Thermodynamic
    Criterion from the Fisher–Lorentz Identity." Zenodo, v1.1 (2026-04-09).
    Concept doi:[10.5281/zenodo.19486629](https://doi.org/10.5281/zenodo.19486629) ·
    Version doi:[10.5281/zenodo.19489276](https://doi.org/10.5281/zenodo.19489276) ·
    SSRN doi:[10.2139/ssrn.6555758](https://doi.org/10.2139/ssrn.6555758).
    Preprint of reference 12.
20. **Srivats, B. G.** "The Lorentz Factor in Binary Classification: Natural
    Gradient Descent and the Fisher–Lorentz Identity." Zenodo, v1 (2026-04-23).
    Concept doi:[10.5281/zenodo.19722236](https://doi.org/10.5281/zenodo.19722236) ·
    Version doi:[10.5281/zenodo.19722237](https://doi.org/10.5281/zenodo.19722237)
21. **Srivats, B. G.** "Discriminating Thomas–Wigner from Pancharatnam–Berry
    Rotations in Sequential Weak Qubit Measurements: A Variable-Visibility
    Protocol." Zenodo, v1 (2026-04-23).
    Concept doi:[10.5281/zenodo.19722697](https://doi.org/10.5281/zenodo.19722697) ·
    Version doi:[10.5281/zenodo.19722698](https://doi.org/10.5281/zenodo.19722698).
    Preprint of reference 13. The discrimination claim and the V = 0.9102
    crossing in this protocol were later withdrawn by the author; see
    `ThomasWigner.lean` for what is machine-checked.
22. **Srivats, B. G.** "Theory of Reality: From Binary Distinction to the
    Structure of Existence." Zenodo (2026-05-21).
    Concept doi:[10.5281/zenodo.20321417](https://doi.org/10.5281/zenodo.20321417) ·
    Version doi:[10.5281/zenodo.20321418](https://doi.org/10.5281/zenodo.20321418).
    *Speculative tier; cited for completeness. No result in this repository
    depends on it.*
23. **Srivats, B. G.** "A Modular Speed Limit on the Qubit: Bloch Precession,
    Saturation, Channel Data-Processing, and the Vanishing of Modular Flow at
    Pure States." Zenodo, v1.1 (2026-05-19).
    Concept doi:[10.5281/zenodo.20245544](https://doi.org/10.5281/zenodo.20245544) ·
    Version doi:[10.5281/zenodo.20287850](https://doi.org/10.5281/zenodo.20287850).
    Preprint of reference 5.

### External results relied upon

- J. Dittmann. "The Scalar Curvature of the Bures Metric on the Space of
  Density Matrices." *J. Geom. Phys.* **31** (1999) 16–24.
  arXiv:quant-ph/9810012. *(Corollary 1 gives the Bures sectional curvature
  in general form; the `N ≥ 3` obstruction rests on it.)*
- A. Uhlmann; M. Hübner. Bures metric as one quarter the round `S³` metric on
  the qubit Bloch ball.
- A. A. Ungar; J. Chen. Gyrovector structure of the Bloch ball; the gamma
  identity of the Einstein gyrogroup underlies the Möbius covariance result.
- F. Nielsen. "A note on some information-theoretic divergences between Zeta
  distributions." arXiv:2104.10548.

## What is machine-checked, module by module

### `Basic.lean` — the anchor identity  *(refs 1, 12)*

| Result | Lean name |
|---|---|
| `I(V) = γ²(V) = 1/(1−V²)` | `fisherInfo_eq_gammaSq` |
| `I(V) = 1/(4 p₊p₋)` | `fisherInfo_eq_inv_four_mul_prod` |
| `γ²` unbounded on `(−1,1)` | `gammaSq_ge` |
| `dp±/dV = ±1/2`, via Mathlib `deriv` | `deriv_pPlus`, `deriv_pMinus` |

Fisher information is **defined through Mathlib's `deriv`**, and the
derivatives are proven rather than assumed, so the theorem states what the
paper states instead of defining its way to the answer.

### `Conformal.lean` — the conformal equivalence  *(ref 1, Theorem 1)*

| Result | Lean name |
|---|---|
| **`ds²_BK = 4γ²(r)·ds²_Bures`, at tensor level** | `bkForm_eq_four_gammaSq_mul_buresForm` |
| radial component | `conformal_radial` |
| angular component | `conformal_angular` |
| `4γ²` is the only factor that works | `conformal_factor_unique` |
| Bures radial speed `1/(2√(1−r²))` | `hasDerivAt_buresDist` |
| `d/dr artanh r = 1/(1−r²)`, from scratch | `hasDerivAt_artanh` |
| `2 s_B(r) = gd(s_BK(r))` | `two_buresDist_eq_gd_bkDist` |

Both metrics are encoded as the quadratic form they assign to a tangent
vector `(dr, dθ, dφ)`, so the identity is quantified over **every tangent
vector at every point**. That is what makes it a tensor statement rather than
a statement about distances.


### `Hemisphere.lean`: where the conformal factor comes from

The factor `4γ²` is classical in substance: the Bures metric is one quarter of the
round hemisphere metric (Uhlmann 1992; Hübner 1992), and the Beltrami-Klein metric
is that round metric divided by the squared height (Cannon, Floyd, Kenyon, Parry,
*Hyperbolic Geometry*, MSRI Publ. 31 (1997), §7). This module proves both facts in
the coordinates of `Conformal.lean` and re-derives Theorem 1 from them.

| Result | Lean name |
|---|---|
| the height `√(1−|y|²)` moves at rate `−(y·v)/√(1−|y|²)` | `hasDerivAt_height` |
| the pull-back of the round metric is `|v|² + (y·v)²/(1−|y|²)` | `round_pullback` |
| **Bures = one quarter of the hemisphere metric** | `buresForm_eq_quarter_hemRound` |
| **Beltrami-Klein = hemisphere metric / height²** | `bkForm_eq_hemRound_div_height` |
| Theorem 1 re-derived from the two | `bkForm_eq_four_gammaSq_mul_buresForm_via_hemisphere` |

### `Gudermannian.lean` — the Gudermannian bridge  *(ref 4, Theorem 2)*

| Result | Lean name |
|---|---|
| `gd x = arcsin(tanh x)` (both definitions agree) | `gd_eq_arcsin_tanh` |
| `arcsin V = gd(artanh V)` | `arcsin_eq_gd_artanh` |
| `tanh 2y = 2 tanh y/(1+tanh²y)` | `tanh_two_mul` |
| `sin(2 arctan t) = 2t/(1+t²)` | `sin_two_arctan` |
| `2 arctan(tanh(x/2)) ∈ [−π/2, π/2]` | `gd_mem_Icc` |

The range lemma is the non-trivial step: it is the side condition that lets
`arcsin ∘ sin` invert, and informal proofs routinely omit it.

### `Modular.lean` — modular structure  *(ref 5, Proposition 1)*

| Result | Lean name |
|---|---|
| `λ = p/(1−p) = (1+V)/(1−V)` | `modRatio_eq` |
| **`λ = exp(2 artanh V) = e^{2η}`** | `modRatio_eq_exp_two_rapidity` |
| `tanh η = V`, `γ² = cosh²η` | `tanh_rapidity`, `gammaSq_eq_cosh_sq` |
| `Δ(E₀₁) = (p/(1−p))·E₀₁` | `modOp_E01` |
| `Δ(E₁₀) = ((1−p)/p)·E₁₀` | `modOp_E10` |
| `Δ(E₀₀) = E₀₀`, `Δ(E₁₁) = E₁₁` | `modOp_E00`, `modOp_E11` |
| the nontrivial eigenvalue is `e^{2η}` | `modOp_nontrivial_eigenvalue` |

`Δ(X) = ρXρ⁻¹` is computed on explicit 2×2 matrices, with the inverse
constructed and proven. Together the four eigenvector results give the
modular spectrum `{1, 1, e^{2η}, e^{−2η}}`.

### `Moebius.lean` — Möbius covariance  *(refs 7, 13)*

| Result | Lean name |
|---|---|
| `1 − (V ⊕ ξ)² = (1−V²)(1−ξ²)/(1+Vξ)²` | `one_sub_einsteinAdd_sq` |
| **`I(V ⊕ ξ) = γ²(ξ)(1+Vξ)²·I(V)`** | `fisherInfo_einsteinAdd` |
| `γ²(V ⊕ ξ) = γ²(V)γ²(ξ)(1+Vξ)²` (SLOCC law) | `gammaSq_einsteinAdd` |
| Einstein addition preserves `(−1,1)` | `einsteinAdd_mem` |
| commutativity, identity, inverses | `einsteinAdd_comm`, `einsteinAdd_zero`, `einsteinAdd_neg_self` |

Fisher information is **not** an `SL(2,ℂ)` invariant; it carries a conformal
weight, and the weight is proven here.

### `ThomasWigner.lean` — sequential measurement kinematics  *(refs 6, 13)*

| Result | Lean name |
|---|---|
| `tanh y = sinh 2y/(cosh 2y + 1)` | `tanh_eq_sinh_two_div` |
| **`tanh(η/2) = Vγ/(γ+1)`** | `tanh_half_rapidity` |
| Bloch and rapidity forms of `tan(Ω/2)` agree | `twTanHalf_eq` |
| at `θ = π/2`, `V₁ = V₂`: `tan(Ω/2) = tanh²(η/2)` | `twTanHalf_orthogonal` |
| `sinh(artanh V) = Vγ`, `cosh(artanh V) = γ` | `sinh_artanh_eq`, `cosh_artanh_eq` |

### `SpeedLimits.lean` — Cramér–Rao and the Planckian point  *(refs 8, 9)*

| Result | Lean name |
|---|---|
| **`γ²(V)·(1−V²) = 1`** | `gammaSq_mul_one_sub_sq` |
| `1/(N I(V)) = (1−V²)/N` | `cramerRao_floor` |
| `V_P = √(1−ln 2) ∈ (0,1)` | `planckianVisibility_mem` |
| **`γ²(V_P) = 1/ln 2`** | `gammaSq_planckian` |
| floor `= (ln 2)²` in units of `kT` | `planckian_floor` |
| `c(1−V²) = c/γ²(V)`, the two forms of the bound | `energyPrecision_forms` |

### `ThirdLaw.lean` — the cooling-cost divergence  *(ref 11, Theorem 1)*

| Result | Lean name |
|---|---|
| **Bures cooling distance `≤ π/4`, uniformly** | `buresDist_le_pi_div_four` |
| `s_B(1) = π/4` exactly | `buresDist_one` |
| `L_BK(ε) = ½ log((1−ε)/ε)` | `bkDist_cooling` |
| **`L_BK` unbounded, with explicit witness `ε = 1/(2+e^{2M})`** | `bkDist_cooling_unbounded` |
| the contrast, in one statement | `cooling_cost_contrast` |
| halving `ε` costs a fixed increment | `bkDist_halving` |

The pure state lies at **finite** statistical distance and **infinite**
thermodynamic distance. Both halves are proven.

### `QuantumComputation.lean` — Grover, batteries, Zeno  *(ref 3)*

| Result | Lean name |
|---|---|
| **`artanh` is an antiderivative of `I(V)`** | `hasDerivAt_artanh_eq_fisherInfo` |
| `V_f = √(1−1/N) ∈ [0,1)` | `groverVisibility_mem` |
| **`γ²(V_f) = N`** | `gammaSq_groverVisibility` |
| battery ratio `= gd(η)/(2η)` | `batteryRatio_eq_gd` |
| **Zeno threshold: `γ²(1/√2) = 2`** | `gammaSq_zeno_threshold` |

The first row is the structural point: the accumulated Fisher cost of Grover
*is* the Beltrami–Klein distance, because `artanh` integrates `γ²`.

### `Identities.lean` — biology and population genetics  *(refs 2, 10, 4)*

| Result | Lean name |
|---|---|
| `I_θ = n_H² p(1−p)` | `hillFisher_eq` |
| **`I_θ|_{p=1/2} = n_H²/4`** | `hillFisher_midpoint` |
| **`Var(ΔV) = 1/(2N_e γ²(V))`** | `wfVariance_eq_inv_gammaSq` |
| Jeffreys density `= √I(V)/π` | `jeffreysDensity_eq_sqrt_fisher` |
| `γ(V)² = γ²(V)` | `gamma_sq_eq_gammaSq` |

Worked values `n_H = 2.8 → 1.96` and `n_H = 10.3 → 26.5225` are checked by
`norm_num`.

### `Retention.lean` — isotropic retention  *(ref 4, Theorem 3)*

| Result | Lean name |
|---|---|
| **`L(r) = 2 artanh r`** | `logFactor_eq_two_artanh` |
| `R(r) = ⟨I_cl⟩/r²`, the two forms agree | `retention_eq_avg_div` |
| `R` in the rapidity coordinate | `retention_rapidity` |

### `NaturalGradient.lean` — the logit coordinate  *(ref 15)*

| Result | Lean name |
|---|---|
| `V = tanh(f/2) ∈ (−1,1)` | `logitToVisibility_mem` |
| **`I_logit = 1/(4γ²(V))`** | `fisherLogit_eq_inv` |
| `I(V)·4I_logit = 1` | `step_ratio` |

---

## What is NOT machine-checked

Stated explicitly so this repository cannot be mistaken for more than it is.

- **The `N ≥ 3` Weyl obstruction** (ref 1, Theorem 2), and the accompanying
  su(3) sectional-curvature computation. This is the deepest result in the
  corpus and is **not** formalised here. It requires Weyl-tensor machinery
  beyond current Mathlib.
- **Most of the Modular Speed Limit theorems** (ref 5): the cross-state
  variance, the Mandelstam–Tamm bound, channel data-processing, the
  integrated Bures bound, the operator-norm bound, Bloch precession, work
  extraction, and the maximum modular speed. Only Proposition 1 is here.
- **Limits and asymptotics.** `R(0⁺) = 1/3` and `R(1⁻) = 1/2` (ref 4) are
  *not* formalised; only the algebraic identities behind them are. Likewise
  the series expansions.
- **The Lawvere obstruction** (ref 8) and the holographic scaling
  correspondence (ref 7), whose own paper labels its constant `κ_d` a
  conjecture.
- Everything in refs 14 and 16, which are synthesis and interpretation rather
  than theorem-proving documents.
- **The `SU(2)` area law at `|β_W| < 2/(d - 1)`** of the companion note, its sharp Wasserstein bound
  on `S³`, infinite-volume Gibbs measures, and anything about the continuum limit. The
  `Confinement` library covers the elementary all-`N` theorem on finite tori only.

No claim is made about any of these.

---

## The audit gate

A Lean file can compile with `sorry` in it, so a successful build proves
nothing unless the build itself checks axioms. This one does.

`Confinement/Audit.lean`, `YMStatement/Audit.lean` and `YMReview/AuditReview.lean` do the same for
their libraries.
`FisherLorentz/Audit.lean` runs `#print axioms` on all 82 named results, for a
readable record, and ends with `#assert_standard_axioms_in FisherLorentz`
(defined in `FisherLorentz/AxiomGate.lean`). That command walks every theorem
constant under the `FisherLorentz` namespace, including results nobody listed and
the auxiliary lemmas Lean generates (216 at this commit), collects its axioms,
and **fails the build** if any lies outside

```
[propext, Classical.choice, Quot.sound]
```

so `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`) and any declared
`axiom` are rejected whether or not they appear in the source text. Negative
controls were run: a `sorry` proof, a `native_decide` proof and a custom axiom
each fail the gate, and a clean proof passes. CI builds on every push, checks
that all four gates reported success, and keeps the older text scan for `sorry`,
`axiom` and `native_decide` as a second line.

## Build

```bash
lake exe cache get
lake build
```

Lean **4.33.0** (pinned in `lean-toolchain`), Mathlib **v4.33.0**. The
Mathlib cache is ~7.5 GB; build outside any synced folder.

## A note on the DOIs

Zenodo assigns one concept DOI per record and a fresh DOI to every version.
The chains below were read from the Zenodo REST API on 2026-09-10. The bold
entry is the version cited in this README; every other DOI in the chain
appears somewhere in the source corpus and resolves to an earlier version of
the same record.

| Ref | Concept DOI | Versions, oldest to newest (date) |
|---|---|---|
| 14 | 10.5281/zenodo.18870606 | 18870607 v1.0 (2026-03-04), 18949072 (2026-03-10), **19363449** v2.1 (2026-03-31) |
| 15 | 10.5281/zenodo.19639616 | 19639617 v1 (2026-04-18), **19653530** v2 (2026-04-19) |
| 16 | 10.5281/zenodo.19388803 | 19388804 v1.0 (2026-04-02), 19394102 v1.1 (2026-04-02), 19486140 v2 (2026-04-09), 19545786 v3 (2026-04-12), **19722019** v4 (2026-04-23) |
| 19 | 10.5281/zenodo.19486629 | 19486630 v1 (2026-04-09), **19489276** v1.1 (2026-04-09) |
| 20 | 10.5281/zenodo.19722236 | **19722237** v1 (2026-04-23) |
| 21 | 10.5281/zenodo.19722697 | **19722698** v1 (2026-04-23) |
| 22 | 10.5281/zenodo.20321417 | **20321418** (2026-05-21) |
| 23 | 10.5281/zenodo.20245544 | 20245545 v1.0 (2026-05-16), **20287850** v1.1 (2026-05-19) |

Cite the concept DOI when the latest version is wanted and the version DOI
when the exact text matters.

## Licence

Apache-2.0. See `LICENSE`.
