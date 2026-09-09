# fisher-lorentz-formalization

Machine-checked proofs, in **Lean 4 + Mathlib**, of results from the
published and preprint corpus of **Bharath G. Srivats**.

**77 results across twelve modules. Zero `sorry`.** Every theorem is
verified to depend only on the three standard axioms of Lean's logic.

The central identity is

```
I(V) = γ²(V) = 1/(1 − V²),    V = 2p − 1,    η = artanh V
```

the Fisher information of a binary measurement in the visibility coordinate,
equal to the squared Lorentz factor.

---

## The corpus formalised here

### Peer-reviewed

1. **Srivats, B. G.** "Fisher Information as the Squared Lorentz Factor:
   Conformal Equivalence of the Bures and Beltrami–Klein Metrics on the Qubit
   Bloch Ball." *Quantum Reports* **8**(3), 68 (2026).
   doi:[10.3390/quantum8030068](https://doi.org/10.3390/quantum8030068)
2. **Srivats, B. G.** "The Hill Coefficient as Fisher Information: An
   Information-Theoretic Identity for Allosteric Cooperativity."
   *BioSystems* **266**, 105847 (2026).
   doi:[10.1016/j.biosystems.2026.105847](https://doi.org/10.1016/j.biosystems.2026.105847)
3. **Srivats, B. G.** "The Squared Lorentz Factor in Quantum Computation:
   Grover Search, Quantum Batteries, and the Zeno Effect."
   *Next Research* **10**, 101888 (2026).
   doi:[10.1016/j.nexres.2026.101888](https://doi.org/10.1016/j.nexres.2026.101888)
4. **Srivats, B. G.** "Three Fisher–Rao Identities on the Binary Statistical
   Manifold: Jeffreys Uniqueness, the Gudermannian Bridge, and Isotropic
   Retention." *European Journal of Pure and Applied Mathematics* **19**(2),
   Article 7819 (2026).
   doi:[10.29020/nybg.ejpam.v19i2.7819](https://doi.org/10.29020/nybg.ejpam.v19i2.7819)

### Under review

5. **Srivats, B. G.** "A Modular Speed Limit on the Qubit: Bloch Precession,
   Saturation, Channel Data-Processing, and the Vanishing of Modular Flow at
   Pure States." Verification code and data:
   doi:[10.5281/zenodo.20287850](https://doi.org/10.5281/zenodo.20287850)
6. **Srivats, B. G.** "Lorentz Kinematics of Sequential Binary Qubit
   Measurements: Thomas–Wigner Composition and SLD Saturation from the
   Fisher–Lorentz Identity."
7. **Srivats, B. G.** "Möbius Covariance, Effect Classification, and a
   Holographic Correspondence for Qubit Fisher Information."
8. **Srivats, B. G.** "Observer Limits and Thermodynamics of Binary Quantum
   Measurement: A Lawvere Obstruction and an Energy–Precision Bound from the
   Fisher–Lorentz Identity."
9. **Srivats, B. G.** "Fisher-Information Speed Limits: Ito, Ito–Dechant,
   Cramér–Rao and Margolus–Levitin Unified by the Squared Lorentz Factor."
10. **Srivats, B. G.** "An Information-Geometric Identity for the
    Wright–Fisher Diffusion: Genetic Drift as Inverse Fisher Information on
    the Allele-Frequency Manifold."
11. **Srivats, B. G.** "Thermodynamic Consequences of the Identity
    I(V) = γ²: A Cooling-Cost Divergence Theorem and a Falsifiable
    Entropy–Visibility Law."

### Preprints

12. **Srivats, B. G.** "Fisher Information Is the Squared Lorentz Factor: Why
    the Qubit Is Special." Zenodo (2026).
    doi:[10.5281/zenodo.19363449](https://doi.org/10.5281/zenodo.19363449)
13. **Srivats, B. G.** "The Algebra of the Qubit: Fourteen Theorems on
    I(V) = γ²(V)." Zenodo (2026).
    doi:[10.5281/zenodo.19653530](https://doi.org/10.5281/zenodo.19653530)
14. **Srivats, B. G.** "From Measurement to Reality: I(V) = γ²(V) and the
    Geometry of Binary Distinction." Zenodo (2026).
    doi:[10.5281/zenodo.19486140](https://doi.org/10.5281/zenodo.19486140)
15. **Srivats, B. G.** "The Lorentz Factor in Binary Classification: Natural
    Gradient Descent and the Fisher–Lorentz Identity." Zenodo (2026).
    doi:[10.5281/zenodo.19722237](https://doi.org/10.5281/zenodo.19722237)
16. **Srivats, B. G.** "Why Current AI Cannot Be Conscious: A Thermodynamic
    Criterion from the Fisher–Lorentz Identity." Zenodo (2026).
    doi:[10.5281/zenodo.19489276](https://doi.org/10.5281/zenodo.19489276)

---

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

No claim is made about any of these.

---

## The audit gate

A Lean file can compile with `sorry` in it. **Compilation is therefore not
the gate.** `FisherLorentz/Audit.lean` runs `#print axioms` on all 77
results; each must report exactly

```
[propext, Classical.choice, Quot.sound]
```

Any occurrence of `sorryAx` means the result is not proven. As of this commit
all 77 are clean, and the source contains no `sorry`, no `axiom`, and no
`native_decide`. CI re-runs the gate on every push.

## Build

```bash
lake exe cache get
lake build
```

Lean **4.33.0** (pinned in `lean-toolchain`), Mathlib **v4.33.0**. The
Mathlib cache is ~7.5 GB; build outside any synced folder.

## A note on the DOIs

Reference 13 appears in the source corpus under two Zenodo DOIs,
`10.5281/zenodo.19653530` and `10.5281/zenodo.19639617`. The former is used
here. This has not been reconciled against the live Zenodo record and should
be confirmed.

## Licence

Apache-2.0. See `LICENSE`.
