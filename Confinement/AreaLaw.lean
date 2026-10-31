/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

**Wilson's area law** on the torus `(ℤ/L)ⁿ × ℤ/Lₜ`, for any gauge group with a nontrivial central
character. The proof has three steps and no analysis. Write each vertical plaquette weight as a
constant times `1 + h` with `h ≥ 0` and expand. A subset of vertical plaquettes that fails to join
the two sides of the loop in some slab contributes zero, by the centre twist of that slab. The
remaining subsets contain a lifted path in every slab, and these are counted by the pointwise bound
`h ≤ p (1 + h)`, with `p = 1 - exp (-2 |J|)`.
-/
import Confinement.Twist

open MeasureTheory Finset

namespace Confinement

variable {n L Lt : ℕ} {G : Type*} [Group G]

section weights

/-- The nonnegative part of a vertical plaquette weight. -/
noncomputable def hP (χ : G → ℂ) (J : ℝ) (p : VP n L Lt) (U : Link n L Lt → G) : ℝ :=
  Real.exp (J * (χ (Qv U p)).re + |J|) - 1

/-- The weight of the horizontal plaquettes. -/
noncomputable def Hwt [NeZero L] [NeZero Lt] (χ : G → ℂ) (J : ℝ) (U : Link n L Lt → G) : ℝ :=
  Real.exp (J * actionH χ U)

variable {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ)
include hχ

lemma re_bounds (g : G) : -1 ≤ (χ g).re ∧ (χ g).re ≤ 1 := by
  have h := (Complex.abs_re_le_norm (χ g)).trans (hχ g)
  exact abs_le.mp h

lemma exponent_bounds (g : G) : 0 ≤ J * (χ g).re + |J| ∧ J * (χ g).re + |J| ≤ 2 * |J| := by
  have h := re_bounds hχ g
  have h2 : |J * (χ g).re| ≤ |J| := by
    rw [abs_mul]
    have : |(χ g).re| ≤ 1 := abs_le.mpr h
    nlinarith [abs_nonneg J]
  have h3 := abs_le.mp h2
  constructor <;> linarith

lemma hP_nonneg (p : VP n L Lt) (U : Link n L Lt → G) : 0 ≤ hP χ J p U := by
  have := (exponent_bounds hχ J (Qv U p)).1
  have h1 := Real.one_le_exp this
  simp only [hP]
  linarith

lemma hP_le (p : VP n L Lt) (U : Link n L Lt → G) :
    hP χ J p U ≤ Real.exp (2 * |J|) - 1 := by
  have := (exponent_bounds hχ J (Qv U p)).2
  have h1 := Real.exp_le_exp.mpr this
  simp only [hP]
  linarith

/-- The pointwise inequality that replaces all of the analysis. -/
lemma hP_le_mul (p : VP n L Lt) (U : Link n L Lt → G) :
    hP χ J p U ≤ (1 - Real.exp (-(2 * |J|))) * (1 + hP χ J p U) := by
  have hb := (exponent_bounds hχ J (Qv U p)).2
  set s := J * (χ (Qv U p)).re + |J| with hs
  have h1 : Real.exp (s - 2 * |J|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : Real.exp (-(2 * |J|)) * Real.exp s = Real.exp (s - 2 * |J|) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [hP, ← hs]
  nlinarith

end weights

section measurability

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

lemma measurable_hor (x : Space n L) (t : ZMod Lt) (μ : Fin n) :
    Measurable fun U : Link n L Lt → G => hor U x t μ := measurable_pi_apply _

lemma measurable_ver (x : Space n L) (t : ZMod Lt) :
    Measurable fun U : Link n L Lt → G => ver U x t := measurable_pi_apply _

lemma measurable_Qh (p : HP n L Lt) : Measurable fun U : Link n L Lt → G => Qh U p := by
  obtain ⟨x, t, μ, ν⟩ := p
  simp only [Qh]
  exact (((measurable_hor _ _ _).mul (measurable_hor _ _ _)).mul (measurable_hor _ _ _).inv).mul
    (measurable_hor _ _ _).inv

lemma measurable_Qv (p : VP n L Lt) : Measurable fun U : Link n L Lt → G => Qv U p := by
  obtain ⟨x, t, μ⟩ := p
  simp only [Qv]
  exact (((measurable_ver _ _).mul (measurable_hor _ _ _)).mul (measurable_ver _ _).inv).mul
    (measurable_hor _ _ _).inv

lemma measurable_list_prod {α Ω : Type*} [MeasurableSpace Ω] (l : List α) (f : α → Ω → G)
    (hf : ∀ a, Measurable (f a)) : Measurable fun ω => (l.map fun a => f a ω).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf a).mul ih

lemma measurable_rectangle (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (R T : ℕ) :
    Measurable fun U : Link n L Lt → G => rectangle U x t₀ μ R T := by
  have hv : ∀ v : Space n L, Measurable fun U : Link n L Lt → G => vline U v t₀ T := fun v =>
    measurable_list_prod _ _ fun i => measurable_ver _ _
  have hh : ∀ t : ZMod Lt, Measurable fun U : Link n L Lt → G => hline U x t μ R := fun t =>
    measurable_list_prod _ _ fun j => measurable_hor _ _ _
  simp only [rectangle]
  exact (((hv _).mul (hh _)).mul (hv _).inv).mul (hh _).inv

variable [NeZero L] [NeZero Lt] {χ : G → ℂ} (hχm : Measurable χ) (J : ℝ)
include hχm

lemma measurable_hP (p : VP n L Lt) : Measurable (hP χ J p : (Link n L Lt → G) → ℝ) := by
  unfold hP
  exact (((Complex.measurable_re.comp (hχm.comp (measurable_Qv p))).const_mul J).add_const _
    |>.exp).sub_const _

lemma measurable_actionH : Measurable (actionH χ : (Link n L Lt → G) → ℝ) := by
  unfold actionH
  exact Finset.measurable_sum _ fun p _ => Complex.measurable_re.comp (hχm.comp (measurable_Qh p))

lemma measurable_actionV : Measurable (actionV χ : (Link n L Lt → G) → ℝ) := by
  unfold actionV
  exact Finset.measurable_sum _ fun p _ => Complex.measurable_re.comp (hχm.comp (measurable_Qv p))

lemma measurable_Hwt : Measurable (Hwt χ J : (Link n L Lt → G) → ℝ) := by
  unfold Hwt
  exact ((measurable_actionH hχm).const_mul J).exp

end measurability

section main

variable [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

instance (μ₀ : Measure G) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (linkMeasure (n := n) (L := L) (Lt := Lt) μ₀) := by
  unfold linkMeasure; infer_instance

variable {μ₀ : Measure G} [IsProbabilityMeasure μ₀] [μ₀.IsMulLeftInvariant]
variable {χ : G → ℂ} (hχm : Measurable χ) (hχ : ∀ g, ‖χ g‖ ≤ 1)
variable {z : G} (hz : ∀ g : G, z * g = g * z) {ζ : ℂ} (hζ : ζ ≠ 1) (hχz : ∀ g, χ (z * g) = ζ * χ g)

include hχm hz hζ in
/-- **The centre twist kills every bad term.** Let `W` pick up `ζ` under the twist of slab `t` over
any set containing `x` and missing `y`. If `A` does not join `x` to `y` in slab `t`, its term
vanishes. -/
theorem term_vanish_general (hL : 3 ≤ L) (x y : Space n L) (t : ZMod Lt)
    (W : (Link n L Lt → G) → ℂ) (hWm : Measurable W)
    (hWtw : ∀ (C : Set (Space n L)) (U : Link n L Lt → G), x ∈ C → y ∉ C →
      W (twist z C t U) = ζ * W U)
    (J : ℝ) (A : Finset (VP n L Lt)) (hnr : ¬ (bondGraph A t).Reachable x y) :
    ∫ U, W U * ((Hwt χ J U * ∏ p ∈ A, hP χ J p U : ℝ) : ℂ) ∂(linkMeasure μ₀) = 0 := by
  classical
  set C : Set (Space n L) := {v | (bondGraph A t).Reachable x v} with hC
  have hxC : x ∈ C := SimpleGraph.Reachable.refl x
  have hyC : y ∉ C := hnr
  set g : (Link n L Lt → G) → ℂ := fun U => W U *
        ((Hwt χ J U * ∏ p ∈ A, hP χ J p U : ℝ) : ℂ) with hg
  -- the integrand transforms by the central character
  have hinv : ∀ U, g (twist z C t U) = ζ * g U := by
    intro U
    have hH : Hwt χ J (twist z C t U) = Hwt χ J U := by
      simp only [Hwt, actionH, Qh_twist]
    have hp : ∀ p ∈ A, hP χ J p (twist z C t U) = hP χ J p U := by
      rintro ⟨v, t', ν⟩ hp
      have hQ : Qv (twist z C t U) (v, t', ν) = Qv U (v, t', ν) := by
        refine Qv_twist hz C t U v t' ν fun ht' => ?_
        rw [ht'] at hp
        have hadj : (bondGraph A t).Adj v (v + e ν) := bondGraph_adj_of_mem hL hp
        constructor
        · intro hv
          exact SimpleGraph.Reachable.trans hv hadj.reachable
        · intro hv
          exact SimpleGraph.Reachable.trans hv hadj.symm.reachable
      simp only [hP, hQ]
    have hprod : ∏ p ∈ A, hP χ J p (twist z C t U) = ∏ p ∈ A, hP χ J p U :=
      Finset.prod_congr rfl hp
    simp only [hg, hH, hprod]
    rw [hWtw C U hxC hyC]
    ring
  -- `g` is measurable
  have hgm : Measurable g := by
    refine hWm.mul (Complex.measurable_ofReal.comp ?_)
    exact (measurable_Hwt hχm J).mul
      (Finset.measurable_prod _ fun p _ => measurable_hP hχm J p)
  -- change of variables
  have hmp := measurePreserving_twist (n := n) (L := L) (Lt := Lt) μ₀ z C t
  have hmap : ∫ U, g U ∂(linkMeasure μ₀) = ∫ U, g (twist z C t U) ∂(linkMeasure μ₀) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hgm.aestronglyMeasurable
  have heq : ∫ U, g U ∂(linkMeasure μ₀) = ζ * ∫ U, g U ∂(linkMeasure μ₀) := by
    conv_lhs => rw [hmap]
    simp_rw [hinv]
    exact integral_const_mul _ _
  have h1 : (1 - ζ) * ∫ U, g U ∂(linkMeasure μ₀) = 0 := by
    rw [sub_mul, one_mul, ← heq, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hζ.symm)

set_option maxHeartbeats 1600000 in
include hχm hχ hz hζ in
/-- **The slab law.** Let `W` be bounded by one and pick up `ζ` under the twist of each of the
`T ≤ Lₜ` slabs `t₀ + i`, over any set containing `x` and missing `y`. If every path from `x` to `y`
has length at least `R`, and `2 n p < 1` with `p = 1 - exp (-2 |J|)`, then
`‖⟨W⟩‖ ≤ ((2 n p) ^ R / (1 - 2 n p)) ^ T`. -/
theorem slab_law (hL : 3 ≤ L) {R T : ℕ} (hT : T ≤ Lt) (x y : Space n L) (t₀ : ZMod Lt)
    (hlen : ∀ γ : (torusGraph n L).Path x y, R ≤ (γ : (torusGraph n L).Walk x y).length)
    (W : (Link n L Lt → G) → ℂ) (hWm : Measurable W) (hWb : ∀ U, ‖W U‖ ≤ 1)
    (hWtw : ∀ i : Fin T, ∀ (C : Set (Space n L)) (U : Link n L Lt → G), x ∈ C → y ∉ C →
      W (twist z C (t₀ + ((i : ℕ) : ZMod Lt)) U) = ζ * W U)
    (J : ℝ) (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs μ₀ χ J W‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ T := by
  classical
  set p : ℝ := 1 - Real.exp (-(2 * |J|)) with hpdef
  have hp0 : 0 ≤ p := by
    have : Real.exp (-(2 * |J|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg J])
    linarith
  have hp1 : p ≤ 1 := by
    have := Real.exp_pos (-(2 * |J|))
    linarith
  set P : Finset (VP n L Lt) := Finset.univ with hP'
  -- the slabs and the lifted paths
  let slab : Fin T → ZMod Lt := fun i => t₀ + ((i : ℕ) : ZMod Lt)
  have hslab : Function.Injective slab := by
    intro i j hij
    have h2 : ((i : ℕ) : ZMod Lt) = ((j : ℕ) : ZMod Lt) := add_left_cancel hij
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    exact Fin.ext h2
  let S : (Fin T → (torusGraph n L).Path x y) → Finset (VP n L Lt) := fun f =>
    Finset.univ.biUnion fun i => lift (slab i) ((f i : (torusGraph n L).Path x y) :
      (torusGraph n L).Walk x y)
  -- a weight bound for the horizontal part
  set CH : ℝ := Real.exp (|J| * ((Finset.univ : Finset (HP n L Lt)).filter
    (fun p => p.2.2.1 < p.2.2.2)).card) with hCH
  have hHle : ∀ U : Link n L Lt → G, Hwt χ J U ≤ CH := by
    intro U
    refine Real.exp_le_exp.mpr ?_
    have habs : |actionH χ U| ≤ ((Finset.univ : Finset (HP n L Lt)).filter
        (fun p => p.2.2.1 < p.2.2.2)).card := by
      unfold actionH
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ q ∈ (Finset.univ : Finset (HP n L Lt)).filter (fun p => p.2.2.1 < p.2.2.2),
          |(χ (Qh U q)).re| ≤ 1 := fun q _ => abs_le.mpr (re_bounds hχ _)
      simpa using Finset.sum_le_card_nsmul _ _ _ this
    calc J * actionH χ U ≤ |J * actionH χ U| := le_abs_self _
      _ = |J| * |actionH χ U| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  -- the expansion bound
  have hbound := expansion_bound (ν := linkMeasure (n := n) (L := L) (Lt := Lt) μ₀) P S
    (fun _ => Finset.subset_univ _) (fun p U => hP χ J p U) (Hwt χ J)
    W (p := p) (M := Real.exp (2 * |J|) - 1) (C := CH)
    (fun i _ => measurable_hP hχm J i) (measurable_Hwt hχm J)
    hWm
    (fun i _ U => hP_nonneg hχ J i U) (fun i _ U => hP_le hχ J i U)
    (fun i _ U => hP_le_mul hχ J i U) (fun U => (Real.exp_pos _).le) hHle hWb
    (by
      intro A _
      by_cases hall : ∀ i : Fin T, (bondGraph A (slab i)).Reachable x y
      · left
        have hpath : ∀ i : Fin T, ∃ γ : (torusGraph n L).Path x y,
            lift (slab i) (γ : (torusGraph n L).Walk x y) ⊆ A := by
          intro i
          obtain ⟨w⟩ := hall i
          let w' := w.toPath
          refine ⟨⟨(w' : (bondGraph A (slab i)).Walk x y).mapLe (bondGraph_le A (slab i)),
            w'.2.mapLe _⟩, ?_⟩
          exact lift_mapLe_subset hL _
        choose f hf using hpath
        refine ⟨f, ?_⟩
        intro q hq'
        obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hq'
        exact hf i hi
      · right
        obtain ⟨i, hi⟩ := not_forall.mp hall
        exact term_vanish_general hχm hz hζ hL x y (slab i) W hWm (hWtw i) J A hi)
  -- the sum over families of paths factorises
  have hS : ∑ f, p ^ (S f).card ≤ ((2 * (n : ℝ) * p) ^ R / (1 - 2 * (n : ℝ) * p)) ^ T := by
    have hterm : ∀ f : Fin T → (torusGraph n L).Path x y,
        p ^ (S f).card ≤ ∏ i, p ^ ((f i : (torusGraph n L).Path x y) :
          (torusGraph n L).Walk x y).length := by
      intro f
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_of_le_one hp0 hp1 ?_
      have hdisj : (↑(Finset.univ : Finset (Fin T)) : Set (Fin T)).PairwiseDisjoint fun i =>
          lift (slab i) ((f i : (torusGraph n L).Path x y) : (torusGraph n L).Walk x y) := by
        intro i _ j _ hij
        exact lift_disjoint (fun h => hij (hslab h)) _ _
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_le_sum fun i _ => length_le_card_lift _ _ (f i).2
    have hfac : ∑ f : Fin T → (torusGraph n L).Path x y, ∏ i, p ^ ((f i : (torusGraph n L).Path x y) :
          (torusGraph n L).Walk x y).length
        = (∑ γ : (torusGraph n L).Path x y, p ^ (γ : (torusGraph n L).Walk x y).length) ^ T :=
      (Fintype.sum_pow (fun γ : (torusGraph n L).Path x y =>
        p ^ (γ : (torusGraph n L).Walk x y).length) T).symm
    have hps := path_sum_le (L := L) (x := x) (y := y) hp0 hq hlen
    have hsum0 : 0 ≤ ∑ γ : (torusGraph n L).Path x y, p ^ (γ : (torusGraph n L).Walk x y).length :=
      Finset.sum_nonneg fun _ _ => pow_nonneg hp0 _
    exact (Finset.sum_le_sum fun f _ => hterm f).trans
      (hfac.le.trans (pow_le_pow_left₀ hsum0 hps T))
  -- back to the Gibbs weight
  set Z : ℝ := ∫ U, Hwt χ J U * ∏ q ∈ P, (1 + hP χ J q U) ∂(linkMeasure (n := n) (L := L) (Lt := Lt) μ₀)
    with hZ
  have hZ0 : 0 ≤ Z := integral_nonneg fun U => mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun q _ => by linarith [hP_nonneg hχ J q U])
  set c : ℝ := Real.exp (-(|J| * (Finset.card P : ℝ))) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hweight : ∀ U : Link n L Lt → G,
      wilsonWeight χ J U = c * (Hwt χ J U * ∏ q ∈ P, (1 + hP χ J q U)) := by
    intro U
    have h1 : ∏ q ∈ P, (1 + hP χ J q U) = Real.exp (J * actionV χ U + |J| * (Finset.card P : ℝ)) := by
      have : ∀ q ∈ P, 1 + hP χ J q U = Real.exp (J * (χ (Qv U q)).re + |J|) := fun q _ => by
        simp [hP]
      rw [Finset.prod_congr rfl this, ← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      congr 2
      ring
    rw [h1, wilsonWeight, Hwt, hc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hden : ∫ U, wilsonWeight χ J U ∂(linkMeasure (n := n) (L := L) (Lt := Lt) μ₀) = c * Z := by
    simp_rw [hweight]
    exact integral_const_mul _ _
  have hnum : ∫ U : Link n L Lt → G, W U * ((wilsonWeight χ J U : ℝ) : ℂ)
        ∂(linkMeasure μ₀)
      = (c : ℂ) * ∫ U, W U *
        ((Hwt χ J U * ∏ q ∈ P, (1 + hP χ J q U) : ℝ) : ℂ) ∂(linkMeasure μ₀) := by
    rw [← integral_const_mul]
    congr 1
    funext U
    rw [hweight]
    push_cast
    ring
  have hnn : 0 ≤ ((2 * (n : ℝ) * p) ^ R / (1 - 2 * (n : ℝ) * p)) ^ T := by
    have : 0 < 1 - 2 * (n : ℝ) * p := by linarith
    positivity
  unfold gibbs
  rw [hnum, hden, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc0.le,
    Real.norm_of_nonneg (mul_nonneg hc0.le hZ0)]
  by_cases hZz : Z = 0
  · simp [hZz, hnn]
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZz)
    rw [div_le_iff₀ (mul_pos hc0 hZpos)]
    have := hbound.trans (mul_le_mul_of_nonneg_right hS hZ0)
    nlinarith [mul_le_mul_of_nonneg_left this hc0.le]

include hχm hχ hz hζ hχz in
/-- **Wilson's area law, general form.** Let `G` carry a probability measure invariant under a
central element `z`, and `χ` a function bounded by one with `χ (z g) = ζ χ g`, `ζ ≠ 1`. Let
`p = 1 - exp (-2 |J|)` and `2 n p < 1`. For the `R × T` rectangle, `R ≤ L / 2`, `T ≤ Lₜ`,
`‖⟨χ(Q_ℓ)⟩‖ ≤ ((2 n p) ^ R / (1 - 2 n p)) ^ T`. -/
theorem area_law_general (hL : 3 ≤ L) {R T : ℕ} (hR : R ≤ L / 2) (hT : T ≤ Lt)
    (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (J : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs μ₀ χ J (fun U : Link n L Lt → G => χ (rectangle U x t₀ μ R T))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ T :=
  slab_law hχm hχ hz hζ hL hT x (x + (R : ZMod L) • (e μ : Space n L)) t₀
    (fun γ => length_ge hL μ x hR γ) (fun U : Link n L Lt → G => χ (rectangle U x t₀ μ R T))
    (hχm.comp (measurable_rectangle x t₀ μ R T)) (fun _ => hχ _)
    (fun i C U hx hy => by
      show χ (rectangle (twist z C (t₀ + ((i : ℕ) : ZMod Lt)) U) x t₀ μ R T) = _
      rw [rectangle_twist hz hT i.2 C t₀ U μ hx hy, hχz]) J hq

/-- The Polyakov line at `x`: the ordered product of the vertical links around the time circle. -/
def polyakov (U : Link n L Lt → G) (x : Space n L) : G := vline U x 0 Lt

include hχm hχ hz hζ hχz in
/-- **Polyakov loop correlators decay, for every temporal extent `Lₜ`.** For `x` and
`y = x + R e μ`, `R ≤ L / 2`, `‖⟨χ(P_x) conj χ(P_y)⟩‖ ≤ ((2 n p) ^ R / (1 - 2 n p)) ^ Lₜ`. So there
is no deconfined phase in the window, at any temperature. -/
theorem polyakov_general (hL : 3 ≤ L) {R : ℕ} (hR : R ≤ L / 2) (x : Space n L) (μ : Fin n) (J : ℝ)
    (hq : 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))) < 1) :
    ‖gibbs μ₀ χ J (fun U : Link n L Lt → G => χ (polyakov U x) *
        (starRingEnd ℂ) (χ (polyakov U (x + (R : ZMod L) • (e μ : Space n L)))))‖
      ≤ ((2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|)))) ^ R /
          (1 - 2 * (n : ℝ) * (1 - Real.exp (-(2 * |J|))))) ^ Lt := by
  refine slab_law hχm hχ hz hζ hL le_rfl x (x + (R : ZMod L) • (e μ : Space n L)) 0
    (fun γ => length_ge hL μ x hR γ)
    (fun U : Link n L Lt → G => χ (polyakov U x) *
        (starRingEnd ℂ) (χ (polyakov U (x + (R : ZMod L) • (e μ : Space n L))))) ?_ ?_ ?_ J hq
  · have hv : ∀ v : Space n L, Measurable fun U : Link n L Lt → G => polyakov U v := fun v =>
      measurable_list_prod _ _ fun i => measurable_ver _ _
    exact (hχm.comp (hv _)).mul (Complex.continuous_conj.measurable.comp (hχm.comp (hv _)))
  · intro U
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ (hχ _) (norm_nonneg _) (hχ _)
  · intro i C U hx hy
    simp only [polyakov]
    rw [vline_twist_mem hz le_rfl i.2 C 0 U hx, vline_twist_not_mem C _ 0 Lt U hy, hχz]
    ring

end main

end Confinement
