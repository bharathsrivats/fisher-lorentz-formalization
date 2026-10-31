/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The centre twist. Multiply the vertical links of one slab over a set `C` of sites by a central
element `z`. The a priori measure does not notice. A horizontal plaquette contains no vertical
link, and a vertical plaquette contains two in the same slab, so its holonomy changes only if
exactly one of its legs lies over `C`. A Wilson loop whose two vertical sides lie one over `C`
and one off it picks up the central character.
-/
import Confinement.Bonds

open MeasureTheory

namespace Confinement

variable {n L Lt : ℕ} {G : Type*} [Group G]

open Classical in
/-- The coordinate map of the twist. -/
noncomputable def twistCoord (z : G) (C : Set (Space n L)) (t : ZMod Lt) :
    Link n L Lt → G → G
  | Sum.inl _ => id
  | Sum.inr (v, t') => if t' = t ∧ v ∈ C then (z * ·) else id

/-- The twist of a configuration. -/
noncomputable def twist (z : G) (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G) :
    Link n L Lt → G :=
  fun l => twistCoord z C t l (U l)

lemma hor_twist (z : G) (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G) (x t' μ) :
    hor (twist z C t U) x t' μ = hor U x t' μ := rfl

open Classical in
lemma ver_twist (z : G) (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G) (x t') :
    ver (twist z C t U) x t' = if t' = t ∧ x ∈ C then z * ver U x t' else ver U x t' := by
  simp only [ver, twist, twistCoord]
  split_ifs <;> rfl

lemma Qh_twist (z : G) (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G)
    (p : HP n L Lt) : Qh (twist z C t U) p = Qh U p := rfl

lemma hline_twist (z : G) (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G) (x t' μ R) :
    hline (twist z C t U) x t' μ R = hline U x t' μ R := rfl

/-- A list product in which exactly one factor carries a central element. -/
lemma prod_twist_once {α : Type*} [DecidableEq α] {z : G} (hz : ∀ g : G, z * g = g * z)
    (f : α → G) (a : α) (l : List α) (hl : l.Nodup) (ha : a ∈ l) :
    (l.map fun i => if i = a then z * f i else f i).prod = z * (l.map f).prod := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hbl := List.nodup_cons.mp hl
    by_cases hb : b = a
    · subst hb
      have hrest : (l.map fun i => if i = b then z * f i else f i) = l.map f :=
        List.map_congr_left fun i hi => if_neg (fun h : i = b => hbl.1 (h ▸ hi))
      simp [hrest, mul_assoc]
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hb
        · exact h
      simp only [List.map_cons, List.prod_cons, if_neg hb, ih hbl.2 ha']
      rw [← mul_assoc, ← hz, mul_assoc]

section central

variable {z : G} (hz : ∀ g : G, z * g = g * z)
include hz

/-- A vertical plaquette is unchanged unless exactly one leg lies over `C` in the twisted slab. -/
lemma Qv_twist (C : Set (Space n L)) (t : ZMod Lt) (U : Link n L Lt → G) (v : Space n L)
    (t' : ZMod Lt) (μ : Fin n) (h : t' = t → (v ∈ C ↔ v + e μ ∈ C)) :
    Qv (twist z C t U) (v, t', μ) = Qv U (v, t', μ) := by
  classical
  simp only [Qv, hor_twist, ver_twist]
  by_cases ht : t' = t
  · by_cases hv : v ∈ C
    · have hv' : v + e μ ∈ C := (h ht).mp hv
      simp only [ht, hv, hv', and_self, if_true]
      generalize ver U v t = a
      generalize hor U v (t + 1) μ = b
      generalize ver U (v + e μ) t = c
      generalize (hor U v t μ)⁻¹ = d
      calc z * a * b * (z * c)⁻¹ * d = z * (a * b * c⁻¹) * z⁻¹ * d := by group
        _ = (a * b * c⁻¹) * z * z⁻¹ * d := by rw [hz]
        _ = a * b * c⁻¹ * d := by group
    · have hv' : v + e μ ∉ C := fun hh => hv ((h ht).mpr hh)
      simp [ht, hv, hv']
  · simp [ht]

/-- The vertical side over `C` picks up one factor of `z`, provided the twisted slab is one of
the `T ≤ Lₜ` slabs it crosses. -/
lemma vline_twist_mem {T i₀ : ℕ} (hT : T ≤ Lt) (hi : i₀ < T) (C : Set (Space n L))
    (t₀ : ZMod Lt) (U : Link n L Lt → G) {v : Space n L} (hv : v ∈ C) :
    vline (twist z C (t₀ + (i₀ : ZMod Lt)) U) v t₀ T = z * vline U v t₀ T := by
  classical
  unfold vline
  have hcongr : ((List.range T).map fun i : ℕ =>
        ver (twist z C (t₀ + (i₀ : ZMod Lt)) U) v (t₀ + (i : ZMod Lt)))
      = (List.range T).map fun i : ℕ => if i = i₀ then z * ver U v (t₀ + (i : ZMod Lt))
          else ver U v (t₀ + (i : ZMod Lt)) := by
    refine List.map_congr_left fun i hi' => ?_
    rw [ver_twist]
    have hiT := List.mem_range.mp hi'
    have hiff : (t₀ + (i : ZMod Lt) = t₀ + (i₀ : ZMod Lt) ∧ v ∈ C) ↔ i = i₀ := by
      constructor
      · rintro ⟨h, -⟩
        have h2 : (i : ZMod Lt) = (i₀ : ZMod Lt) := add_left_cancel h
        rw [ZMod.natCast_eq_natCast_iff'] at h2
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
      · rintro rfl
        exact ⟨rfl, hv⟩
    simp only [hiff]
  rw [hcongr]
  exact prod_twist_once hz (fun i : ℕ => ver U v (t₀ + (i : ZMod Lt))) i₀ (List.range T)
    List.nodup_range (List.mem_range.mpr hi)

omit hz in
/-- The vertical side off `C` does not change. -/
lemma vline_twist_not_mem (C : Set (Space n L)) (t : ZMod Lt) (t₀ : ZMod Lt) (T : ℕ)
    (U : Link n L Lt → G) {v : Space n L} (hv : v ∉ C) :
    vline (twist z C t U) v t₀ T = vline U v t₀ T := by
  classical
  unfold vline
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [ver_twist, if_neg (fun h => hv h.2)]

/-- The Wilson loop picks up `z`. -/
lemma rectangle_twist {T i₀ : ℕ} (hT : T ≤ Lt) (hi : i₀ < T) (C : Set (Space n L))
    (t₀ : ZMod Lt) (U : Link n L Lt → G) {x : Space n L} (μ : Fin n) {R : ℕ} (hx : x ∈ C)
    (hy : x + (R : ZMod L) • (e μ : Space n L) ∉ C) :
    rectangle (twist z C (t₀ + (i₀ : ZMod Lt)) U) x t₀ μ R T = z * rectangle U x t₀ μ R T := by
  unfold rectangle
  rw [vline_twist_mem hz hT hi C t₀ U hx, vline_twist_not_mem C _ t₀ T U hy, hline_twist,
    hline_twist]
  simp only [mul_assoc]

end central

section measure

variable [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul G]

/-- The twist preserves the product of the single-link measures. -/
lemma measurePreserving_twist (μ₀ : Measure G) [SigmaFinite μ₀] [μ₀.IsMulLeftInvariant]
    (z : G) (C : Set (Space n L)) (t : ZMod Lt) :
    MeasurePreserving (twist z C t) (linkMeasure (n := n) (L := L) (Lt := Lt) μ₀)
      (linkMeasure μ₀) := by
  classical
  refine measurePreserving_pi (fun _ => μ₀) (fun _ => μ₀) fun l => ?_
  rcases l with q | ⟨v, t'⟩
  · exact MeasurePreserving.id μ₀
  · simp only [twistCoord]
    split_ifs
    · exact measurePreserving_mul_left μ₀ z
    · exact MeasurePreserving.id μ₀

end measure

end Confinement
