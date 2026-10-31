/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The audit of the confinement library. The build fails if any theorem under `Confinement` uses an
axiom other than `propext`, `Classical.choice` and `Quot.sound`.
-/
import Confinement.AreaLaw
import Confinement.GaugeInvariance
import Confinement.SpecialUnitary
import FisherLorentz.AxiomGate

#print axioms Confinement.expansion_bound
#print axioms Confinement.term_vanish
#print axioms Confinement.area_law_general
#print axioms Confinement.area_law_SU
#print axioms Confinement.area_law_SU_window
#print axioms Confinement.area_law_SU_exp
#print axioms Confinement.partition_pos
#print axioms Confinement.rectangle_gauge
#print axioms Confinement.Qv_gauge
#print axioms Confinement.Qh_gauge

#assert_standard_axioms_in Confinement
