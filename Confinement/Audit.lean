/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The audit of the confinement library. The build fails if any theorem under `Confinement` depends
on anything beyond `propext`, `Classical.choice` and `Quot.sound`.
-/
import Confinement.AreaLaw
import Confinement.GaugeInvariance
import Confinement.Instances
import FisherLorentz.AxiomGate

#print axioms Confinement.expansion_bound
#print axioms Confinement.term_vanish_general
#print axioms Confinement.slab_law
#print axioms Confinement.polyakov_general
#print axioms Confinement.polyakov_SU
#print axioms Confinement.area_law_general
#print axioms Confinement.area_law_SU
#print axioms Confinement.area_law_SU_window
#print axioms Confinement.area_law_SU_exp
#print axioms Confinement.partition_pos
#print axioms Confinement.area_law_compact
#print axioms Confinement.area_law_U1
#print axioms Confinement.area_law_Z2
#print axioms Confinement.term_vanish_swap
#print axioms Confinement.clustering_general
#print axioms Confinement.clustering_SU
#print axioms Confinement.mass_gap_plaquette_SU
#print axioms Confinement.partition_pos_general
#print axioms Confinement.rectangle_gauge
#print axioms Confinement.Qv_gauge
#print axioms Confinement.Qh_gauge

#assert_standard_axioms_in Confinement
