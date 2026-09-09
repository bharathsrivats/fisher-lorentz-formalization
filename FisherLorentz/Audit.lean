/-
# Audit gate

A theorem whose axiom list contains `sorryAx` is NOT proven. A clean result
lists exactly `[propext, Classical.choice, Quot.sound]`, the three standard
axioms of Lean's logic. This file prints the axiom dependency of every
result in the library. It is the gate; a successful build is not.
-/
import FisherLorentz.Basic
import FisherLorentz.Conformal
import FisherLorentz.Gudermannian
import FisherLorentz.Identities
import FisherLorentz.Modular
import FisherLorentz.Moebius
import FisherLorentz.NaturalGradient
import FisherLorentz.QuantumComputation
import FisherLorentz.Retention
import FisherLorentz.SpeedLimits
import FisherLorentz.ThirdLaw
import FisherLorentz.ThomasWigner

namespace FisherLorentz

-- Basic
#print axioms pPlus_pos
#print axioms pMinus_pos
#print axioms pPlus_mul_pMinus
#print axioms fisherInfo_eq_gammaSq
#print axioms fisherInfo_eq_inv_four_mul_prod
#print axioms gammaSq_ge

-- Conformal
#print axioms bkForm_eq_four_gammaSq_mul_buresForm
#print axioms conformal_radial
#print axioms conformal_angular
#print axioms conformal_factor_unique
#print axioms hasDerivAt_buresDist
#print axioms hasDerivAt_artanh
#print axioms two_buresDist_eq_gd_bkDist

-- Gudermannian
#print axioms tanh_two_mul
#print axioms tanh_eq_double
#print axioms sin_two_arctan
#print axioms gd_mem_Icc
#print axioms gd_eq_arcsin_tanh
#print axioms arcsin_eq_gd_artanh

-- Identities
#print axioms hillOccupancy_mem
#print axioms hillFisher_eq
#print axioms hillFisher_midpoint
#print axioms wfVariance_eq_inv_gammaSq
#print axioms gamma_sq_eq_gammaSq
#print axioms jeffreysDensity_eq_sqrt_fisher

-- Modular
#print axioms modRatio_eq
#print axioms modRatio_eq_exp_two_rapidity
#print axioms tanh_rapidity
#print axioms gammaSq_eq_cosh_sq
#print axioms cast_p_ne
#print axioms cast_q_ne
#print axioms rhoDiag_mul_inv
#print axioms inv_rhoDiag
#print axioms modOp_E01
#print axioms modOp_E10
#print axioms modOp_E00
#print axioms modOp_E11
#print axioms modOp_nontrivial_eigenvalue

-- Moebius
#print axioms one_add_mul_pos
#print axioms one_sub_einsteinAdd_sq
#print axioms einsteinAdd_mem
#print axioms fisherInfo_einsteinAdd
#print axioms gammaSq_einsteinAdd
#print axioms einsteinAdd_comm

-- NaturalGradient
#print axioms logitToVisibility_mem
#print axioms fisherLogit_eq_inv
#print axioms step_ratio

-- QuantumComputation
#print axioms hasDerivAt_artanh_eq_fisherInfo
#print axioms groverVisibility_mem
#print axioms gammaSq_groverVisibility
#print axioms batteryRatio_eq_gd
#print axioms gammaSq_zeno_threshold
#print axioms zeno_threshold_mem

-- Retention
#print axioms logFactor_eq_two_artanh
#print axioms retention_eq_avg_div
#print axioms retention_rapidity
#print axioms retention_numerator_eq

-- SpeedLimits
#print axioms gammaSq_mul_one_sub_sq
#print axioms cramerRao_floor
#print axioms log_two_lt_one
#print axioms log_two_pos
#print axioms planckianVisibility_mem
#print axioms gammaSq_planckian
#print axioms planckian_floor
#print axioms energyPrecision_forms

-- ThirdLaw
#print axioms buresDist_le_pi_div_four
#print axioms bkDist_cooling
#print axioms bkDist_cooling_unbounded
#print axioms cooling_cost_contrast
#print axioms bkDist_halving

-- ThomasWigner
#print axioms sinh_artanh_eq
#print axioms cosh_artanh_eq
#print axioms tanh_eq_sinh_two_div
#print axioms tanh_half_rapidity
#print axioms ratio_rescale
#print axioms twTanHalf_eq
#print axioms twTanHalf_orthogonal

end FisherLorentz