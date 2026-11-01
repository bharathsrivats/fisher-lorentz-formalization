import FisherLorentz.AxiomGate
import YMStatement.Statement
import YMStatement.NonVacuity
import YMStatement.NonVacuity2

open YMStatement

#check @YangMillsExistenceAndMassGap
#print axioms YMStatement.tensor
#print axioms YMStatement.tensor_apply
#print axioms YMStatement.not_AFProfile_of_le_rpow
#print axioms YMStatement.not_AFProfile_of_ge_pow
#print axioms YMStatement.not_bounded_generator_of_AFProfile
#print axioms YMStatement.commute_of_exp_commute
#print axioms YMStatement.not_hasSimpleLieAlgebra_of_comm
#print axioms YMStatement.circle_not_isCompactSimpleGaugeGroup
#print axioms YMStatement.trivialSchwinger_not_hasFiniteMass
#print axioms YMStatement.not_hasFiniteMass_of_invariantAlong
#print axioms YMStatement.not_agreesWithAF_of_kernel_le
#print axioms YMStatement.not_agreesWithAF_of_kernel_ge
#print axioms YMStatement.not_agreesWithAF_of_boundedTransfer
#print axioms YMStatement.trivial_not_witness
#print axioms YMStatement.witness_not_invariantAlong
#print axioms YMStatement.witness_kernel_not_le
#print axioms YMStatement.witness_not_boundedTransfer
#print axioms YMStatement.circle_outside_domain
#print axioms YMStatement.YangMillsExistenceAndMassGap
#print axioms YMStatement.so3_isSimple
#print axioms YMStatement.rhoSO3_lieAlgebraCarrier
#print axioms YMStatement.eq_of_exp_smul_eq
#print axioms YMStatement.hasSimpleLieAlgebra_SO3gen
#check (YMStatement.hasSimpleLieAlgebra_SO3gen : YMStatement.HasSimpleLieAlgebra YMStatement.SO3gen)
#print axioms YMStatement.lieAlgebraCarrier_eq_so3
#print axioms YMStatement.isCompact_unitary3
#print axioms YMStatement.isPreconnected_SO3gen
#print axioms YMStatement.SO3bar_isCompactSimpleGaugeGroup
#print axioms YMStatement.exists_compactSimpleGaugeGroup
#print axioms YMStatement.specialize_SO3
#check (YMStatement.exists_compactSimpleGaugeGroup : ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G), YMStatement.IsCompactSimpleGaugeGroup G)

#assert_standard_axioms_in YMStatement
