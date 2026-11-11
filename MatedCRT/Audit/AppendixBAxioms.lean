import MatedCRT.FirstPass.Closure.AppendixBRewire
import MatedCRT.FirstPass.Closure.Clean51NoSC

/-!
# Axiom audit of the Appendix B occupation identity and of the forms derived from it

The occupation identity of Appendix B (the clock of Liouville Brownian motion killed on leaving a disc has
occupation measure the Green function of the disc against the Liouville measure) is proved in
`MatedCRT/Proofs/Sec3/KilledOccupation/` for the reference quantum cone and transferred to every certified model in
`MatedCRT/FirstPass/Closure/AppendixBRewire.lean`. This file prints the axioms of the main steps of that chain, of the
forms of Theorems 1.4 and 1.6 that derive the occupation identity instead of binding it, and of the form of
Proposition 5.1 without the cluster strong compatibility binder.

Each line must print only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms MatedCRT.KilledOccupation.exists_strictMono_ae_limClockFun_eq_clock_cone
#print axioms MatedCRT.KilledOccupation.ae_limClockKernel_Iic_cone
#print axioms MatedCRT.KilledOccupation.ae_gmcGreenMeasure_cone
#print axioms MatedCRT.KilledOccupation.lintegral_limClockOccupationMeasure_of_Iic_eq
#print axioms MatedCRT.KilledOccupation.ae_lintegral_clock_occupation_eq_green_cone
#print axioms MatedCRT.KilledOccupation.rescaled_occupation_green_identity_of_clock
#print axioms MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_of_coneGFFLaw
#print axioms MatedCRT.coneUnitDiskGFFLaw_of_fieldLaw
#print axioms MatedCRT.frozenLBMGreenOccupationRescaled_of_fieldLaw
#print axioms MatedCRT.CertifiedReferenceModelCoreNoOccupation.toCore_of_fieldLaw
#print axioms MatedCRT.CertifiedReferenceModelCoreNoOccupation.toModel_of_fieldLaw
#print axioms MatedCRT.closed_1_4_derivedOccupation
#print axioms MatedCRT.closed_1_6_derivedOccupation
#print axioms MatedCRT.FirstPassClosure.closed_5_1_lp_noSup_noSC
