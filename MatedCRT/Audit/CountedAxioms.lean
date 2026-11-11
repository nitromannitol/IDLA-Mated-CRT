import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Closure.Chain42ConeLaw
import MatedCRT.FirstPass.Closure.Clean14And16LPNoSC
import MatedCRT.FirstPass.Closure.Clean2xLP
import MatedCRT.FirstPass.Closure.Clean42And5LP
import MatedCRT.FirstPass.Closure.Clean51And54
import MatedCRT.FirstPass.Closure.Clean61And71LP
import MatedCRT.FirstPass.Closure.Clean61And81
import MatedCRT.FirstPass.Closure.Clean71
import MatedCRT.FirstPass.Closure.Clean81Full
import MatedCRT.FirstPass.Closure.Clean81LP
import MatedCRT.FirstPass.Closure.CleanSec23LP
import MatedCRT.FirstPass.Closure.CleanSec456LP
import MatedCRT.FirstPass.Closure.Final14Full
import MatedCRT.FirstPass.Closure.Final14LP
import MatedCRT.FirstPass.Closure.Final22
import MatedCRT.FirstPass.Closure.Final23
import MatedCRT.FirstPass.Closure.H35CorrectedRewire
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.HSCRewire
import MatedCRT.FirstPass.Closure.LssDerived
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.Closure.Section7
import MatedCRT.FirstPass.LIClosed68Y
import MatedCRT.FirstPass.LPBridge.GFFExistence
import MatedCRT.FirstPass.Main
import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S2VG.Literature
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S2g.LawCode
import MatedCRT.FirstPass.S2g.LawCoded
import MatedCRT.FirstPass.S2i.GlobalFactor
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3c
import MatedCRT.FirstPass.S3c.CountableFamilies
import MatedCRT.FirstPass.S3i.LensClosed
import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.S6p
import MatedCRT.FirstPass.S6q
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure2
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure3
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure4
import MatedCRT.Proofs.Sec4.SubsequentialProperties.CircleAverage
import MatedCRT.Proofs.SecA.DiscreteDivergence
import MatedCRT.Proofs.SecA.Statements

/-!
#print axioms for every declaration counted in docs/campaign/COUNTED.md.
-/

#print axioms MatedCRT.closed_1_4_lp_noSC
#print axioms MatedCRT.closed_1_6_lp_noSC
#print axioms MatedCRT.closed_2_3_lp
#print axioms MatedCRT.closed_2_3_lit_noSC
#print axioms MatedCRT.closed_2_4_lp
#print axioms MatedCRT.closed_2_5_lp
#print axioms MatedCRT.closed_2_6_lp
#print axioms MatedCRT.closed_2_13_cellRewire
#print axioms MatedCRT.firstPass_2_17_ownBinders
#print axioms MatedCRT.closed_2_19_ownBinders
#print axioms MatedCRT.S3c.firstPass_3_1_faithful
#print axioms MatedCRT.closed_3_3_ownBinders
#print axioms MatedCRT.closed_3_4_ownBinders
#print axioms MatedCRT.closed_3_5_lp
#print axioms MatedCRT.closed_3_6_lp
#print axioms MatedCRT.closed_3_7_lp
#print axioms MatedCRT.closed_4_1_lp
#print axioms MatedCRT.FirstPassClosure.closed_4_2_lp
#print axioms MatedCRT.closed_4_3
#print axioms MatedCRT.closed_4_4
#print axioms MatedCRT.closed_4_5
#print axioms MatedCRT.firstPass_4_6_h35c
#print axioms MatedCRT.closed_4_7_ownBinders
#print axioms MatedCRT.closed_4_8_lp
#print axioms MatedCRT.FirstPassClosure.closed_5_1_lp
#print axioms MatedCRT.closed_5_2_ownBinders
#print axioms MatedCRT.closed_5_3_clean
#print axioms MatedCRT.FirstPassClosure.closed_5_4_clean
#print axioms MatedCRT.closed_6_1_lp
#print axioms MatedCRT.closed_6_4_lp
#print axioms MatedCRT.FirstPass64.firstPass_6_5_uniform
#print axioms MatedCRT.LIClosed68Y.firstPass_6_7
#print axioms MatedCRT.LIClosed68Y.firstPass_6_8
#print axioms MatedCRT.LIClosed68Y.firstPass_6_9
#print axioms MatedCRT.closed_6_10_lp
#print axioms MatedCRT.closed_7_1_lp
#print axioms MatedCRT.closed_7_2
#print axioms MatedCRT.closed_7_3
#print axioms MatedCRT.closed_8_1_lp
#print axioms MatedCRT.FirstPassClosure.closed_5_3_lp
#print axioms MatedCRT.FirstPassClosure.closed_5_4_lp
#print axioms MatedCRT.discreteDivergenceTheorem
#print axioms MatedCRT.discreteBasicPropertiesGeneral
#print axioms MatedCRT.discreteLaplacianBoundGeneral
#print axioms MatedCRT.discreteConservationOfMassGeneral
#print axioms MatedCRT.firstPassMain_1_4_full
#print axioms MatedCRT.firstPassMain_1_6_full
#print axioms MatedCRT.FirstPassClosure.closed_5_1_cellRewire
#print axioms MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_closed
#print axioms MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_closed2
#print axioms MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_closed3
#print axioms MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_closed4
#print axioms MatedCRT.GFFExistence.exists_harmonicBalls_isWholePlaneGFF
#print axioms MatedCRT.S2VG.LitExistence
#print axioms MatedCRT.ratPoint
#print axioms MatedCRT.rationalGridPoint
#print axioms MatedCRT.closed_1_4_full
#print axioms MatedCRT.closed_1_4_lp
#print axioms MatedCRT.closed_1_6_full
#print axioms MatedCRT.closed_1_6_lp
#print axioms MatedCRT.closed_2_13
#print axioms MatedCRT.closed_2_13_lp
#print axioms MatedCRT.closed_2_2_lit
#print axioms MatedCRT.closed_2_2_ownBinders
#print axioms MatedCRT.closed_2_3_lit
#print axioms MatedCRT.closed_3_1
#print axioms MatedCRT.closed_3_1_lp
#print axioms MatedCRT.closed_3_5
#print axioms MatedCRT.closed_3_5_ownBinders
#print axioms MatedCRT.closed_4_2_clean
#print axioms MatedCRT.closed_4_8_corrected_ownBinders
#print axioms MatedCRT.FirstPassClosure.closed_5_1
#print axioms MatedCRT.FirstPassClosure.closed_5_1_clean
#print axioms MatedCRT.closed_6_10
#print axioms MatedCRT.closed_6_10_ownBinders
#print axioms MatedCRT.closed_6_1_clean
#print axioms MatedCRT.closed_7_1_clean
#print axioms MatedCRT.closed_8_1_full
#print axioms MatedCRT.coneGlobalFamilyFactor_ownBinders
#print axioms MatedCRT.coneGlobalFamilyFactor_proved
#print axioms MatedCRT.coneScaleInvarianceCoded_ownBinders
#print axioms MatedCRT.firstPassMain_1_4
#print axioms MatedCRT.firstPassMain_1_6
#print axioms MatedCRT.firstPass_2_4_ownBinders
#print axioms MatedCRT.Phase2.firstPass_2_5_canonical_p2
#print axioms MatedCRT.firstPass_2_5_ownBinders
#print axioms MatedCRT.firstPass_2_6_coded_of_globalFamilyFactor
#print axioms MatedCRT.Phase2.firstPass_2_6_corrected_p2
#print axioms MatedCRT.firstPass_2_6_ownBinders
#print axioms MatedCRT.S3c.firstPass_3_1_countable
#print axioms MatedCRT.firstPass_3_1_ownBinders
#print axioms MatedCRT.FirstPass36.firstPass_3_6_closed
#print axioms MatedCRT.firstPass_3_6_ownBinders
#print axioms MatedCRT.firstPass_3_7_ownBinders
#print axioms MatedCRT.firstPass_4_1
#print axioms MatedCRT.firstPass_4_1_coneLaw_h35c
#print axioms MatedCRT.firstPass_4_1_coneLaw_ownBinders
#print axioms MatedCRT.firstPass_4_1_ownBinders
#print axioms MatedCRT.firstPass_4_1_ownBinders_counted
#print axioms MatedCRT.firstPass_4_1_ownBinders_h35c
#print axioms MatedCRT.firstPass_4_2_final
#print axioms MatedCRT.firstPass_4_2_final_h35c
#print axioms MatedCRT.firstPass_4_6_corrected
#print axioms MatedCRT.firstPass_5_4
#print axioms MatedCRT.firstPass_6_1_corrected
#print axioms MatedCRT.FirstPass64.firstPass_6_4_uniform
#print axioms MatedCRT.firstPass_7_1
#print axioms MatedCRT.volumeGrowthStmt_of_berestyckiGwynne
#print axioms MatedCRT.closed_1_4_lp_noSC_noSup
#print axioms MatedCRT.closed_1_6_lp_noSC_noSup
#print axioms MatedCRT.firstPassMain_1_4_full_noSup
#print axioms MatedCRT.firstPassMain_1_6_full_noSup
#print axioms MatedCRT.closed_6_1_lp_noSup
#print axioms MatedCRT.closed_8_1_lp_noSup
#print axioms MatedCRT.FirstPassClosure.closed_5_1_lp_noSup
#print axioms MatedCRT.FirstPassClosure.closed_5_1_cellRewire_noSup
