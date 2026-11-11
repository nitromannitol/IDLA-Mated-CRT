import MatedCRT.Draft.Section6

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

#print HarmonicBalls.PolyHighProb
#check @MatedCRT.IsLQGMeasure
#print MatedCRT.IsLQGMeasure
#check @Monotone.measure_iUnion
#check @MeasureTheory.measure_iUnion_eq_iSup
#check @MeasureTheory.measure_union_add_inter
#check @MeasureTheory.measure_biUnion_finset₀
#check @Set.Infinite.exists_subset_card_eq
#check @IsCompact.image
#check @MeasureTheory.Measure.bind_apply
#check @MeasureTheory.lintegral_mono
#check @Metric.diam_le_of_forall_dist_le
#check @Metric.dist_le_diam_of_mem
#check @IsCompact.isBounded
#check @MeasureTheory.ae_iff
