import MatedCRT.Draft.Section6

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

#check @MeasureTheory.measurePreserving_piFinSuccAbove
#check @MeasurableEquiv.piFinSuccAbove_symm_apply
#check @Fin.insertNth_zero'
#check @MeasureTheory.MeasurePreserving.lintegral_comp_emb
#check @MeasureTheory.lintegral_prod
#check @measurable_to_countable'
#check @measurable_from_nat
#check @MeasureTheory.meas_ge_le_lintegral_div
#check @Set.ncard_insert_of_notMem
#check @MeasurableSet.const
#check @List.ofFn_succ
#check @MeasureTheory.prob_compl_eq_one_sub
#check @Set.Countable.measurableSet
#check @Set.to_countable
#check @measurable_pi_lambda
#check @MeasureTheory.lintegral_indicator_const
#check @ENNReal.ofReal_div_of_pos
#check @Real.add_one_le_exp
#check @Nat.find_eq_iff
#check @ENNReal.ofReal_pow
#check @Set.ncard_le_ncard
#check @MeasureTheory.measure_union_le
#check @MeasureTheory.lintegral_mono
#check @MeasureTheory.lintegral_const_mul
#check @MeasureTheory.lintegral_mul_const
#check @ENNReal.ofReal_add
#check @ENNReal.ofReal_sub
#check @tendsto_of_tendsto_of_tendsto_of_le_of_le
#check @Set.Finite.insert
#check @Set.ncard_eq_zero
#check @Fin.cons_succ
#check @MeasurableSet.iUnion
#check @MeasureTheory.measure_mono
example (m : ℤ → ℤ → ℕ) (k : ℕ) (a : Fin k → ℤ) : IsProbabilityMeasure (MatedCRT.walkersLaw m a) := by
  unfold MatedCRT.walkersLaw; infer_instance
example : MeasurableSingletonClass ((Fin 3) → ℤ) := inferInstance
example : MeasurableSingletonClass (ℕ → ℤ) := inferInstance
example (s : Set (Fin 3 → ℤ)) : MeasurableSet s := (Set.to_countable s).measurableSet
example : Countable (Option ℤ) := inferInstance
