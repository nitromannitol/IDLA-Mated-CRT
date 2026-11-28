import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMap
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionCellSide

/-!
# The reconstruction map of the local configurations is Borel

The map `coneRecon` (`MatedCRT/FirstPass/Derived/ConeConfigReconstructionMap.lean`) reads a local
configuration off the outer data `(e, μ)` and the residues `r`. Here we prove
`measurable_coneRecon`: it is measurable on the space of marked phase vectors.

The proof is by composition. The capped measure is a Borel function of the measure; the inverse
mass clock is measurable jointly in the parameter and the (measurable) time at which it is read
(an infimum over the rationals of a conditional on a measurable comparison); the masses of the two
time blocks are measurable by `LatticeProb.measurable_measure_image_Icc`; the validity of a label
is a finite conjunction of measurable inequalities; the point `e (t)` at a measurable time is
measurable since evaluation is continuous; and the frontier-side count is
`measurable_cellSideCount_endpoints` at four measurable times. A map out of the space of marked
phase vectors is measurable as soon as it is measurable on each coordinate count.
-/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace MatedCRT

open LatticeProb.LQG (massClockInv)

section Pieces

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The capping of a measure to `closedBall 0 M` is a Borel map of the measure. -/
theorem measurable_cappedMeasure (M : ℝ) : Measurable (cappedMeasure M) := by
  change Measurable fun μ : Measure ℂ =>
    if μ (closedBall (0 : ℂ) M) < ⊤ then μ.restrict (closedBall (0 : ℂ) M) else 0
  exact Measurable.ite
    (measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const)
    (measurable_restrict_of_measurableSet measurableSet_closedBall) measurable_const

/-- A random curve evaluated at a random time is measurable. -/
theorem measurable_curve_eval {e : Ω → C(ℝ, ℂ)} (he : Measurable e) {T : Ω → ℝ}
    (hT : Measurable T) : Measurable fun ω => e ω (T ω) :=
  continuous_eval.measurable.comp (he.prodMk hT)

/-- The inverse mass clock, read at a measurable time, is measurable in the parameter. -/
theorem measurable_massClockInv_comp {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → ℂ} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => massClockInv (μ ω) (L ω) (s ω) := by
  unfold massClockInv
  refine Measurable.ereal_toReal (Measurable.iInf fun q => ?_)
  exact Measurable.ite
    (measurableSet_lt hs (LatticeProb.LQG.measurable_massClock hμ hfin hLc hLm q))
    measurable_const measurable_const

theorem measurable_posBlockTime (a M : ℝ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => posBlockTime a M (e ω) (μ ω) (s ω) := by
  unfold posBlockTime
  refine measurable_const.add ?_
  exact measurable_massClockInv_comp (μ := fun ω => cappedMeasure M (μ ω))
    ((measurable_cappedMeasure M).comp hμ)
    (fun ω => (inferInstance : IsFiniteMeasureOnCompacts (cappedMeasure M (μ ω))))
    (L := fun ω t => e ω (a + t))
    (fun ω => (e ω).continuous.comp (continuous_const.add continuous_id))
    (fun t => measurable_curve_eval he (T := fun _ => a + t) measurable_const) hs

theorem measurable_negBlockTime (a M : ℝ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => negBlockTime a M (e ω) (μ ω) (s ω) := by
  unfold negBlockTime
  refine measurable_const.add ?_
  exact measurable_massClockInv_comp (μ := fun ω => cappedMeasure M (μ ω))
    ((measurable_cappedMeasure M).comp hμ)
    (fun ω => (inferInstance : IsFiniteMeasureOnCompacts (cappedMeasure M (μ ω))))
    (L := fun ω t => e ω (-a + t))
    (fun ω => (e ω).continuous.comp (continuous_const.add continuous_id))
    (fun t => measurable_curve_eval he (T := fun _ => -a + t) measurable_const) hs

theorem measurable_reconTime (a M : ℝ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) (ℓ : ℤ) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => reconTime a M (e ω) (μ ω) ℓ (s ω) := by
  by_cases h : ℓ ≤ 0
  · simp only [reconTime, h, ↓reduceIte]
    exact measurable_negBlockTime a M he hμ hs
  · simp only [reconTime, h, ↓reduceIte]
    exact measurable_posBlockTime a M he hμ hs

theorem measurable_posBlockMass (a L M : ℝ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) :
    Measurable fun ω => posBlockMass a L M (e ω) (μ ω) := by
  unfold posBlockMass
  by_cases hal : a ≤ L
  · exact (LatticeProb.measurable_measure_image_Icc (μ := fun ω => cappedMeasure M (μ ω))
      ((measurable_cappedMeasure M).comp hμ)
      (fun ω => (inferInstance : IsFiniteMeasureOnCompacts (cappedMeasure M (μ ω))))
      (L := fun ω => ⇑(e ω)) (fun ω => (e ω).continuous)
      (fun t => measurable_curve_eval he (T := fun _ => t) measurable_const) hal).ennreal_toReal
  · simp only [Icc_eq_empty hal, image_empty, measure_empty, ENNReal.toReal_zero]
    exact measurable_const

theorem measurable_negBlockMass (a L M : ℝ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) :
    Measurable fun ω => negBlockMass a L M (e ω) (μ ω) := by
  unfold negBlockMass
  by_cases hal : -L ≤ -a
  · exact (LatticeProb.measurable_measure_image_Icc (μ := fun ω => cappedMeasure M (μ ω))
      ((measurable_cappedMeasure M).comp hμ)
      (fun ω => (inferInstance : IsFiniteMeasureOnCompacts (cappedMeasure M (μ ω))))
      (L := fun ω => ⇑(e ω)) (fun ω => (e ω).continuous)
      (fun t => measurable_curve_eval he (T := fun _ => t) measurable_const) hal).ennreal_toReal
  · simp only [Icc_eq_empty hal, image_empty, measure_empty, ENNReal.toReal_zero]
    exact measurable_const

theorem measurable_reconRelLeft (n : ℕ) {r : Ω → Fin 2 → ℝ} (hr : Measurable r) (ℓ : ℤ) :
    Measurable fun ω => reconRelLeft n (r ω) ℓ := by
  have h0 : Measurable fun ω => r ω 0 := (measurable_pi_apply 0).comp hr
  have h1 : Measurable fun ω => r ω 1 := (measurable_pi_apply 1).comp hr
  by_cases h : ℓ ≤ 0
  · simp only [reconRelLeft, h, ↓reduceIte]
    exact (measurable_const.sub h0).div_const _
  · simp only [reconRelLeft, h, ↓reduceIte]
    exact (measurable_const.sub h1).div_const _

theorem measurable_reconRelRight (n : ℕ) {r : Ω → Fin 2 → ℝ} (hr : Measurable r) (ℓ : ℤ) :
    Measurable fun ω => reconRelRight n (r ω) ℓ := by
  have h0 : Measurable fun ω => r ω 0 := (measurable_pi_apply 0).comp hr
  have h1 : Measurable fun ω => r ω 1 := (measurable_pi_apply 1).comp hr
  by_cases h : ℓ ≤ 0
  · simp only [reconRelRight, h, ↓reduceIte]
    exact (measurable_const.sub h0).div_const _
  · simp only [reconRelRight, h, ↓reduceIte]
    exact (measurable_const.sub h1).div_const _

theorem measurableSet_reconValid (a L M : ℝ) (n : ℕ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) {r : Ω → Fin 2 → ℝ} (hr : Measurable r) (ℓ : ℤ) :
    MeasurableSet {ω | ReconValid a L M n (e ω) (μ ω) (r ω) ℓ} := by
  by_cases h : ℓ ≤ 0
  · simp only [ReconValid, h, ↓reduceIte]
    exact (measurableSet_lt (measurable_negBlockMass a L M he hμ).neg
      (measurable_reconRelLeft n hr ℓ)).inter
      (measurableSet_le (measurable_reconRelRight n hr ℓ) measurable_const)
  · simp only [ReconValid, h, ↓reduceIte]
    exact (measurableSet_le measurable_const (measurable_reconRelLeft n hr ℓ)).inter
      (measurableSet_lt (measurable_reconRelRight n hr ℓ) (measurable_posBlockMass a L M he hμ))

theorem measurable_cellSideCountInc {t : Ω → ℝ × ℝ × ℝ × ℝ} (ht : Measurable t)
    {e : Ω → C(ℝ, ℂ)} (he : Measurable e) :
    Measurable fun ω => cellSideCountInc (t ω).1 (t ω).2.1 (t ω).2.2.1 (t ω).2.2.2 (e ω) :=
  measurable_cellSideCount_endpoints.comp (ht.prodMk he)

/-- **The synthetic data are measurable** in a measurable parameter. -/
theorem measurable_reconData (a L M : ℝ) (n : ℕ) {e : Ω → C(ℝ, ℂ)} (he : Measurable e)
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) {r : Ω → Fin 2 → ℝ} (hr : Measurable r) :
    Measurable fun ω => reconData a L M n (e ω) (μ ω) (r ω) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun ℓ => ?_)
    (measurable_pi_iff.2 fun ℓ => measurable_pi_iff.2 fun ℓ' => ?_)
  · exact Measurable.ite (measurableSet_reconValid a L M n he hμ hr ℓ)
      (measurable_curve_eval he
        (measurable_reconTime a M he hμ ℓ (measurable_reconRelRight n hr ℓ)))
      measurable_const
  · refine Measurable.ite ((measurableSet_reconValid a L M n he hμ hr ℓ).inter
      (measurableSet_reconValid a L M n he hμ hr ℓ')) ?_ measurable_const
    by_cases h1 : ℓ = ℓ'
    · simp only [h1, ↓reduceIte]
      exact measurable_const
    · by_cases h2 : |ℓ - ℓ'| = 1
      · simp only [h1, h2, ↓reduceIte]
        exact measurable_const
      · simp only [h1, h2, ↓reduceIte]
        have hT : ∀ (ℓ₀ : ℤ) (s : Ω → ℝ), Measurable s →
            Measurable fun ω => reconTime a M (e ω) (μ ω) ℓ₀ (s ω) := fun ℓ₀ s hs =>
          measurable_reconTime a M he hμ ℓ₀ hs
        exact measurable_cellSideCountInc (t := fun ω =>
          (reconTime a M (e ω) (μ ω) (min ℓ ℓ') (reconRelLeft n (r ω) (min ℓ ℓ')),
            reconTime a M (e ω) (μ ω) (min ℓ ℓ') (reconRelRight n (r ω) (min ℓ ℓ')),
            reconTime a M (e ω) (μ ω) (max ℓ ℓ') (reconRelLeft n (r ω) (max ℓ ℓ')),
            reconTime a M (e ω) (μ ω) (max ℓ ℓ') (reconRelRight n (r ω) (max ℓ ℓ'))))
          (((hT _ _ (measurable_reconRelLeft n hr _)).prodMk
            ((hT _ _ (measurable_reconRelRight n hr _)).prodMk
              ((hT _ _ (measurable_reconRelLeft n hr _)).prodMk
                (hT _ _ (measurable_reconRelRight n hr _)))))) he

end Pieces

/-- The residues of a marked phase vector are measurable on each fibre of the coordinate count. -/
theorem measurable_residuePair_mk (k : ℕ) {E : Type*} [MeasurableSpace E] :
    Measurable fun p : E × (Fin k → ℝ) =>
      residuePair (⟨k, p⟩ : LatticeProb.CountablePhaseSpace E) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : (i : ℕ) < k
  · simp only [residuePair, h, ↓reduceDIte]
    exact (measurable_pi_apply (⟨i, h⟩ : Fin k)).comp measurable_snd
  · simp only [residuePair, h, ↓reduceDIte]
    exact measurable_const

/-- **The reconstruction map of the local configurations is Borel.** -/
theorem measurable_coneRecon (α R a L M : ℝ) (n : ℕ) : Measurable (coneRecon α R a L M n) := by
  refine measurable_of_countablePhase fun k => ?_
  exact (measurable_localConfig (measurableSet_ball.diff measurableSet_closedBall)).comp
    (measurable_reconData a L M n (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) (measurable_residuePair_mk k))

end MatedCRT
