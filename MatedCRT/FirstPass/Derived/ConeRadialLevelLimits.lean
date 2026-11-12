import MatedCRT.FirstPass.Derived.ConeRadialDivergence
import MatedCRT.FirstPass.Derived.ConeScaleRadiusSpec
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLogMajorantProof
import LatticeProb.Prob.ContinuousPathLaw

/-!
# Almost sure regularity of the radial level function of a quantum cone

For a `γ`-quantum cone the radial level function `f s = h_{e^s}(0) + Q s` is almost surely continuous on `ℝ`
(continuity of the circle averages), tends to `+∞` at `+∞` (its outer part is `B̂_s + (Q - γ) s` with `B̂` the
conditioned Brownian motion, `frozenConeRadialDivergenceCorrected_holds`) and to `-∞` at `-∞` (its inner part is
`B_t - (Q - γ) t` for a standard Brownian motion `B`, by the Brownian strong law `B_t / t → 0`).

The limit events are not measurable for the product σ-algebra of `ℝ≥0 → ℝ`.  They are tested at nonnegative
rational times (`RisesRat`, `FallsRat`: countable operations on coordinates), and continuity of the circle averages
upgrades the rational-time statements to limits along the reals.  Combined with `coneScaleRadius_spec` this gives the
almost sure well-definedness of the cone scale radius `R_b`.
-/

open MeasureTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- `x s + Q s → +∞`, tested at nonnegative rational times. -/
def RisesRat (Q : ℝ) (x : ℝ≥0 → ℝ) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ q : ℚ≥0, (N : ℝ) ≤ ((q : ℝ≥0) : ℝ) →
    (M : ℝ) < x (q : ℝ≥0) + Q * ((q : ℝ≥0) : ℝ)

/-- `x t - Q t → -∞`, tested at nonnegative rational times. -/
def FallsRat (Q : ℝ) (x : ℝ≥0 → ℝ) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ q : ℚ≥0, (N : ℝ) ≤ ((q : ℝ≥0) : ℝ) →
    x (q : ℝ≥0) - Q * ((q : ℝ≥0) : ℝ) < -(M : ℝ)

lemma measurableSet_risesRat (Q : ℝ) : MeasurableSet {x : ℝ≥0 → ℝ | RisesRat Q x} := by
  have hset : {x : ℝ≥0 → ℝ | RisesRat Q x} = ⋂ M : ℕ, ⋃ N : ℕ, ⋂ q : ℚ≥0,
      ⋂ (_ : (N : ℝ) ≤ ((q : ℝ≥0) : ℝ)),
        {x : ℝ≥0 → ℝ | (M : ℝ) < x (q : ℝ≥0) + Q * ((q : ℝ≥0) : ℝ)} := by
    ext x
    simp only [RisesRat, Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [hset]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const ((measurable_pi_apply _).add_const _)

lemma measurableSet_fallsRat (Q : ℝ) : MeasurableSet {x : ℝ≥0 → ℝ | FallsRat Q x} := by
  have hset : {x : ℝ≥0 → ℝ | FallsRat Q x} = ⋂ M : ℕ, ⋃ N : ℕ, ⋂ q : ℚ≥0,
      ⋂ (_ : (N : ℝ) ≤ ((q : ℝ≥0) : ℝ)),
        {x : ℝ≥0 → ℝ | x (q : ℝ≥0) - Q * ((q : ℝ≥0) : ℝ) < -(M : ℝ)} := by
    ext x
    simp only [FallsRat, Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [hset]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun _ =>
      measurableSet_lt (((measurable_pi_apply _)).sub_const _) measurable_const

lemma risesRat_of_forall {Q : ℝ} {x : ℝ≥0 → ℝ}
    (h : ∀ M : ℕ, ∃ T : ℝ, ∀ s : ℝ≥0, T ≤ (s : ℝ) → (M : ℝ) < x s + Q * (s : ℝ)) : RisesRat Q x := by
  intro M
  obtain ⟨T, hT⟩ := h M
  refine ⟨⌈T⌉₊, fun q hq => hT _ ?_⟩
  exact (Nat.le_ceil T).trans hq

lemma fallsRat_of_forall {Q : ℝ} {x : ℝ≥0 → ℝ}
    (h : ∀ M : ℕ, ∃ T : ℝ, ∀ s : ℝ≥0, T ≤ (s : ℝ) → x s - Q * (s : ℝ) < -(M : ℝ)) : FallsRat Q x := by
  intro M
  obtain ⟨T, hT⟩ := h M
  refine ⟨⌈T⌉₊, fun q hq => hT _ ?_⟩
  exact (Nat.le_ceil T).trans hq

/-- A nonnegative rational number in a nonempty open set of `(a, ∞)`, `a ≥ 0`. -/
lemma exists_nnrat_mem_open {U : Set ℝ} (hU : IsOpen U) {a s : ℝ} (ha : 0 ≤ a) (hs : a < s)
    (hsU : s ∈ U) : ∃ q : ℚ≥0, a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) ∈ U := by
  have hV : IsOpen (U ∩ Ioi a) := hU.inter isOpen_Ioi
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open hV ⟨s, hsU, hs⟩
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := ha.trans (le_of_lt hr.2)
  have hr0' : 0 ≤ r := by exact_mod_cast hr0
  have key : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (r : ℝ) := by
    have e : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((r.toNNRat : ℚ≥0) : ℝ) := rfl
    rw [e]
    exact_mod_cast Rat.coe_toNNRat r hr0'
  exact ⟨r.toNNRat, by rw [key]; exact hr.2, by rw [key]; exact hr.1⟩

/-- A continuous function that exceeds `M` at all large nonnegative rationals, for every `M`, tends to `+∞`. -/
lemma tendsto_atTop_of_risesRat {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ M : ℕ, ∃ N : ℕ, ∀ q : ℚ≥0, (N : ℝ) ≤ ((q : ℝ≥0) : ℝ) → (M : ℝ) < g ((q : ℝ≥0) : ℝ)) :
    Tendsto g atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨N, hN⟩ := h ⌈M⌉₊
  refine ⟨(N : ℝ) + 1, fun s hs => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : g s < (⌈M⌉₊ : ℝ) := hlt.trans_le (Nat.le_ceil M)
  have hU : IsOpen (g ⁻¹' Iio (⌈M⌉₊ : ℝ)) := isOpen_Iio.preimage hg
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_mem_open hU (a := (N : ℝ)) (Nat.cast_nonneg N)
    (by linarith) hlt'
  exact absurd (hN q hq1.le) (not_lt.mpr (le_of_lt hq2))

/-- A continuous function that is below `-M` at the negatives of all large nonnegative rationals, for every `M`,
tends to `-∞` at `-∞`. -/
lemma tendsto_atBot_of_fallsRat {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ M : ℕ, ∃ N : ℕ, ∀ q : ℚ≥0, (N : ℝ) ≤ ((q : ℝ≥0) : ℝ) →
      g (-((q : ℝ≥0) : ℝ)) < -(M : ℝ)) :
    Tendsto g atBot atBot := by
  have h' : Tendsto (fun t => -g (-t)) atTop atTop :=
    tendsto_atTop_of_risesRat ((hg.comp continuous_neg).neg) (fun M => by
      obtain ⟨N, hN⟩ := h M
      exact ⟨N, fun q hq => by have := hN q hq; linarith⟩)
  have h2 : Tendsto (fun s => -(-g (-(-s)))) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (h'.comp tendsto_neg_atBot_atTop)
  simpa using h2

/-- Marginal transfer, inner path: if a measurable set of paths is almost surely hit by `t ↦ B_t + γ t` for a
standard Brownian motion `B`, then almost surely the inner radial path `t ↦ h_{e^{-t}}(0)` of the cone lies in it. -/
lemma ae_radial_fst_mem {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) {A : Set (ℝ≥0 → ℝ)} (hA : MeasurableSet A)
    (hBM : ∀ᵐ w ∂(brownianMotion 0), (fun t : ℝ≥0 => w t + γ * (t : ℝ)) ∈ A) :
    ∀ᵐ ω ∂P, (fun u : ℝ≥0 => hcirc ω (Real.exp (-(u : ℝ))) 0) ∈ A := by
  obtain ⟨ν, ⟨_hνP, -⟩, hν⟩ := h.radial_law
  have hmeas : ∀ (r : ℝ), 0 < r → ∀ z : ℂ, Measurable fun ω => hcirc ω r z :=
    fun r hr z => h.measurable_circle r z hr
  have hX : Measurable (fun ω (u : ℝ≥0) => hcirc ω (Real.exp (-(u : ℝ))) 0) :=
    Measurable.of_eval fun u => hmeas _ (Real.exp_pos _) 0
  have hR : Measurable (fun ω => radialProcess (hcirc ω)) := by
    unfold radialProcess
    exact Measurable.prodMk hX (Measurable.of_eval fun s => hmeas _ (Real.exp_pos _) 0)
  have hdrift : Measurable (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ)) :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess t).add_const _
  unfold quantumConeRadialLaw at hν
  set μ₁ := (brownianMotion 0).map (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ))
  have hμ₁prob : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff (μ := brownianMotion 0) hdrift.aemeasurable).2 inferInstance
  have hfst : (fun ω (u : ℝ≥0) => hcirc ω (Real.exp (-(u : ℝ))) 0) =
      Prod.fst ∘ (fun ω => radialProcess (hcirc ω)) := rfl
  have hmass : P.map (fun ω (u : ℝ≥0) => hcirc ω (Real.exp (-(u : ℝ))) 0) Set.univ = 1 := by
    rw [Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hmarg : P.map (fun ω (u : ℝ≥0) => hcirc ω (Real.exp (-(u : ℝ))) 0) = μ₁ := by
    have hsec : ((ν.map (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s - γ * (s : ℝ))) Set.univ) = 1 := by
      rw [hfst, ← Measure.map_map measurable_fst hR, hν, Measure.map_fst_prod,
        Measure.smul_apply, smul_eq_mul, measure_univ (μ := μ₁), mul_one] at hmass
      exact hmass
    rw [hfst, ← Measure.map_map measurable_fst hR, hν, Measure.map_fst_prod, hsec, one_smul]
  have h1 : ∀ᵐ f ∂(P.map (fun ω (u : ℝ≥0) => hcirc ω (Real.exp (-(u : ℝ))) 0)), f ∈ A := by
    rw [hmarg]
    exact (MeasureTheory.ae_map_iff hdrift.aemeasurable hA).mpr hBM
  exact (MeasureTheory.ae_map_iff hX.aemeasurable hA).mp h1

/-- Marginal transfer, outer path: if a measurable set of paths is almost surely hit by `s ↦ B̂_s - γ s` for
every law `ν` of the conditioned Brownian motion, then almost surely the outer radial path
`s ↦ h_{e^s}(0)` of the cone lies in it. -/
lemma ae_radial_snd_mem {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) {A : Set (ℝ≥0 → ℝ)} (hA : MeasurableSet A)
    (hν : ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
      ∀ᵐ w ∂ν, (fun s : ℝ≥0 => w s - γ * (s : ℝ)) ∈ A) :
    ∀ᵐ ω ∂P, (fun s : ℝ≥0 => hcirc ω (Real.exp (s : ℝ)) 0) ∈ A := by
  obtain ⟨ν, hνC, hνlaw⟩ := h.radial_law
  have hνP : IsProbabilityMeasure ν := hνC.1
  have hmeas : ∀ (r : ℝ), 0 < r → ∀ z : ℂ, Measurable fun ω => hcirc ω r z :=
    fun r hr z => h.measurable_circle r z hr
  have hX : Measurable (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (s : ℝ)) 0) :=
    Measurable.of_eval fun s => hmeas _ (Real.exp_pos _) 0
  have hR : Measurable (fun ω => radialProcess (hcirc ω)) := by
    unfold radialProcess
    exact Measurable.prodMk (Measurable.of_eval fun u => hmeas _ (Real.exp_pos _) 0) hX
  have hdrift : Measurable (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ)) :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess t).add_const _
  have hdrift2 : Measurable (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s - γ * (s : ℝ)) :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess t).sub_const _
  unfold quantumConeRadialLaw at hνlaw
  set μ₁ := (brownianMotion 0).map (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ))
  have hμ₁prob : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff (μ := brownianMotion 0) hdrift.aemeasurable).2 inferInstance
  have hsnd : (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (s : ℝ)) 0) =
      Prod.snd ∘ (fun ω => radialProcess (hcirc ω)) := rfl
  have hmarg : P.map (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (s : ℝ)) 0) =
      ν.map (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s - γ * (s : ℝ)) := by
    rw [hsnd, ← Measure.map_map measurable_snd hR, hνlaw, Measure.map_snd_prod,
      measure_univ (μ := μ₁), one_smul]
  have h1 : ∀ᵐ f ∂(P.map (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (s : ℝ)) 0)), f ∈ A := by
    rw [hmarg]
    exact (MeasureTheory.ae_map_iff hdrift2.aemeasurable hA).mpr (hν ν hνC)
  exact (MeasureTheory.ae_map_iff hX.aemeasurable hA).mp h1

lemma lqgQ_sub_pos' {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 0 < lqgQ γ - γ := by
  unfold lqgQ
  have key : 2 / γ + γ / 2 - γ = (4 - γ ^ 2) / (2 * γ) := by
    field_simp
    ring
  rw [key]
  apply div_pos _ (by positivity)
  nlinarith

/-- **Almost sure regularity of the radial level function of a quantum cone.**  Almost surely the function
`s ↦ h_{e^s}(0)` is continuous on `ℝ` and `s ↦ h_{e^s}(0) + Q s` tends to `+∞` at `+∞` and to `-∞` at `-∞`. -/
theorem ae_coneRadialLevel {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Continuous (fun s : ℝ => hcirc ω (Real.exp s) 0) ∧
      Tendsto (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) atTop atTop ∧
      Tendsto (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) atBot atBot := by
  have hμ := lqgQ_sub_pos' hγ0 hγ2
  have hup : ∀ᵐ ω ∂P, (fun s : ℝ≥0 => hcirc ω (Real.exp (s : ℝ)) 0) ∈
      {x : ℝ≥0 → ℝ | RisesRat (lqgQ γ) x} := by
    refine ae_radial_snd_mem h (measurableSet_risesRat _) (fun ν hν => ?_)
    filter_upwards [frozenConeRadialDivergenceCorrected_holds γ hγ0 hγ2 ν hν] with w hw
    refine risesRat_of_forall (fun M => ?_)
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hw.eventually (eventually_gt_atTop (M : ℝ)))
    refine ⟨(T : ℝ), fun s hs => ?_⟩
    have := hT s (by exact_mod_cast hs)
    linarith
  have hdown : ∀ᵐ ω ∂P, (fun u : ℝ≥0 => hcirc ω (Real.exp (-(u : ℝ))) 0) ∈
      {x : ℝ≥0 → ℝ | FallsRat (lqgQ γ) x} := by
    refine ae_radial_fst_mem h (measurableSet_fallsRat _) ?_
    have hsub := MatedCRT.Sec1.ae_tendsto_div_real_of_isBrownianReal
      MatedCRT.Sec1.brownianMotion_zero_isBrownianReal
      (fun t => ContinuousPath.measurable_coordinateProcess t)
    filter_upwards [hsub] with w hw
    have hneg : Tendsto (fun t : ℝ => (fun t : ℝ => -w t.toNNReal) t / t) atTop (𝓝 0) := by
      have := hw.neg
      simpa [neg_div] using this
    have hlim := LatticeProb.ContinuousPathLaw.tendsto_add_pos_drift_of_sublinear
      (fun t : ℝ => -w t.toNNReal) (lqgQ γ - γ) hμ hneg
    refine fallsRat_of_forall (fun M => ?_)
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (eventually_gt_atTop (M : ℝ)))
    refine ⟨T, fun s hs => ?_⟩
    have := hT (s : ℝ) hs
    simp only [Real.toNNReal_coe] at this
    linarith
  filter_upwards [h.ae_continuousOn_circle, hup, hdown] with ω hcont hu hd
  have hF : Continuous (fun s : ℝ => hcirc ω (Real.exp s) 0) :=
    hcont.comp_continuous (f := fun s : ℝ => (Real.exp s, (0 : ℂ))) (by fun_prop)
      (fun s => ⟨Real.exp_pos s, mem_univ _⟩)
  have hg : Continuous (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) :=
    hF.add (continuous_const.mul continuous_id)
  refine ⟨hF, tendsto_atTop_of_risesRat hg (fun M => hu M), ?_⟩
  refine tendsto_atBot_of_fallsRat hg (fun M => ?_)
  obtain ⟨N, hN⟩ := hd M
  refine ⟨N, fun q hq => ?_⟩
  have := hN q hq
  simp only at this ⊢
  linarith

/-- **The cone scale radius is almost surely well defined** (eq:cone-scale-radius): almost surely `R_b > 0` is a
point of the level set and `h_r(0) + Q log r > γ⁻¹ log b` for every `r > R_b`. -/
theorem ae_coneScaleRadius_spec {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b ∧
      hcirc ω (coneScaleRadius γ (hcirc ω) b) 0 + lqgQ γ * Real.log (coneScaleRadius γ (hcirc ω) b)
        = γ⁻¹ * Real.log b ∧
      ∀ r : ℝ, coneScaleRadius γ (hcirc ω) b < r →
        γ⁻¹ * Real.log b < hcirc ω r 0 + lqgQ γ * Real.log r := by
  filter_upwards [ae_coneRadialLevel hγ0 hγ2 h] with ω hω
  exact coneScaleRadius_spec hω.1 hω.2.1 hω.2.2

end MatedCRT.FirstPass.Derived
