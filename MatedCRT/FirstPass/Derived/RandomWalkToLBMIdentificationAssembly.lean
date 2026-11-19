import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtDerived
import MatedCRT.FirstPass.Derived.LBMReversibilityOfUniformStart
import MatedCRT.FirstPass.Derived.MarkovTimeChangeRevuzUniqueDerived
import MatedCRT.FirstPass.Derived.AnnealedMedianLimitIdentified
import MatedCRT.FirstPass.Derived.MedianOfCdf
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputs
import MatedCRT.FirstPass.Derived.ValidApproximantBallBound
import MatedCRT.FirstPass.Derived.ReferenceBoundsForallGamma
import MatedCRT.FirstPass.Derived.GreenKernelUpperOfReference
import MatedCRT.FirstPass.Derived.CoreGffLowerOfLemma69
import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail

/-!
# Identification of the subsequential limits of the walk laws (Berestycki–Gwynne §7.1–7.4)

The identification hypothesis `hid` of `randomWalkToLBMStmt_of_identification` asks for Polish data `D` of the
environment and a measurable law field `Λ` such that every subsequential weak limit `ν` of the pairs
(data, interpolated quenched walk law) is the law of `(D, Λ D)`. Here the data are the field coordinates
`pairJ ⊤ H` of the environment together with a Borel coordinate `E` of the LQG measure `μ_h` (`μX (E ω) = μ_h`),
and `Λ` is the field of laws of the rescaled Liouville Brownian motion `lbmPathLawField γ`.

For a subsequential limit `ν` the argument of Berestycki–Gwynne (2020), §7.1–7.4, runs as follows.

* The data marginal of `ν` is the law of `D` (`map_fst_eq_map_of_tendsto_integral`).
* `μ_h` is invariant for the limiting family (Lemma 7.6, `ae_isInvariantFor_of_tendsto_law_of_uniformStart`), the
  limiting family is a Markovian time change of Brownian motion (Lemma 7.4, premise `hN5`), and so is the Liouville
  Brownian law field, with `μ_h` invariant, `μ_h ≠ 0` and a nonzero exit-time median (premise `hN8`).
* By the uniqueness of the time change with a given invariant measure (Proposition 7.10,
  `exists_measurable_timeScale_of_isMarkovTCBM_revuzUnique_derived`) the limiting family is a linear time change of
  the Liouville Brownian law field with a random constant; by Lemma 7.18 (premise `hN9`) the constant `c₀` is
  deterministic.
* The normalization: the exit time of `B_{1/2}` under the origin mixture of `ν` has median `1` (the lower median of
  the annealed walk exit time is `m^interp_ε / m_ε → 1`), while under the origin mixture of the law of `(D, Λ D)` it
  also has median `1`; the time change divides medians by `c₀` (`originPathLaw_eq_map_timeScalePath`,
  `medianOf_exitCdf_map_timeScalePath`), so `c₀ = 1`. The regular exit and the strict increase of the exit-time
  distribution function beyond its median transfer through the time change (`regularExit_timeScalePath`).
* Hence `ν`-almost surely the limiting family is `Λ` of the data, and `ν` is the law of `(D, Λ D)`.

## Main statements

* `hid_of_markovLimit`: the identification hypothesis `hid`, from the premises `hK3` (a Borel coordinate of `μ_h`
  with Lévy–Prokhorov continuous cutoff measures), `hN8`, `hN5`, `hN9` and the Brownian outward excursion at the exit
  time (`hexit`).
* `randomWalkToLBMStmt_of_markovLimit`: Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the same premises.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open MatedCRT.TruncatedLaws (RegularExit)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

/-! ### Linear time changes of paths -/

/-- **Regular exit under a linear time change.** If a continuous path exits `U` regularly, so does the time-changed
path `t ↦ g (c t)` for `c ≠ 0`. -/
theorem regularExit_timeScalePath {U : Set ℂ} {c : ℝ≥0} (hc : c ≠ 0) {g : ContinuousPath ℂ}
    (hg : RegularExit U ⇑g) : RegularExit U ⇑(MatedCRT.timeScalePath c g) := by
  have hT : pathExitTime U ⇑(MatedCRT.timeScalePath c g) = pathExitTime U ⇑g / c :=
    MatedCRT.exitTime_timeScalePath U hc g
  by_cases htop : pathExitTime U ⇑g = ⊤
  · refine Or.inl ?_
    rw [hT, htop]
    exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top
  · have hfreq : ∃ᶠ t in 𝓝[>] (pathExitTime U ⇑g).toNNReal, g t ∉ closure U := Or.resolve_left hg htop
    refine Or.inr ?_
    have hTa : (pathExitTime U ⇑(MatedCRT.timeScalePath c g)).toNNReal =
        (pathExitTime U ⇑g).toNNReal / c := by
      rw [hT, ← ENNReal.coe_toNNReal htop, ← ENNReal.coe_div hc, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rw [hTa]
    set a : ℝ≥0 := (pathExitTime U ⇑g).toNNReal with ha
    have hcpos : 0 < c := pos_iff_ne_zero.2 hc
    have htend : Tendsto (fun t : ℝ≥0 => t / c) (𝓝[>] a) (𝓝[>] (a / c)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.div_const c).tendsto a).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      show a / c < t / c
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right (show a < t from ht) (inv_pos.2 hcpos)
    refine htend.frequently (p := fun s => (MatedCRT.timeScalePath c g) s ∉ closure U)
      (hfreq.mono fun t ht => ?_)
    have hct : c * (t / c) = t := by field_simp
    show g (c * (t / c)) ∉ closure U
    rw [hct]
    exact ht

/-- **Almost sure properties under the image by a linear time change.** If `p (g (c ·))` holds for `μ`-almost every
path `g`, then `p` holds almost surely under the image of `μ` by `g ↦ g (c ·)`, for `c ≠ 0` (no measurability of `p`
is needed: the time change is a measurable equivalence of the path space). -/
theorem ae_map_timeScalePath_of_ae {c : ℝ≥0} (hc : c ≠ 0) {μ : Measure (ContinuousPath ℂ)}
    {p : ContinuousPath ℂ → Prop} (h : ∀ᵐ g ∂μ, p (MatedCRT.timeScalePath c g)) :
    ∀ᵐ g ∂(μ.map (MatedCRT.timeScalePath c)), p g := by
  let e : ContinuousPath ℂ ≃ᵐ ContinuousPath ℂ :=
    { toFun := MatedCRT.timeScalePath c
      invFun := MatedCRT.timeScalePath c⁻¹
      left_inv := fun f => ContinuousMap.ext fun t => by
        show f (c * (c⁻¹ * t)) = f t
        rw [mul_inv_cancel_left₀ hc]
      right_inv := fun f => ContinuousMap.ext fun t => by
        show f (c⁻¹ * (c * t)) = f t
        rw [inv_mul_cancel_left₀ hc]
      measurable_toFun := MatedCRT.measurable_timeScalePath c
      measurable_invFun := MatedCRT.measurable_timeScalePath c⁻¹ }
  have he : μ.map (MatedCRT.timeScalePath c) = μ.map e := rfl
  rw [he, ae_iff, e.map_apply]
  exact ae_iff.1 h

/-- The linear time change with constant `1` does not change a family of path laws. -/
theorem timeScalePathKernel_one_apply (K : ℂ → ProbabilityMeasure (ContinuousPath ℂ)) (z : ℂ) :
    LatticeProb.timeScalePathKernel 1 K z = K z := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [LatticeProb.timeScalePathKernel, ProbabilityMeasure.toMeasure_map]
  have h1 : (LatticeProb.timeScalePath 1 : ContinuousPath ℂ → ContinuousPath ℂ) = id :=
    funext fun f => ContinuousMap.ext fun t => by simp
  rw [h1, Measure.map_id]

/-! ### The origin mixture under a deterministic time change -/

/-- **The origin mixture of a time-changed limit.** Let `ν` be a law of pairs (data, path-law family) whose data
marginal is the law of `D`, and suppose that `ν`-almost surely the family is the linear time change, with a
deterministic constant `c`, of `Λ` of the data. Then the origin mixture of `ν` is the image by `g ↦ g (c ·)` of the
origin mixture of the law of `(D, Λ D)`. -/
theorem originPathLaw_eq_map_timeScalePath {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data]
    [BorelSpace Data] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → Data} (hD : Measurable D)
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} (hfst : ν.map Prod.fst = P.map D)
    {c : ℝ≥0} (hc : ∀ᵐ p ∂ν, ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (Λ p.1) z) :
    originPathLaw ν =
      (originPathLaw (P.map fun ω => (D ω, Λ (D ω)))).map (MatedCRT.timeScalePath c) := by
  ext E hE
  have hE' : MeasurableSet (MatedCRT.timeScalePath c ⁻¹' E) := MatedCRT.measurable_timeScalePath c hE
  have hκ0 : Measurable fun d : Data => (Λ d 0 : ProbabilityMeasure (ContinuousPath ℂ)) :=
    (continuous_eval_const (0 : ℂ)).measurable.comp hΛm
  have hκ : Measurable fun d : Data =>
      ((Λ d 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (MatedCRT.timeScalePath c ⁻¹' E) :=
    (Measure.measurable_coe hE').comp (measurable_subtype_coe.comp hκ0)
  have hts : ∀ (K : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (z : ℂ),
      ((LatticeProb.timeScalePathKernel c K z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)) E =
        (K z : Measure (ContinuousPath ℂ)) (MatedCRT.timeScalePath c ⁻¹' E) := by
    intro K z
    simp only [LatticeProb.timeScalePathKernel, ProbabilityMeasure.toMeasure_map]
    exact Measure.map_apply (MatedCRT.measurable_timeScalePath c) hE
  rw [Measure.map_apply (MatedCRT.measurable_timeScalePath c) hE,
    originPathLaw_apply_of_eq_map hD hΛm rfl hE', originPathLaw,
    Measure.bind_apply hE measurable_originPathLawKernel.aemeasurable]
  calc ∫⁻ p, ((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) E ∂ν
      = ∫⁻ p, ((Λ p.1 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
          (MatedCRT.timeScalePath c ⁻¹' E) ∂ν :=
        lintegral_congr_ae (hc.mono fun p hp =>
          (congrArg (fun Q : ProbabilityMeasure (ContinuousPath ℂ) => (Q : Measure (ContinuousPath ℂ)) E)
            (hp 0)).trans (hts (Λ p.1) 0))
    _ = ∫⁻ d, ((Λ d 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
          (MatedCRT.timeScalePath c ⁻¹' E) ∂(ν.map Prod.fst) :=
        (lintegral_map hκ measurable_fst).symm
    _ = _ := by rw [hfst]; exact lintegral_map hκ hD

/-! ### The data marginal of a subsequential limit -/

/-- **The data marginal of a joint weak limit.** If the laws of `(D, Z n)` converge weakly to `ν`, then the first
marginal of `ν` is the law of `D`. -/
theorem map_fst_eq_map_of_tendsto_integral {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data]
    [PolishSpace Data] [BorelSpace Data] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {D : Ω → Data} (hD : Measurable D) {Z : ℕ → Ω → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsFiniteMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, Z n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν))) :
    ν.map Prod.fst = P.map D := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have h : Tendsto (fun _ : ℕ => ∫ ω, f (D ω) ∂P) atTop (𝓝 (∫ p, f p.1 ∂ν)) :=
    hconv (f.compContinuous ⟨Prod.fst, continuous_fst⟩)
  rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hD.aemeasurable f.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique h tendsto_const_nhds

/-! ### The identification hypothesis -/

/-- **The identification hypothesis of Theorem 2.11 from the Markovian time-change structure of the limits**
(Berestycki–Gwynne (2020), §7.1–7.4: Lemmas 7.4, 7.6, Proposition 7.10, Lemmas 7.17, 7.18). The consumer binders
(`hEnvS`, `hN4`, `hν`, `href`, `hU`) are those of `randomWalkToLBMStmt_of_identification`; the premises are

* `hexit`: Brownian motion makes an outward excursion right after its exit time (Mörters–Peres);
* `μX`, `hπ`, `hK3`: a family of locally finite measures on the plane indexed by a Polish space `M`, with the cutoff
  measures `ψ μX d` Lévy–Prokhorov continuous in `d`, and in every valid environment a measurable coordinate `E`
  with `μX (E ω) = μ_h` almost surely;
* `hN8`: for almost every value `d` of the data `(pairJ ⊤ H, E)`, the Liouville Brownian law field
  `lbmPathLawField γ d.1` is a Markovian time change of Brownian motion with `μX d.2` invariant, `μX d.2 ≠ 0`, and the
  exit time of `B_{1/2}` from `0` has nonzero median;
* `hN5`: every subsequential weak limit of the interpolated walk laws is almost surely a Markovian time change of
  Brownian motion (Lemma 7.4);
* `hN9`: if almost surely the limiting family is a linear time change of the Liouville Brownian law field, the
  constant is deterministic (Lemma 7.18). -/
theorem hid_of_markovLimit {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hexit : BrownianOutwardExcursionAtExitStep)
    {M : Type} [TopologicalSpace M] [MeasurableSpace M] [PolishSpace M] [BorelSpace M]
    (μX : M → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    (hK3 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ E : Ω → M, Measurable E ∧ ∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω)
    (hN8 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → (∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (μX d.2) ∧
          μX d.2 ≠ 0 ∧ medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2))
            (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))) ≠ 0)
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × M) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × M) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∃ (Data : Type) (_ : TopologicalSpace Data) (_ : MeasurableSpace Data) (_ : PolishSpace Data)
        (_ : BorelSpace Data) (D : Ω → Data) (Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))),
        Measurable D ∧ Measurable Λ ∧
        (∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
          ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
            ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ))) ∧
        ∀ (e : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) → StrictMono φ →
          ∀ ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))), IsProbabilityMeasure ν →
          (∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
            Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
              (𝓝 (∫ p, f p ∂ν))) →
          ν = S.P.map fun ω => (D ω, Λ (D ω)) := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨H, hHm, hrep⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS
  have hH : Measurable H := hHm.mono (S.fieldSigma_le hS) le_rfl
  obtain ⟨E, hE, hEμ⟩ := hK3 γ hγ hγ2 Ω S hS
  have hDm : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) := (measurable_pairJ_top.comp hH).prodMk hE
  have hΛm : Measurable fun d : (LQGMetric.CoordJ → ℝ) × M => lbmPathLawField γ d.1 :=
    (measurable_lbmPathLawField γ).comp measurable_fst
  have hY : ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
        ∫ q, blPathFunctionalBCF hF q
          ∂(lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω), E ω).1 z : Measure (ContinuousPath ℂ)) :=
    fun z F hF => hLBM_lbmPathLawField (𝒮 := 𝒮) lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS H hH hrep z F hF
  refine ⟨(LQGMetric.CoordJ → ℝ) × M, inferInstance, inferInstance, inferInstance, inferInstance,
    fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω), fun d => lbmPathLawField γ d.1, hDm, hΛm, hY, ?_⟩
  intro e φ he0 he hφ ν' hν' hconv
  have hε0 : ∀ k, 0 < e (φ k) := fun k => he0 (φ k)
  have hε : Tendsto (fun k => e (φ k)) atTop (𝓝 0) := he.comp hφ.tendsto_atTop
  -- the data marginal of the limit
  have hfst : ν'.map Prod.fst = S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) :=
    map_fst_eq_map_of_tendsto_integral hDm hconv
  -- the scaling inputs of the uniform-start route
  have hD27 := degreeMeasureConvergenceStmt_of_envScaling_derived hEnvS
  have h213 := greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := exitTimeUpperBoundStmt_of_greenKernelUpper
    (greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have hEqLaw := hEqLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2 hν href hU hS hae hε0 hε
  -- `μ_h` is invariant for the limiting family (BG20 Lemma 7.6)
  have hinv : ∀ᵐ p ∂ν', IsInvariantFor p.2 (μX p.1.2) :=
    ae_isInvariantFor_of_tendsto_law_of_uniformStart hD27 h213 h214 hN4 hγ hγ2 hS hη' hae hε0 hε hEqLaw
      (D := fun _ ω => (LQGMetric.pairJ ⊤ (H ω), E ω)) (fun _ => hDm.aemeasurable) (fun d => μX d.2)
      (fun _ => hEμ) (fun ψ hψ hψc h0 => (hπ ψ hψ hψc h0).comp continuous_snd) hconv
  -- the Liouville Brownian law field (premise `hN8`), at `ν'`-almost every data value
  have h8 := hN8 γ hγ hγ2 Ω S hS H hH hrep E hE hEμ
  rw [← hfst] at h8
  have h8' := ae_of_ae_map measurable_fst.aemeasurable h8
  -- the limiting family is a Markovian time change of Brownian motion (premise `hN5`)
  have hν2 : IsProbabilityMeasure (ν'.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  have h5 := hN5 γ hγ hγ2 Ω S hS η' hη' hae (fun k => e (φ k)) hε0 hε (ν'.map Prod.snd) hν2 fun f => by
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact hconv (f.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have h5' : ∀ᵐ p ∂ν', IsMarkovTCBM p.2 := ae_of_ae_map measurable_snd.aemeasurable h5
  -- uniqueness of the time change (BG20 Proposition 7.10)
  have hK : Measurable fun p : ((LQGMetric.CoordJ → ℝ) × M) × PathLawFamily =>
      ((lbmPathLawField γ p.1.1 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) :=
    (measurable_originPathLawKernel (Data := (LQGMetric.CoordJ → ℝ) × M)).comp
      (measurable_fst.prodMk ((measurable_lbmPathLawField γ).comp (measurable_fst.comp measurable_fst)))
  obtain ⟨c, -, hc⟩ := exists_measurable_timeScale_of_isMarkovTCBM_revuzUnique_derived (P := ν')
    (fun p => lbmPathLawField γ p.1.1) Prod.snd (Metric.ball (0 : ℂ) (1 / 2)) Metric.isOpen_ball 0
    hK (measurable_originPathLawKernel (Data := (LQGMetric.CoordJ → ℝ) × M))
    (h8'.mono fun p hp => hp.2.2.2)
    (by
      filter_upwards [h8', h5', hinv] with p h8p h5p hip
      exact ⟨h8p.1, h5p, μX p.1.2, inferInstance, h8p.2.2.1, h8p.2.1, hip⟩)
  -- the time-change constant is deterministic (BG20 Lemma 7.18, premise `hN9`)
  obtain ⟨c₀, hc₀, hc₀ae⟩ := hN9 γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE (fun k => e (φ k)) hε0 hε ν' hν'
    hconv (hc.mono fun p hp => ⟨c p, hp.1, hp.2⟩)
  -- the normalization `c₀ = 1` through the exit-time median of the origin mixtures
  have hmap := originPathLaw_eq_map_timeScalePath (P := S.P) hDm hΛm hfst hc₀ae
  have hY0 := hY 0
  have hG1 := medianOf_exitCdf_originPathLaw_eq_one_of_eq_map hS hγ hγ2 hDm hΛm rfl hY0
  have hregG := ae_regularExit_originPathLaw_of_identification hS hDm hΛm rfl hY0 hexit
  have hstrictG := half_lt_exitCdf_originPathLaw_of_medianOf_lt hS hγ hγ2 hDm hΛm rfl hY0
  have hcR : (c₀ : ℝ) ≠ 0 := by exact_mod_cast hc₀
  have hcpos : (0 : ℝ) < c₀ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc₀)
  have hmedν : medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν')) = 1 / c₀ := by
    rw [hmap, medianOf_exitCdf_map_timeScalePath _ Metric.isOpen_ball hc₀, hG1]
  have hregν : ∀ᵐ g : ContinuousPath ℂ ∂(originPathLaw ν'),
      RegularExit (Metric.ball (0 : ℂ) (1 / 2)) ⇑g := by
    rw [hmap]
    exact ae_map_timeScalePath_of_ae hc₀ (hregG.mono fun g hg => regularExit_timeScalePath hc₀ hg)
  have hstrictν : ∀ s, medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν')) < s →
      (1 / 2 : ℝ≥0∞) < exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν') s := by
    intro s hs
    rw [hmedν, div_lt_iff₀ hcpos] at hs
    rw [hmap, exitCdf_map_timeScalePath _ Metric.isOpen_ball hc₀]
    refine hstrictG _ ?_
    rw [hG1, mul_comm]
    exact hs
  choose V hVm hVe using fun k => exists_measurable_vertexOf_curve (hε0 k)
  have ha : ∀ k, Measurable fun ω => V k (η' ω, 0) := fun k => (hVm k).comp (hη'.prodMk measurable_const)
  have hav : ∀ k, ∀ᵐ ω ∂S.P, V k (η' ω, 0) = vertexOf (e (φ k)) (S.η ω) 0 := fun k => by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hae] with ω hap hcoc hω
    rw [hVe k (η' ω) 0 (by rw [hω]; exact hcoc) (by rw [hω]; exact hap.2.2.1), hω]
  have hone := medianOf_exitCdf_originPathLaw_eq_one hS hη' hae hε0 hε hEqLaw ha hav hDm hconv hregν
    hstrictν (tendsto_mε_atTop_of_uniformStart h213 h214 hN4 hγ hγ2 hS hε0 hε)
  have hc1 : c₀ = 1 := by
    have h := hmedν.symm.trans hone
    rw [div_eq_one_iff_eq hcR] at h
    exact_mod_cast h.symm
  -- hence the limiting family is the Liouville Brownian law field of the data
  have hpath : ∀ᵐ p ∂ν', p.2 = lbmPathLawField γ p.1.1 := by
    filter_upwards [hc₀ae] with p hp
    refine ContinuousMap.ext fun z => ?_
    rw [hp z, hc1]
    exact timeScalePathKernel_one_apply _ z
  have hpair : Measurable fun d : (LQGMetric.CoordJ → ℝ) × M => (d, lbmPathLawField γ d.1) :=
    measurable_id.prodMk hΛm
  calc ν' = ν'.map id := Measure.map_id.symm
    _ = ν'.map fun p => (p.1, lbmPathLawField γ p.1.1) :=
        Measure.map_congr (hpath.mono fun p hp => Prod.ext rfl hp)
    _ = (ν'.map Prod.fst).map fun d => (d, lbmPathLawField γ d.1) :=
        (Measure.map_map hpair measurable_fst).symm
    _ = _ := by rw [hfst]; exact Measure.map_map hpair hDm

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the Markovian time-change structure of the
limits.** The premises are those of `hid_of_markovLimit`. -/
theorem randomWalkToLBMStmt_of_markovLimit {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hexit : BrownianOutwardExcursionAtExitStep)
    {M : Type} [TopologicalSpace M] [MeasurableSpace M] [PolishSpace M] [BorelSpace M]
    (μX : M → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    (hK3 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ E : Ω → M, Measurable E ∧ ∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω)
    (hN8 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → (∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (μX d.2) ∧
          μX d.2 ≠ 0 ∧ medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2))
            (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))) ≠ 0)
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × M) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × M) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_identification hEnvS hN4 hν href hU
    (hid_of_markovLimit hEnvS hN4 hν href hU hexit μX hπ hK3 hN8 hN5 hN9)

end MatedCRT.FirstPass.Derived
