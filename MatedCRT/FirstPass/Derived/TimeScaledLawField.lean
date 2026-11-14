import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.BLPathFunctionalDUnif
import MatedCRT.FirstPass.Derived.ExitTimeScaling
import LatticeProb.Topology.ContinuousMapBorel

/-!
# Time scaling of fields of path laws and the rescaled Liouville Brownian motion

For `m ≥ 0` let `timeScalePath m q = (t ↦ q (m t))` be the time scaling of continuous paths
(`MatedCRT.timeScalePath`, continuous for the compact-open topology). Pushing forward by it gives

* `timeScaleLaw m : C(𝒫(C(ℝ≥0, ℂ)), 𝒫(C(ℝ≥0, ℂ)))`, `ν ↦ (q ↦ q(m ·))_* ν`, continuous for the topology of weak
  convergence (`ProbabilityMeasure.continuous_map`);
* `timeScaleLawField m : C(C(ℂ, 𝒫), C(ℂ, 𝒫))`, `K ↦ (z ↦ (q ↦ q(m ·))_* K(z))`, the postcomposition by
  `timeScaleLaw m`, continuous for the compact-open topology and hence Borel measurable
  (`measurable_timeScaleLawField`) for the Borel σ-algebra of the compact-open topology on `C(ℂ, 𝒫)`.

The rescaled Liouville Brownian motion `X_t = B_{F⁻¹(m₀ t)}` (`rescaledLBMPath`, Setting.lean) is the time scaling
by `m₀` of the Liouville Brownian motion path `t ↦ B_{F⁻¹(t)}` (`lbmContinuousPath`) whenever the clock `F(B)` is
a time-change clock. Hence for every bounded Lipschitz path functional `G`, the expectation of `G(X)` under planar
Brownian motion from `z` is the integral of `G` against the time-scaled law of Liouville Brownian motion from `z`
(`integral_rescaledLBMPath_eq_timeScale`), and against `timeScaleLawField m₀ K z` for every field of path laws `K`
whose value at `z` is that law (`integral_rescaledLBMPath_eq_timeScaleLawField`). This is the defining property
of the field `Φ(γ, d)(z) = (q ↦ [t ↦ q(m_γ t)])_* K_γ(d)(z)` of the random-walk-to-Liouville-Brownian-motion
identification (Berestycki–Gwynne (2020), (1.6)).

Terminology: positive continuous additive functional (the LQG clock `F`), its right-continuous inverse, and the
time change `B_{F⁻¹(t)}` of planar Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian motion*,
Definition 2.17; Berestycki, *Diffusion in planar Liouville quantum gravity*, Section 2).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local fun_prop] measurable_timeScalePath

/-- The time scaling `ν ↦ (q ↦ [t ↦ q(m t)])_* ν` of laws of continuous planar paths, as a continuous map for the
topology of weak convergence. -/
noncomputable def timeScaleLaw (m : ℝ≥0) :
    C(ProbabilityMeasure (ContinuousPath ℂ), ProbabilityMeasure (ContinuousPath ℂ)) :=
  ⟨fun ν => ν.map (timeScalePath m),
    ProbabilityMeasure.continuous_map (continuous_timeScalePath m)⟩

theorem timeScaleLaw_apply (m : ℝ≥0) (ν : ProbabilityMeasure (ContinuousPath ℂ)) :
    timeScaleLaw m ν = ν.map (timeScalePath m) := rfl

theorem coe_timeScaleLaw (m : ℝ≥0) (ν : ProbabilityMeasure (ContinuousPath ℂ)) :
    (timeScaleLaw m ν : Measure (ContinuousPath ℂ)) =
      (ν : Measure (ContinuousPath ℂ)).map (timeScalePath m) := by
  rw [timeScaleLaw_apply, ProbabilityMeasure.toMeasure_map]

/-- The time scaling of a field of path laws, `K ↦ (z ↦ (q ↦ [t ↦ q(m t)])_* K(z))`, as a continuous map for the
compact-open topologies. -/
noncomputable def timeScaleLawField (m : ℝ≥0) :
    C(C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)), C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) :=
  ⟨fun K => (timeScaleLaw m).comp K, ContinuousMap.continuous_postcomp _⟩

theorem timeScaleLawField_apply (m : ℝ≥0) (K : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (z : ℂ) :
    timeScaleLawField m K z = (K z).map (timeScalePath m) := rfl

/-- **The time scaling of fields of path laws is Borel measurable** for the Borel σ-algebra of the compact-open
topology on `C(ℂ, 𝒫(C(ℝ≥0, ℂ)))`: it is continuous. -/
theorem measurable_timeScaleLawField (m : ℝ≥0) : Measurable (timeScaleLawField m) :=
  (timeScaleLawField m).continuous.measurable

/-- On the event that `F b` is a time-change clock, the rescaled Liouville Brownian motion path `t ↦ b(F⁻¹(m₀ t))`
is the time scaling by `m₀` of the Liouville Brownian motion path `t ↦ b(F⁻¹(t))`. -/
theorem timeScalePath_lbmContinuousPath {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (m₀ : ℝ) {b : ContinuousPath ℂ}
    (hb : IsTimeChangeClock (F b)) :
    ⇑(timeScalePath m₀.toNNReal (lbmContinuousPath F b)) = rescaledLBMPath F m₀ b := by
  rw [lbmContinuousPath_of_isTimeChangeClock hb]
  rfl

/-- **Integral identity for the rescaled Liouville Brownian motion.** Let the clock `F b` be a time-change clock
for almost every planar Brownian path `b` from `z`, and let the Liouville Brownian motion path `b ↦ (t ↦ b(F⁻¹(t)))`
be almost everywhere measurable (`hg`, the hypothesis of `planarBrownianPathLaw`). Then for every bounded Lipschitz
path functional `G`, the expectation of `G` of the rescaled path `t ↦ b(F⁻¹(m₀ t))` is the integral of `G` against
the time scaling by `m₀` of the law of Liouville Brownian motion from `z`. -/
theorem integral_rescaledLBMPath_eq_timeScale {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (z : ℂ) (m₀ : ℝ)
    (hclock : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hg : AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z))
    {G : (ℝ≥0 → ℂ) → ℝ} (hG : IsBoundedLipschitzPathFunctional G) :
    ∫ b, G (rescaledLBMPath F m₀ b) ∂planarBrownianMotion z =
      ∫ q, FirstPass.Derived.blPathFunctionalBCF hG q
        ∂((planarBrownianPathLaw z (lbmContinuousPath F) hg).map (timeScalePath m₀.toNNReal) :
          Measure (ContinuousPath ℂ)) := by
  have hf := (FirstPass.Derived.blPathFunctionalBCF hG).continuous
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_timeScalePath _).aemeasurable hf.aestronglyMeasurable]
  change _ = ∫ q, FirstPass.Derived.blPathFunctionalBCF hG (timeScalePath m₀.toNNReal q)
    ∂(Measure.map (lbmContinuousPath F) (planarBrownianMotion z))
  rw [integral_map hg (show AEStronglyMeasurable
    (fun q => FirstPass.Derived.blPathFunctionalBCF hG (timeScalePath m₀.toNNReal q)) _ from
      (hf.comp (continuous_timeScalePath _)).aestronglyMeasurable)]
  refine integral_congr_ae ?_
  filter_upwards [hclock] with b hb
  rw [FirstPass.Derived.blPathFunctionalBCF_apply, timeScalePath_lbmContinuousPath m₀ hb]

/-- **Integral identity against a time-scaled field of path laws.** If a field of path laws `K` takes at `z` the
value of the law of Liouville Brownian motion from `z`, then for every bounded Lipschitz path functional `G` the
expectation of `G` of the rescaled path `t ↦ b(F⁻¹(m₀ t))` is the integral of `G` against
`timeScaleLawField m₀ K z`. -/
theorem integral_rescaledLBMPath_eq_timeScaleLawField {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (z : ℂ) (m₀ : ℝ)
    (hclock : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hg : AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z))
    {K : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (hK : K z = planarBrownianPathLaw z (lbmContinuousPath F) hg)
    {G : (ℝ≥0 → ℂ) → ℝ} (hG : IsBoundedLipschitzPathFunctional G) :
    ∫ b, G (rescaledLBMPath F m₀ b) ∂planarBrownianMotion z =
      ∫ q, FirstPass.Derived.blPathFunctionalBCF hG q
        ∂(timeScaleLawField m₀.toNNReal K z : Measure (ContinuousPath ℂ)) := by
  rw [timeScaleLawField_apply, hK]
  exact integral_rescaledLBMPath_eq_timeScale z m₀ hclock hg hG

end MatedCRT
