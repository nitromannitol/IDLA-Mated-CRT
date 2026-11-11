import MatedCRT.LPStaging.Bonanno.LQGMeasureFieldMeasurable
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.Proofs.Measurability.FieldCircle

/-!
# The σ(h)-measurability of the LQG measure, from the Lattice-Probability theorem

`FrozenLQGMeasureFieldMeasurable 𝒮` asserts that for every valid environment `S` the γ-LQG measure `S.μ` agrees
almost surely with a `σ(h)`-measurable random measure. The general statement is
`LatticeProb.exists_measurable_version_of_lqgArea` (mirror `MatedCRT.LPStaging.Bonanno.LQGMeasureFieldMeasurable`;
Duplantier–Sheffield 2011, arXiv:0808.1560v2, Proposition 1.1): for circle averages `H r z ω` whose dyadic restrictions
are jointly measurable and a.s. continuous in `z`, the γ-LQG area measure `μ` (`IsLQGAreaOf`: the a.s. vague limit of
`ε^{γ²/2} e^{γ H ε z} dz` along `ε = 2^{-k}`) agrees a.s. with an `m`-measurable random measure.

We apply it with `m := S.fieldSigma`, `P := S.P`, `μ := S.μ` and `H := fieldVersion S`, the family of
`σ(h)`-measurable versions of the circle averages (`dyadicCircleVersion`, `FieldCircle.lean`). The bridges:

* `dyadicIndex`, `dyadicIndex_dyadicRadius`: the map `k ↦ dyadicRadius k = 2⁻ᵏ` is injective, and `dyadicIndex` is its
  inverse (`Function.invFun`), so that `fieldVersion S (dyadicRadius k) = dyadicCircleVersion S k`.
* `measurable_uncurry_fieldVersion`: the dyadic restrictions are jointly `σ(h) ⊗ 𝓑(ℂ)`-measurable
  (`FieldCircle.measurable_dyadicCircleVersion`).
* `ae_continuous_fieldVersion`: a.s. continuity in `z` of every dyadic restriction, from
  `IsQuantumCone.ae_continuousOn_circle` and `FieldCircle.ae_dyadicCircleVersion_eq`.
* `lqgApprox_fieldVersion_eq`, `isLQGAreaOf_fieldVersion`: the a.s. identification of the approximations
  `LatticeProb.lqgApprox` with `HarmonicBalls.lqgApprox` at `dyadicScale k = 2⁻ᵏ`, and so `IsLQGAreaOf` from the
  `IsLQGLimit` of `IsValid.isLQGMeasure`.

Every bridge is proved from the fields of `MatedCRTEnv.IsValid`; no hypothesis is introduced. The application of
`LatticeProb.exists_measurable_version_of_lqgArea` to these bridges is not in this file: its probability measure
`P : Measure Ω` is elaborated on the sub-σ-algebra `m` (the explicit binder `(m : MeasurableSpace Ω)` becomes the
local instance), while `MatedCRTEnv.P` lives on the ambient σ-algebra.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

namespace LQGMeasureFieldLP

variable {Ω : Type} [MeasurableSpace Ω]

/-- The Lattice-Probability dyadic radius `2^{-k}` is the Harmonic-Balls dyadic scale `2⁻ᵏ`. -/
lemma dyadicRadius_eq_dyadicScale (k : ℕ) :
    MatedCRTHarmonic.GMSLemma27.dyadicRadius k = HarmonicBalls.dyadicScale k := by
  unfold MatedCRTHarmonic.GMSLemma27.dyadicRadius HarmonicBalls.dyadicScale
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- The dyadic radii are pairwise distinct. -/
lemma dyadicRadius_injective :
    Function.Injective fun k : ℕ => MatedCRTHarmonic.GMSLemma27.dyadicRadius k := by
  intro j k hjk
  have hjk' : (2 : ℝ)⁻¹ ^ j = (2 : ℝ)⁻¹ ^ k := by
    have h := hjk
    simp only [dyadicRadius_eq_dyadicScale] at h
    exact h
  exact pow_right_injective₀ (by norm_num) (by norm_num) hjk'

/-- The dyadic index of a real radius: the inverse of `k ↦ dyadicRadius k` (`Function.invFun`). -/
noncomputable def dyadicIndex (r : ℝ) : ℕ :=
  Function.invFun (fun k : ℕ => MatedCRTHarmonic.GMSLemma27.dyadicRadius k) r

lemma dyadicIndex_dyadicRadius (k : ℕ) :
    dyadicIndex (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) = k :=
  Function.leftInverse_invFun dyadicRadius_injective k

/-- The `σ(h)`-measurable version of the circle averages at every real radius: at `r = 2^{-k}` it is the
dyadic version `dyadicCircleVersion S k` (`FieldCircle.lean`). -/
noncomputable def fieldVersion (S : MatedCRTEnv Ω) : ℝ → ℂ → Ω → ℝ :=
  fun r z ω => MatedCRT.FieldCircle.dyadicCircleVersion S (dyadicIndex r) ω z

lemma fieldVersion_dyadicRadius (S : MatedCRTEnv Ω) (k : ℕ) (z : ℂ) (ω : Ω) :
    fieldVersion S (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω =
      MatedCRT.FieldCircle.dyadicCircleVersion S k ω z := by
  simp only [fieldVersion, dyadicIndex_dyadicRadius]

lemma measurable_uncurry_fieldVersion (S : MatedCRTEnv Ω) (k : ℕ) :
    Measurable[S.fieldSigma.prod (inferInstance : MeasurableSpace ℂ)]
      (Function.uncurry fun ω z => fieldVersion S (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω) := by
  have h : (Function.uncurry fun ω z => fieldVersion S (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω) =
      Function.uncurry (MatedCRT.FieldCircle.dyadicCircleVersion S k) := by
    funext p
    exact fieldVersion_dyadicRadius S k p.2 p.1
  rw [h]
  exact MatedCRT.FieldCircle.measurable_dyadicCircleVersion S k

lemma ae_continuous_fieldVersion {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ k : ℕ,
      Continuous fun z : ℂ => fieldVersion S (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω := by
  filter_upwards [MatedCRT.FieldCircle.ae_dyadicCircleVersion_eq hS,
    hS.isQuantumCone.ae_continuousOn_circle] with ω h1 h2 k
  have hfun : (fun z : ℂ => fieldVersion S (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω) =
      fun z : ℂ => S.hcirc ω ((2 : ℝ)⁻¹ ^ k) z := by
    funext z
    rw [fieldVersion_dyadicRadius, h1 k z]
  rw [hfun, ← continuousOn_univ]
  have hcont : Continuous fun w : ℂ => (((2 : ℝ)⁻¹ ^ k, w) : ℝ × ℂ) :=
    continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun w : ℂ => (((2 : ℝ)⁻¹ ^ k, w) : ℝ × ℂ)) univ (Ioi 0 ×ˢ univ) :=
    fun w _ => ⟨mem_Ioi.2 (by positivity), mem_univ _⟩
  exact h2.comp hcont.continuousOn hmaps

lemma lqgApprox_fieldVersion_eq (S : MatedCRTEnv Ω) (γ : ℝ) (ω : Ω)
    (h1 : ∀ (n : ℕ) (z : ℂ), MatedCRT.FieldCircle.dyadicCircleVersion S n ω z = S.hcirc ω ((2 : ℝ)⁻¹ ^ n) z)
    (k : ℕ) :
    MatedCRTHarmonic.GMSLemma27.lqgApprox γ (fieldVersion S) k ω =
      HarmonicBalls.lqgApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) := by
  unfold MatedCRTHarmonic.GMSLemma27.lqgApprox HarmonicBalls.lqgApprox
  refine congrArg (fun f => (volume : Measure ℂ).withDensity f) ?_
  funext z
  rw [fieldVersion_dyadicRadius, h1 k z]
  simp only [dyadicRadius_eq_dyadicScale, HarmonicBalls.dyadicScale]

lemma isLQGAreaOf_fieldVersion {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ (fieldVersion S) S.μ S.P := by
  have hLQG : ∀ᵐ ω ∂S.P, HarmonicBalls.IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  unfold MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf
  filter_upwards [hLQG, MatedCRT.FieldCircle.ae_dyadicCircleVersion_eq hS] with ω h2 h1
  refine ⟨h2.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  simp only [lqgApprox_fieldVersion_eq S γ ω h1]
  exact h2.tendsto_integral f hf hfc

end LQGMeasureFieldLP

end MatedCRT
