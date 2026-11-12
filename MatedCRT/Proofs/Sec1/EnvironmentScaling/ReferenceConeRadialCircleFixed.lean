import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalConeIdentification

/-!
# The reference-cone radial circle step from fixed-radius circle averages

`ReferenceConeRadialCircleStep` asks that, almost surely, the radial process of the
distributional circle version of the reference cone field `coneField X (coneRadial γ γ B B')` is
`referenceConeRadialPair γ B B'`. This file reduces it to the fixed-radius identity
`h_{e^{-t}}(0) = A_t` for the circle average of the cone field, one null set for each `t`
(DMS Definition 4.10: the radial part of the `γ`-quantum cone field is the process `A`).

The distributional circle version agrees with the continuous circle process of the environment
(`ae_distributionCircleVersion_eq`), rational times give one null set, and both sides are
continuous on each closed half-line, so they agree there. Neither the vanishing of the drifted
path at its last zero nor any growth bound for Brownian motion is used.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MatedCRT.Sec1

/-- Two functions continuous on the closure of an open set of reals which agree at the rational
points of the set agree on its closure. -/
theorem eqOn_closure_of_eq_rat {f g : ℝ → ℝ} {u : Set ℝ} (hu : IsOpen u)
    (hf : ContinuousOn f (closure u)) (hg : ContinuousOn g (closure u))
    (hq : ∀ q : ℚ, (q : ℝ) ∈ u → f q = g q) : EqOn f g (closure u) := by
  have hsub : u ⊆ closure (u ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter Rat.denseRange_cast hu
  refine EqOn.of_subset_closure (s := u ∩ range ((↑) : ℚ → ℝ)) ?_ hf hg
    (inter_subset_left.trans subset_closure) (closure_minimal hsub isClosed_closure)
  rintro _ ⟨hx, q, rfl⟩
  exact hq q hx

/-- **The radial process of the reference cone from fixed-radius circle averages.** Let `S` be a
valid environment whose field is almost surely the cone field built from `X` and the radial
process `A = coneRadial γ γ B B'`, with `B` and `B'` almost surely continuous. If for every fixed
`t`, almost surely, the circle average of the cone field at radius `e^{-t}` about `0` is `A_t`,
then almost surely the radial process of the distributional circle version of the cone field is
`referenceConeRadialPair γ B B'`. -/
theorem ae_radialProcess_coneField_eq_referenceConeRadialPair
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : ∀ᵐ ω ∂S.P, Continuous fun t => B t ω)
    (hB' : ∀ᵐ ω ∂S.P, Continuous fun t => B' t ω)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ)
    (hfix : ∀ t : ℝ, ∀ᵐ ω ∂S.P, LQGMetric.circleAvg
      (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))
      (Real.exp (-t)) 0 =
        MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ᵐ ω ∂S.P, radialProcess (distributionCircleVersion
      (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω) := by
  have hq : ∀ᵐ ω ∂S.P, ∀ q : ℚ, S.hcirc ω (Real.exp (-(q : ℝ))) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) q := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hfix q, ae_distribution_circleAvg_eq hS hH (Real.exp_pos (-(q : ℝ)))
      (z := 0) (by rw [norm_zero]; exact (Real.exp_pos _).ne)] with ω h1 h2
    rw [← h2, h1]
  filter_upwards [hq, ae_distributionCircleVersion_eq hS hH,
    hS.isQuantumCone.ae_continuousOn_circle, hB, hB'] with ω hq hD hc hBc hB'c
  set b : ℝ≥0 → ℝ := fun s => B s ω with hb
  set b' : ℝ≥0 → ℝ := fun s => B' s ω with hb'
  set Q : ℝ := MatedCRTHarmonic.MatedCRT.lqgQ γ with hQ
  set f : ℝ → ℝ := fun t => S.hcirc ω (Real.exp (-t)) 0 with hfdef
  set c : ℝ → ℝ := fun u => b' u.toNNReal + (Q - γ) * u with hcdef
  set ℓ : ℝ := MatedCRTHarmonic.MatedCRT.lastZeroR c with hℓ
  have hf : Continuous f :=
    hc.comp_continuous ((Real.continuous_exp.comp continuous_neg).prodMk continuous_const)
      fun t => ⟨Real.exp_pos _, mem_univ _⟩
  have hcc : Continuous c :=
    (hB'c.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
  have hg₁ : Continuous fun t : ℝ => b t.toNNReal + γ * t :=
    (hBc.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
  have hg₂ : Continuous fun t : ℝ => c (ℓ - t) + Q * t :=
    (hcc.comp (continuous_const.sub continuous_id)).add (continuous_const.mul continuous_id)
  have h₁ : EqOn f (fun t : ℝ => b t.toNNReal + γ * t) (Ici 0) := by
    have := eqOn_closure_of_eq_rat (u := Ioi 0) isOpen_Ioi hf.continuousOn hg₁.continuousOn
      (fun q hq0 => by
        rw [hfdef]
        simp only
        rw [hq q, MatedCRTHarmonic.MatedCRT.coneRadial]
        simp only [show (0 : ℝ) ≤ q from hq0.le, ↓reduceIte])
    rwa [closure_Ioi] at this
  have h₂ : EqOn f (fun t : ℝ => c (ℓ - t) + Q * t) (Iic 0) := by
    have := eqOn_closure_of_eq_rat (u := Iio 0) isOpen_Iio hf.continuousOn hg₂.continuousOn
      (fun q hq0 => by
        rw [hfdef]
        simp only
        rw [hq q, MatedCRTHarmonic.MatedCRT.coneRadial]
        simp only [show ¬ (0 : ℝ) ≤ q from not_le.mpr hq0, ↓reduceIte]
        rfl)
    rwa [closure_Iio] at this
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have ht : (0 : ℝ) ≤ t := t.2
    have e1 := hD (Real.exp (-(t : ℝ))) (Real.exp_pos _) 0
    have e2 := h₁ (mem_Ici.2 ht)
    simp only [hfdef] at e2
    simp only [radialProcess, referenceConeRadialPair]
    rw [e1, e2, Real.toNNReal_coe]
  · have hs : -(s : ℝ) ≤ 0 := neg_nonpos.2 s.2
    have e1 := hD (Real.exp (s : ℝ)) (Real.exp_pos _) 0
    have e2 := h₂ (mem_Iic.2 hs)
    simp only [hfdef, neg_neg] at e2
    simp only [radialProcess, referenceConeRadialPair]
    rw [e1, e2, sub_neg_eq_add, mul_neg, ← sub_eq_add_neg]

/-- **`ReferenceConeRadialCircleStep` from the fixed-radius circle averages of the cone field.**
The hypothesis is the statement, for every probability space, every whole-plane Gaussian free
field `X` and independent Brownian motions `B`, `B'`, that at every fixed `t` the circle average of
`coneField X (coneRadial γ γ B B')` at radius `e^{-t}` about `0` is almost surely the radial
process at time `t` (the cone field is built so that its radial part is `A`). -/
theorem referenceConeRadialCircleStep_of_fixedRadius {𝒮 : SpaceFillingSLEModel}
    (hfix : ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
      LQGMetric.IsWholePlaneGFF X P → IsBrownianReal B P → IsBrownianReal B' P →
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P →
      ∀ t : ℝ, ∀ᵐ ω ∂P, LQGMetric.circleAvg
        (MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))
        (Real.exp (-t)) 0 =
          MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) :
    ReferenceConeRadialCircleStep 𝒮 := by
  intro γ Ω _ S hS X B B' hX hB hB' _ hBB' hH
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact ae_radialProcess_coneField_eq_referenceConeRadialPair hS hB.cont hB'.cont hH
    (hfix γ Ω S.P X B B' hX hB hB' hBB')

end MatedCRT.Sec1
