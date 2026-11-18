import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import LatticeProb.Prob.BrownianPathSpace

/-!
# From the Lévy–Prokhorov bound for the interpolated walk to a bound on all sets of stopped paths

The interpolated embedded walk of the mated-CRT map at speed `1` stopped at its exit time from a
bounded open set `Uc` has the law of the stopped curve class `stoppedExitCurve Uc` under
`srwLaw`. A Lévy–Prokhorov bound between this law (for the walk written in the unit-speed,
unit-scale normalization of the area-cell package) and the stopped Brownian law of the Euclidean
reading of `Uc` bounds the probability of every set `S` of stopped walk paths by the planar
Brownian probability of the `cmpEDist`-neighborhood of `S`.
-/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitWalkBound

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.StopAtExitCurveClass
  MatedCRT.StopAtExitLevyProkhorov

/-- Planar Brownian motion exits every bounded set in finite time, from every starting point. -/
theorem ae_pathExitTime_planarBrownianMotion_ne_top {Uc : Set ℂ} (hb : Bornology.IsBounded Uc)
    (z : ℂ) : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z), pathExitTime Uc ⇑b ≠ ⊤ := by
  obtain ⟨R, hR⟩ := hb.subset_ball z
  filter_upwards [HarmonicBalls.Section6.ae_planarBrownianMotion_exitTime_ball_lt_top z R]
    with b hb'
  exact ((ContinuousPath.exitTime_mono hR b).trans_lt hb').ne

/-- The standard Brownian laws of the library and of its curve-space development agree. -/
theorem isStandardBrownianLaw_iff (μ : Measure (BouRabeeGwynne.BrownianPath 2)) :
    LatticeProb.IsStandardBrownianLaw μ ↔ BouRabeeGwynne.IsStandardBrownianLaw μ :=
  Iff.rfl

/-- **All-set bound for the unit-speed interpolated walk.** Let `Uc` be bounded and open. A
Lévy–Prokhorov bound `< δ` between the law, under the walk law `srwLaw m a`, of the curve class of
the interpolated embedded walk (speed `m₀ = 1`, scale `α = 1`) stopped at its exit time from `Uc`,
and the stopped Brownian law of the Euclidean reading of `Uc` from `y`, bounds the probability of
every set `S` of stopped walk paths by the Brownian probability of the `cmpEDist`-neighborhood of
`S` plus `δ`, provided the walk exits `Uc` in finite time almost surely. -/
theorem srwLaw_allSet_le_of_levyProkhorovEDist {α m₀ : ℝ≥0} (hα : α = 1) (hm₀ : 0 < m₀)
    (hm₁ : m₀ = 1) (ε : ℝ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (a : ℤ) (Uc : Set ℂ) (hUo : IsOpen Uc)
    (hUb : Bornology.IsBounded Uc)
    (hfin : ∀ᵐ ξ ∂(srwLaw m a), pathExitTime Uc (interpolatedWalk ε η 1 ξ) ≠ ⊤)
    (y : LatticeProb.Euc 2) (U : Set (LatticeProb.Euc 2))
    (hUc : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)
    (μ : Measure (LatticeProb.BrownianPath 2)) (hμ : LatticeProb.IsStandardBrownianLaw μ)
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (h : levyProkhorovEDist
      ((srwLaw m a).map (fun x : ℕ → ℤ => isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le x))
          (pathExitTime Uc ⇑((α : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le x)).toNNReal)))
      (BouRabeeGwynne.stoppedBrownianLaw U y μ) < ENNReal.ofReal δ)
    (S : Set (ℝ≥0 → ℂ)) :
    srwLaw m a {ξ | stopAtExit Uc (interpolatedWalk ε η 1 ξ) ∈ S} ≤
      planarBrownianMotion (Complex.orthonormalBasisOneI.repr.symm y)
        {b : ContinuousPath ℂ | ∃ f ∈ S, cmpEDist (stopAtExit Uc ⇑b) f < ENNReal.ofReal (δ + κ)} +
      ENNReal.ofReal δ := by
  subst hα hm₁
  set z : ℂ := Complex.orthonormalBasisOneI.repr.symm y with hz
  have hyz : Complex.orthonormalBasisOneI.repr z = y := by
    rw [hz]; exact LinearIsometryEquiv.apply_symm_apply _ _
  have hU : U = Complex.orthonormalBasisOneI.repr '' Uc := by
    rw [hUc]
    exact (Complex.orthonormalBasisOneI.repr.toEquiv.image_eq_preimage_symm Uc).symm
  have hlaw : BouRabeeGwynne.stoppedBrownianLaw U y μ =
      (planarBrownianMotion z).map (stoppedExitCurve Uc) := by
    rw [hU, ← hyz]
    exact stoppedBrownianLaw_eq_map Uc hUo z μ hμ
  have hF : (fun x : ℕ → ℤ => isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le x))
          (pathExitTime Uc ⇑(((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le x)).toNNReal)) =
      fun x => stoppedExitCurve Uc (interpPathCM (vertexPoint ε η) zero_le_one x) := by
    funext x
    have hp : (((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le x) =
        interpPathCM (vertexPoint ε η) zero_le_one x := by
      rw [NNReal.coe_one, one_smul]
      refine ContinuousMap.ext fun t => ?_
      simp [interpPathCM_apply]
    rw [hp]
    rfl
  rw [hF, hlaw] at h
  have hmeas : Measurable (fun x : ℕ → ℤ => stoppedExitCurve Uc
      (interpPathCM (vertexPoint ε η) zero_le_one x)) :=
    (measurable_stoppedExitCurve Uc hUo).comp (measurable_interpPathCM _ zero_le_one)
  exact allSet_stopAtExit_le_of_levyProkhorovEDist (srwLaw m a)
    (fun x => interpPathCM (vertexPoint ε η) zero_le_one x) Uc hmeas.aemeasurable hfin Uc hUo z
    (ae_pathExitTime_planarBrownianMotion_ne_top hUb z) hδ hκ h S

end MatedCRT.StopAtExitWalkBound
