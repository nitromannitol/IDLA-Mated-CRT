import MatedCRT.FirstPass.Derived.AnnealedWalkLawInterpClosenessInMeasure

/-!
# The walk law from the cell of a point against the interpolated law at the point, under the annealed law

For a fixed point `z₀` and random start vertices `k_n(ω)` with `z₀ ∈ H^{ε_n}_{k_n(ω)}`, the quenched law
`Q^{ε_n}(k_n)` of the embedded walk is close in Lévy–Prokhorov distance to the interpolated law `P̃^{ε_n}_{z₀}`
in probability under the environment law `S.P` (`tendstoInMeasure_levyProkhorovDist_walkPathLaw_interpWalkLaw`).
The environment coordinate of the `n`-th factor of the product space `annealedWalksAt` has law `S.P`, so the
statement transfers to the annealed product space.  This is the closeness of the conditional law `Q^{ε_n}(k_n)` of
the walk to the continuous function `d ↦ d(z₀)` of the datum `D_n = P̃^{ε_n}`, in measure on the product space.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The quenched walk law from the cell of `z₀` against the interpolated law at `z₀`, in probability, under the
annealed law.**  Under `hEqLaw` and `hdiam` for the environment law `S.P`, and `z₀ ∈ H^{ε_n}_{k_n(ω)}` almost
surely for all `n`, the Lévy–Prokhorov distance of `Q^{ε_n}(k_n(ω))` and `P̃^{ε_n}_{z₀}` tends to `0` in
probability under `annealedWalksAt`, where `ω` is the environment coordinate `(p n).1` of the product point. -/
theorem tendstoInMeasure_levyProkhorovDist_annealedWalksAt_walkPathLaw_interpWalkLaw_start
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    [IsProbabilityMeasure S.P] {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    {z₀ : ℂ} {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n))
    (hz₀ : ∀ᵐ ω ∂S.P, ∀ n, z₀ ∈ cell (ε n) (⇑(η' ω)) (k n ω)) :
    TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n)
          (k n (p n).1) (p n).1 : Measure (ContinuousPath ℂ))
        (interpWalkLaw S η' (ε n) (p n).1 z₀ : Measure (ContinuousPath ℂ))) atTop (fun _ => 0) := by
  have h1 := tendstoInMeasure_levyProkhorovDist_walkPathLaw_interpWalkLaw hS hae hε0 hε hEqLaw hdiam hz₀
  rw [tendstoInMeasure_iff_dist] at h1 ⊢
  intro θ hθ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h1 θ hθ)
    (fun n => zero_le) (fun n => ?_)
  exact annealedWalksAt_preimage_fst_le hS ε hk n
    {ω | θ ≤ dist (levyProkhorovDist
      (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) (k n ω) ω :
        Measure (ContinuousPath ℂ))
      (interpWalkLaw S η' (ε n) ω z₀ : Measure (ContinuousPath ℂ))) 0}

end MatedCRT.FirstPass.Derived
