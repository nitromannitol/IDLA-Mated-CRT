import MatedCRT.FirstPass.Derived.WalkLawInterpClosenessAtPoint
import MatedCRT.FirstPass.Derived.InterpWalkLawJointConvergence

/-!
# The walk law against the interpolated law at a point, in probability

The embedded walk of Theorem 2.11 started at the vertex `k_n(ω)` of a cell `H^{ε_n}_{k_n(ω)}` containing a fixed
point `z₀` has quenched law `Q^{ε_n}(k_n)`.  By `pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell_of_nonneg`
its Lévy–Prokhorov distance to the interpolated law `P̃^{ε_n}_{z₀}` at the point `z₀` is at most the modulus
`ω^{ε_n}_R(δ)` as soon as the cells near `B_{R+1}` are small.  If the walk laws are equicontinuous in law
(`hEqLaw`) and the cell diameters tend to `0` in probability (`hdiam`), the distance tends to `0` in probability.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The quenched walk law from the cell of `z₀` against the interpolated law at `z₀`, in probability.**
Let `ε_n → 0⁺`, assume the walk laws are equicontinuous in law (`hEqLaw`: for all `R` and `a > 0` there is `δ > 0`
with `P[ω^{ε_n}_R(δ) > a] ≤ a` eventually) and that the cell diameters near `B_{R+1}` tend to `0` in probability
(`hdiam`).  If `z₀ ∈ H^{ε_n}_{k_n(ω)}` almost surely, then
`LP(Q^{ε_n}(k_n), P̃^{ε_n}_{z₀}) → 0` in probability. -/
theorem tendstoInMeasure_levyProkhorovDist_walkPathLaw_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    {z₀ : ℂ} {k : ℕ → Ω → ℤ} (hz₀ : ∀ᵐ ω ∂S.P, ∀ n, z₀ ∈ cell (ε n) (⇑(η' ω)) (k n ω)) :
    TendstoInMeasure S.P (fun n ω => levyProkhorovDist
      (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) (k n ω) ω :
        Measure (ContinuousPath ℂ))
      (interpWalkLaw S η' (ε n) ω z₀ : Measure (ContinuousPath ℂ))) atTop (fun _ => 0) := by
  have hgood : ∀ᵐ ω ∂S.P, ∀ n,
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
        interpWeight (fun k => cell (ε n) (⇑(η' ω)) k) (ε n) k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (ε n) (⇑(η' ω)) k) (ε n) k z ≠ 0 := by
    rw [ae_all_iff]
    intro n
    exact hS.ae_interpWeight_good hae (hε0 n)
  have hnn : ∀ μ ν : Measure (ContinuousPath ℂ), 0 ≤ levyProkhorovDist μ ν := fun _ _ => ENNReal.toReal_nonneg
  rw [tendstoInMeasure_iff_dist]
  intro θ hθ
  rw [ENNReal.tendsto_nhds_zero]
  intro r' hr'
  obtain ⟨r, hr0, hrr'⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ r' := by
    rcases eq_or_ne r' ⊤ with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨r'.toReal, ENNReal.toReal_pos hr'.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨a', ha'0, ha'r, ha'θ⟩ : ∃ a' : ℝ, 0 < a' ∧ a' ≤ r / 2 ∧ a' < θ :=
    ⟨min (r / 2) (θ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨δ, hδ0, hδ⟩ := hEqLaw ‖z₀‖ a' ha'0
  obtain ⟨δ', hδ'0, hδ'δ, hδ'1⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 :=
    ⟨min δ 1, lt_min hδ0 one_pos, min_le_left _ _, min_le_right _ _⟩
  have hD' : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) ‖z₀‖}
      ≤ ENNReal.ofReal (r / 2) :=
    (ENNReal.tendsto_nhds_zero.1 (hdiam ‖z₀‖ (δ' / 4) (by linarith))) _
      (ENNReal.ofReal_pos.2 (by linarith))
  have hεs : ∀ᶠ n in atTop, ε n < δ' / 2 := hε.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hδ, hD', hεs] with n hn1 hn2 hn3
  refine (measure_mono_ae (t := {ω | ENNReal.ofReal a' < walkLawModulus S η' (ε n) ‖z₀‖ δ ω} ∪
      {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) ‖z₀‖}) ?_).trans ?_
  · filter_upwards [hgood, hz₀] with ω hω hz hmem
    by_contra hnot
    have h2 : ¬ ENNReal.ofReal a' < walkLawModulus S η' (ε n) ‖z₀‖ δ ω := fun h => hnot (Or.inl h)
    have h3 : ¬ ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) ‖z₀‖ := fun h => hnot (Or.inr h)
    obtain ⟨hloc, hpos⟩ := hω n
    have hLP := pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell_of_nonneg S η' (hε0 n).le hloc hpos
      (R := ‖z₀‖) (δ := δ) (d := δ' / 4) (a := a') (by linarith) (by linarith) (by linarith) ha'0.le
      (not_lt.1 h3) (not_lt.1 h2) (hz n) le_rfl
    rw [pathLevyProkhorovEDist_eq_ofReal_dist, ENNReal.ofReal_le_ofReal_iff ha'0.le,
      LevyProkhorov.dist_probabilityMeasure_def] at hLP
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn _ _)] at hmem
    exact absurd hmem (not_le.2 (hLP.trans_lt ha'θ))
  · refine (measure_union_le _ _).trans ?_
    refine (add_le_add (hn1.trans (ENNReal.ofReal_le_ofReal ha'r)) hn2).trans ?_
    have hr2 : (0 : ℝ) ≤ r / 2 := by linarith
    rw [← ENNReal.ofReal_add hr2 hr2]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hrr'

end MatedCRT.FirstPass.Derived
