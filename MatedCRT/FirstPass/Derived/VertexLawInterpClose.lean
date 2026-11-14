import MatedCRT.FirstPass.Derived.InterpWalkLawVertexBound
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.FirstPass.Derived.MepsUpperDeterministic

/-!
# The quenched law from the vertex of the origin is close in probability to the interpolated law at `0`

Along a sequence `ε_n → 0`, suppose that the vertex-indexed modulus of the quenched walk laws is small in
probability (the equicontinuity in law of the quenched walks, Berestycki–Gwynne (2020), Prop. 6.1).  Then the
quenched path law `Q^{ε_n}(a^{ε_n}_0)(ω)` started from the vertex of the cell containing `0` is within `b` of the
interpolated law `P̃^{ε_n}_0(ω)` in the Lévy–Prokhorov distance of `dUnif`, with probability tending to `1`, for every
`b > 0`.  This is the comparison of `P̃^ε_0` and `Q^ε(a^ε_0)` used to transfer the median normalisation
(Berestycki–Gwynne, end of the proof of Theorem 1.2) from the interpolated law to the walk from the vertex of `0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`Q^ε(a^ε_0)` and `P̃^ε_0` are close in probability.** -/
theorem tendsto_prob_pathLP_vertex_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    (a : ℕ → Ω → ℤ) (hav : ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n => S.P {ω | ENNReal.ofReal b < pathLevyProkhorovEDist
      (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω)
      (interpWalkLaw S η' (e n) ω 0)}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have h2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h2
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr0
  set a₀ : ℝ := min b r with ha₀
  have ha₀pos : 0 < a₀ := lt_min hb hrpos
  obtain ⟨δ, hδ0, hev1⟩ := hmod 1 a₀ ha₀pos
  set d : ℝ := min δ 1 / 4 with hd
  have hdpos : 0 < d := by
    have : 0 < min δ 1 := lt_min hδ0 one_pos
    simp only [hd]; positivity
  have hev2 := (ENNReal.tendsto_nhds_zero.1 (hdiam_of_isValid hS hae he 1 d hdpos)) (η / 2) h2
  have hev3 : ∀ᶠ n in atTop, e n < d := he.eventually (Iio_mem_nhds hdpos)
  filter_upwards [hev1, hev2, hev3] with n h1 h2' h3
  have hε : 0 < e n := he0 n
  set A : Set Ω := {ω | ENNReal.ofReal a₀ < walkLawModulus S η' (e n) 1 δ ω} with hA
  set B : Set Ω := {ω | ENNReal.ofReal d < maxCellDiam (e n) (⇑(η' ω)) 1} with hB
  have hsub : ∀ᵐ ω ∂S.P, ω ∈ {ω | ENNReal.ofReal b < pathLevyProkhorovEDist
      (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω)
      (interpWalkLaw S η' (e n) ω 0)} → ω ∈ A ∪ B := by
    filter_upwards [hae, hav n, hS.ae_interpWeight_good hae hε, hS.isAreaParametrized] with ω hω haω hw hpar hLP
    by_contra hnot
    simp only [mem_union, not_or, hA, hB, Set.mem_ofPred_eq, not_lt] at hnot
    obtain ⟨hmω, hDω⟩ := hnot
    have hmin : min δ 1 ≤ δ := min_le_left _ _
    have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
    have hdle : d ≤ δ / 4 := by simp only [hd]; linarith
    have hd1 : d ≤ 1 / 4 := by simp only [hd]; linarith
    have hzj : (0 : ℂ) ∈ cell (e n) (⇑(η' ω)) (a n ω) := by
      rw [hω, haω]
      exact zero_mem_cell_vertexOf hε.le hpar.2.1
    have hle := pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell S η' hε hw.1 hw.2
      (R := 1) (δ := δ) (d := d) (a := a₀) hdpos.le (by linarith) (by linarith) ha₀pos.le hDω hmω
      (z := 0) (by simp) hzj
    exact absurd hLP (not_lt.2 (hle.trans (ENNReal.ofReal_le_ofReal (min_le_left b r))))
  calc S.P _ ≤ S.P (A ∪ B) := measure_mono_ae hsub
    _ ≤ S.P A + S.P B := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := by
        gcongr
        · refine h1.trans ((ENNReal.ofReal_le_ofReal (min_le_right b r)).trans ?_)
          rw [ENNReal.ofReal_coe_nnreal]
          exact hr.le
    _ = η := ENNReal.add_halves η

end MatedCRT.FirstPass.Derived
