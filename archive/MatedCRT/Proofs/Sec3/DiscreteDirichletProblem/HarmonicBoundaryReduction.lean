import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.HarmonicComparison
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! A probabilistic reduction of the Dirichlet boundary barrier. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory

/-- On any part of the closed disk, the probability of a large Dirichlet
error is controlled by the corresponding ordinary exit-time barrier and the
error of a discrete harmonic comparison function. -/
theorem measure_dirichlet_error_le_exitTime_add_harmonic
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε r M C δ : ℝ} {z : ℂ} (hε : 0 < ε) (hr : 0 < r)
    (hM : 0 ≤ M⁻¹) (hC : 0 ≤ C)
    (m : Ω → ℤ → ℤ → ℕ) (η : Ω → ℝ → ℂ)
    (u h : Ω → ℤ → ℝ) (f : Ω → ℂ → ℝ) (K : Set ℂ)
    (hK : K ⊆ closedBall z r)
    (hgood : ∀ᵐ ω ∂P,
      Continuous (η ω) ∧ Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (∀ j k, m ω j k ≠ 0 → (cell ε (η ω) j ∩ cell ε (η ω) k).Nonempty) ∧
      (∀ k, m ω k (k + 1) ≠ 0) ∧
      (∀ a ∈ interiorCellVertices ε (η ω) (ball z r),
        |matedLaplacian (m ω) (u ω) a| ≤ C) ∧
      (∀ a ∈ interiorCellVertices ε (η ω) (ball z r),
        matedLaplacian (m ω) (h ω) a = 0) ∧
      (∀ b ∈ cellVertices ε (η ω) (sphere z r), u ω b = h ω b) ∧
      (∀ a ∈ interiorCellVertices ε (η ω) (ball z r),
        expectedExitTime (m ω) (interiorCellVertices ε (η ω) (ball z r)) a ≠ ⊤) ∧
      (∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x))) :
    P {ω | ∃ x ∈ K, δ < |rescale M ε (η ω) (u ω) x - f ω x|} ≤
      P {ω | ∃ x ∈ K, δ / 2 < C * (M⁻¹ *
        (expectedExitTime (m ω) (interiorCellVertices ε (η ω) (ball z r))
          (vertexOf ε (η ω) x)).toReal)} +
      P {ω | ∃ x ∈ K, δ / 2 < |rescale M ε (η ω) (h ω) x - f ω x|} := by
  calc
    _ ≤ P ({ω | ∃ x ∈ K, δ / 2 < C * (M⁻¹ *
        (expectedExitTime (m ω) (interiorCellVertices ε (η ω) (ball z r))
          (vertexOf ε (η ω) x)).toReal)} ∪
      {ω | ∃ x ∈ K, δ / 2 < |rescale M ε (η ω) (h ω) x - f ω x|}) := by
        apply measure_mono_ae
        filter_upwards [hgood] with ω hg
        rintro ⟨x, hx, hxerr⟩
        obtain ⟨hη, hp, hadj, hsucc, hlap, hharm, hbd, hfin, hcell⟩ := hg
        have hb := abs_rescale_sub_harmonic_le_expectedExitTime hε hr hM hη hp
          hadj hsucc (u ω) (h ω) hC hlap hharm hbd hfin (hK hx) (hcell x hx)
        have ht := abs_sub_le (rescale M ε (η ω) (u ω) x)
          (rescale M ε (η ω) (h ω) x) (f ω x)
        by_cases he : δ / 2 < C * (M⁻¹ *
            (expectedExitTime (m ω) (interiorCellVertices ε (η ω) (ball z r))
              (vertexOf ε (η ω) x)).toReal)
        · exact Or.inl ⟨x, hx, he⟩
        · right
          refine ⟨x, hx, ?_⟩
          have := le_of_not_gt he
          linarith
    _ ≤ _ := measure_union_le _ _

end MatedCRT

#print axioms MatedCRT.measure_dirichlet_error_le_exitTime_add_harmonic
