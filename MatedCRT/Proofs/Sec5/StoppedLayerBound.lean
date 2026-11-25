import MatedCRT.Proofs.Sec5.StoppedSurplusSteps
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize
import MatedCRT.FirstPass.Derived.NearCellCount
import MatedCRT.FirstPass.Derived.GreenFunctionCrudeBoundHolds
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.CellInballDisjoint
import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S5u
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventBoundedModulus
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.Sec5.IDLALowerBound.Stopped
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Count
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec5.StoppedPoleBound
import MatedCRT.Proofs.Sec5.StoppedMeanValueInequality
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# The Green potential of the boundary layer, from the number of missing sites

The step `StoppedLayerPotentialStep` of Proposition 5.1 (the consultant's answer to target 9): with `A = V^ε(Λ_t)` and
`S = A \ Λ^ε_t`, on `{t < T}`, `ε ∑_{b ∈ S} g^ε_A(a, b) ≤ κ` for every `a ∈ A`, with probability tending to one. This
file splits the sum according to the distance `d = |η(a) - η(b)|`:

* `d < ε^{β₂}`: `g^ε_A ≤ G^ε_{B_ρ} ≤ ε^{-ζ}` (Lemma 2.15) and there are at most `ε^{-1+α₀}` such `b` ((5.41));
* `ε^{β₂} ≤ d < r`: `g^ε_A(a, b) ≤ C log(1/d) + C` (Lemma 2.14), and since each cell has mass `ε` and distinct cells
  meet in null sets, `ε ∑ (C log(1/d) + C) ≤ C (1 + log 2) 𝓜(B_{2r}(η(a)))`, which is small for small `r` (Lemma 2.17);
* `r ≤ d`: `g^ε_A(a, b) ≤ C log(1/r) + C`, so this part is at most `(C log(1/r) + C) ε #S`.

This is a simpler route than the square-sum bound of the answer: it needs only `ε #S → 0` on `{t < T}`.

## Main results

* `eps_mul_sum_log_le_largestExitTimeRV`: the middle range, deterministic;
* `eps_mul_layerSum_le`: the three ranges together, deterministic;
* `StoppedMissingSitesStep`: `ε #(V^ε(Λ_t) \ Λ^ε_t) → 0` in probability on `{t < T}` (open);
* `stoppedLayerPotential_of_missingSites`: `StoppedLayerPotentialStep` from Lemma 2.14 and `StoppedMissingSitesStep`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

/-- **The middle range of the layer sum** (deterministic). Let `η` be parametrized by `μ`-area, `ε > 0`, `0 < 2r ≤ 1`,
`C ≥ 0`, and let `s` be a finite set of vertices `b` with `0 < |z - η(b)| < r` whose cells lie in the annulus
`|z - η(b)|/2 ≤ |z - ·| ≤ 2|z - η(b)|`. Then `ε ∑_{b ∈ s} (C log(1/|z - η(b)|) + C) ≤ C (1 + log 2) 𝓜(B_{2r}(z))`. -/
theorem eps_mul_sum_log_le_largestExitTimeRV {μ : Measure ℂ} {η : ℝ → ℂ} (hpar : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) {r C : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hr2 : 2 * r ≤ 1) (s : Finset ℤ)
    (hs : ∀ b ∈ s, ∀ y ∈ cell ε η b,
      ‖z - vertexPoint ε η b‖ / 2 ≤ ‖z - y‖ ∧ ‖z - y‖ ≤ 2 * ‖z - vertexPoint ε η b‖)
    (hsr : ∀ b ∈ s, 0 < ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r)
    (hM : largestExitTimeRV μ (ball z (2 * r)) ≠ ⊤) :
    ε * ∑ b ∈ s, (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C) ≤
      C * (1 + Real.log 2) * (largestExitTimeRV μ (ball z (2 * r))).toReal := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hK : 0 ≤ C * (1 + Real.log 2) := mul_nonneg hC (by linarith)
  -- the terms are nonnegative
  have hX : ∀ b ∈ s, 0 ≤ C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C := by
    intro b hb
    obtain ⟨hd0, hdr⟩ := hsr b hb
    have : 0 ≤ Real.log (1 / ‖z - vertexPoint ε η b‖) :=
      Real.log_nonneg (one_le_one_div hd0 (by linarith))
    positivity
  -- pointwise comparison on each cell
  have hpt : ∀ b ∈ s, ∀ y ∈ cell ε η b, C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C ≤
      C * (1 + Real.log 2) * (Real.log (1 / ‖z - y‖) + 1) := by
    intro b hb y hy
    obtain ⟨h1, h2⟩ := hs b hb y hy
    obtain ⟨hd0, hdr⟩ := hsr b hb
    have hy0 : 0 < ‖z - y‖ := by linarith
    have hy1 : ‖z - y‖ ≤ 1 := by linarith
    have hL0 : 0 ≤ Real.log (1 / ‖z - y‖) := Real.log_nonneg (one_le_one_div hy0 hy1)
    have hle : 1 / ‖z - vertexPoint ε η b‖ ≤ 2 * (1 / ‖z - y‖) := by
      calc 1 / ‖z - vertexPoint ε η b‖ = 2 * (1 / (2 * ‖z - vertexPoint ε η b‖)) := by field_simp
        _ ≤ 2 * (1 / ‖z - y‖) := by gcongr
    have hlog1 : Real.log (1 / ‖z - vertexPoint ε η b‖) ≤ Real.log 2 + Real.log (1 / ‖z - y‖) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) hle
    have h3 := mul_le_mul_of_nonneg_left hlog1 hC
    nlinarith [mul_nonneg (mul_nonneg hC hlog2) hL0]
  have hsub : ∀ b ∈ s, cell ε η b ⊆ ball z (2 * r) := by
    intro b hb y hy
    obtain ⟨-, h2⟩ := hs b hb y hy
    obtain ⟨-, hdr⟩ := hsr b hb
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  have hstep : ∀ b ∈ s, ENNReal.ofReal (ε * (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C)) ≤
      ∫⁻ y in cell ε η b, ENNReal.ofReal (C * (1 + Real.log 2) * (Real.log (1 / ‖z - y‖) + 1)) ∂μ := by
    intro b hb
    calc ENNReal.ofReal (ε * (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C))
        = ENNReal.ofReal (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C) * μ (cell ε η b) := by
          rw [hpar.measure_cell hε, ← ENNReal.ofReal_mul (hX b hb), mul_comm]
      _ = ∫⁻ _ in cell ε η b, ENNReal.ofReal (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C) ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' (isCompact_cell hpar.1 ε b).isClosed.measurableSet
          fun y hy => ENNReal.ofReal_le_ofReal (hpt b hb y hy)
  have hsum : ENNReal.ofReal (ε * ∑ b ∈ s, (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C)) ≤
      ENNReal.ofReal (C * (1 + Real.log 2)) * largestExitTimeRV μ (ball z (2 * r)) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun b hb => mul_nonneg hε.le (hX b hb)]
    calc ∑ b ∈ s, ENNReal.ofReal (ε * (C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C))
        ≤ ∑ b ∈ s, ∫⁻ y in cell ε η b,
            ENNReal.ofReal (C * (1 + Real.log 2) * (Real.log (1 / ‖z - y‖) + 1)) ∂μ :=
          Finset.sum_le_sum hstep
      _ = ∫⁻ y in ⋃ b ∈ s, cell ε η b,
            ENNReal.ofReal (C * (1 + Real.log 2) * (Real.log (1 / ‖z - y‖) + 1)) ∂μ :=
          (lintegral_biUnion_finset₀ (fun j _ k _ hjk => hpar.measure_cell_inter hε hjk)
            (fun k _ => (isCompact_cell hpar.1 ε k).isClosed.measurableSet.nullMeasurableSet) _).symm
      _ ≤ ∫⁻ y in ball z (2 * r),
            ENNReal.ofReal (C * (1 + Real.log 2) * (Real.log (1 / ‖z - y‖) + 1)) ∂μ :=
          lintegral_mono_set (iUnion₂_subset hsub)
      _ = ENNReal.ofReal (C * (1 + Real.log 2)) *
            ∫⁻ y in ball z (2 * r), ENNReal.ofReal (Real.log (1 / ‖z - y‖) + 1) ∂μ := by
          simp_rw [ENNReal.ofReal_mul hK]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C * (1 + Real.log 2)) * largestExitTimeRV μ (ball z (2 * r)) := by
          gcongr
          exact le_iSup₂_of_le (f := fun z' (_ : z' ∈ ball z (2 * r)) =>
            ∫⁻ w in ball z (2 * r), ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) z
            (mem_ball_self (by linarith)) le_rfl
  have hM' : ENNReal.ofReal (C * (1 + Real.log 2)) * largestExitTimeRV μ (ball z (2 * r)) =
      ENNReal.ofReal (C * (1 + Real.log 2) * (largestExitTimeRV μ (ball z (2 * r))).toReal) := by
    rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hM]
  rw [hM'] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK ENNReal.toReal_nonneg)).1 hsum

/-- **The layer sum, all three ranges** (deterministic, one environment and one mesh `ε ∈ (0, 1]`). Let
`D = V^ε(B_ρ) \ V^ε(∂B_ρ)`, `A ⊆ D` finite, `S ⊆ A` finite and `a ∈ A`. Under the conclusions of Lemma 2.14
(constant `C`, exponent `β`), Lemma 2.15 (exponent `ζ`), the count (5.41) at `ε^{β₂}` (exponent `α₀`), cells meeting `B_ρ`
of diameter `≤ ε^{β₂}/2` and `𝓜(B_{2r}(z)) ≤ M₂` on `B_ρ`, with `β₂ ≤ β` and `ε^{β₂} ≤ r`, `2r ≤ 1`:
`ε ∑_{b ∈ S} g^ε_A(a, b) ≤ ε^{α₀ - ζ} + C (1 + log 2) M₂ + (C log(1/r) + C) ε #S`. -/
theorem eps_mul_layerSum_le {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (hpar : IsAreaParametrized μ η)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k, m k (k + 1) ≠ 0)
    {ε ρ β β₂ ζ α₀ C r M₂ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ₂β : β₂ ≤ β) (hC : 0 ≤ C)
    (hr : 0 < r) (hr2 : 2 * r ≤ 1) (hεr : ε ^ β₂ ≤ r) (hM₂ : 0 ≤ M₂)
    {A : Set ℤ} (hA : A.Finite) (hAD : A ⊆ interiorCellVertices ε η (ball 0 ρ))
    (hD : (interiorCellVertices ε η (ball 0 ρ)).Finite)
    (h214 : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ε ^ β ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b ≤
        C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) + C)
    (h215 : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) a b ≤ ε ^ (-ζ))
    (hnear : ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : Finset ℤ, (↑s : Set ℤ) ⊆ cellVertices ε η (ball z (ε ^ β₂)) →
      (s.card : ℝ) ≤ ε ^ (-1 + α₀))
    (hdiam : ∀ k, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ ε ^ β₂ / 2)
    (hM : ∀ z ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball z (2 * r)) ≤ ENNReal.ofReal M₂)
    (S : Finset ℤ) (hSA : (↑S : Set ℤ) ⊆ A) (a : ℤ) (ha : a ∈ A) :
    ε * ∑ b ∈ S, greenKernel m A a b ≤
      ε ^ (α₀ - ζ) + C * (1 + Real.log 2) * M₂ + (C * Real.log (1 / r) + C) * (ε * S.card) := by
  classical
  have hη : Continuous η := hpar.1
  have hvk : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hDV : interiorCellVertices ε η (ball (0 : ℂ) ρ) ⊆ cellVertices ε η (ball 0 ρ) := Set.sdiff_subset
  have hzρ : vertexPoint ε η a ∈ ball (0 : ℂ) ρ :=
    Sec7.cell_subset_ball_of_mem_interiorCellVertices hη (hAD ha) (hvk a)
  have haV : a ∈ cellVertices ε η (ball 0 ρ) := hDV (hAD ha)
  have hbV : ∀ b ∈ S, b ∈ cellVertices ε η (ball 0 ρ) := fun b hb => hDV (hAD (hSA hb))
  have hεβ : ε ^ β ≤ ε ^ β₂ := Real.rpow_le_rpow_of_exponent_ge hε hε1 hβ₂β
  have hεβ₂ : 0 < ε ^ β₂ := Real.rpow_pos_of_pos hε _
  have hgG : ∀ b, greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b ≤
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) a b := by
    intro b
    unfold greenKernel
    have h1 : (1 : ℝ) ≤ (mdeg m b : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (mdeg_ne_zero_of_ne_zero hlf (hcons b))
    exact div_le_self (greenFn_nonnegative m _ a b) h1
  have hmono : ∀ b, greenKernel m A a b ≤ greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b :=
    fun b => greenKernel_mono_of_finite hlf hcons hA hD hAD a b
  -- the three ranges, termwise
  set z := vertexPoint ε η a with hz
  set X : ℤ → ℝ := fun b => C * Real.log (1 / ‖z - vertexPoint ε η b‖) + C with hX
  have hterm : ∀ b ∈ S, ε * greenKernel m A a b ≤
      (if ‖z - vertexPoint ε η b‖ < ε ^ β₂ then ε * ε ^ (-ζ) else 0) +
      (if ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r then ε * X b else 0) +
      (if r ≤ ‖z - vertexPoint ε η b‖ then ε * (C * Real.log (1 / r) + C) else 0) := by
    intro b hb
    have hgA := (hmono b).trans (hgG b)
    by_cases h1 : ‖z - vertexPoint ε η b‖ < ε ^ β₂
    · have h2 : ¬ (ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r) := fun h => absurd h.1 (not_le.2 h1)
      have h3 : ¬ r ≤ ‖z - vertexPoint ε η b‖ := fun h => absurd (hεr.trans h) (not_le.2 h1)
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, add_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgA.trans (h215 a haV b (hbV b hb))) hε.le
    · have h1' : ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ := not_lt.1 h1
      have hg14 := (hmono b).trans (h214 a haV b (hbV b hb) (hεβ.trans h1'))
      rw [ite_eq_right h1, zero_add]
      by_cases h3 : r ≤ ‖z - vertexPoint ε η b‖
      · have h2 : ¬ (ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r) := fun h => absurd h.2 (not_lt.2 h3)
        rw [ite_eq_right h2, ite_eq_left h3, zero_add]
        refine mul_le_mul_of_nonneg_left (hg14.trans ?_) hε.le
        have hd0 : 0 < ‖z - vertexPoint ε η b‖ := hr.trans_le h3
        have hlog : Real.log (1 / ‖z - vertexPoint ε η b‖) ≤ Real.log (1 / r) :=
          Real.log_le_log (by positivity) (one_div_le_one_div_of_le hr h3)
        have := mul_le_mul_of_nonneg_left hlog hC
        linarith
      · have h2 : ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r := ⟨h1', not_le.1 h3⟩
        rw [ite_eq_left h2, ite_eq_right h3, add_zero]
        exact mul_le_mul_of_nonneg_left hg14 hε.le
  -- summing
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite,
    Finset.sum_ite] at hsum
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hsum
  -- the near range
  set S₁ := S.filter fun b => ‖z - vertexPoint ε η b‖ < ε ^ β₂ with hS₁
  have hS₁card : (S₁.card : ℝ) ≤ ε ^ (-1 + α₀) := by
    refine hnear z hzρ S₁ fun b hb => ?_
    have hb' := Finset.mem_filter.1 hb
    refine ⟨vertexPoint ε η b, hvk b, ?_⟩
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    exact hb'.2
  have hnearB : (S₁.card : ℝ) * (ε * ε ^ (-ζ)) ≤ ε ^ (α₀ - ζ) := by
    have hpos : 0 ≤ ε * ε ^ (-ζ) := by positivity
    calc (S₁.card : ℝ) * (ε * ε ^ (-ζ)) ≤ ε ^ (-1 + α₀) * (ε * ε ^ (-ζ)) :=
          mul_le_mul_of_nonneg_right hS₁card hpos
      _ = ε ^ (α₀ - ζ) := by
          rw [show ε * ε ^ (-ζ) = ε ^ (1 + -ζ) by rw [Real.rpow_add hε, Real.rpow_one],
            ← Real.rpow_add hε]
          congr 1
          ring
  -- the middle range
  set S₂ := S.filter fun b => ε ^ β₂ ≤ ‖z - vertexPoint ε η b‖ ∧ ‖z - vertexPoint ε η b‖ < r with hS₂
  have hMz := hM z hzρ
  have hMne : largestExitTimeRV μ (ball z (2 * r)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMz
  have hmid : ∑ b ∈ S₂, ε * X b ≤ C * (1 + Real.log 2) * M₂ := by
    rw [← Finset.mul_sum]
    refine (eps_mul_sum_log_le_largestExitTimeRV hpar hε z hC hr hr2 S₂ ?_ ?_ hMne).trans ?_
    · intro b hb y hy
      have hb' := Finset.mem_filter.1 hb
      have hdiamb : dist y (vertexPoint ε η b) ≤ ε ^ β₂ / 2 :=
        (dist_le_diam_of_mem (isBounded_cell hη b) hy (hvk b)).trans (hdiam b (hbV b hb'.1))
      rw [dist_eq_norm] at hdiamb
      have h1 : ‖z - vertexPoint ε η b‖ ≤ ‖z - y‖ + ‖y - vertexPoint ε η b‖ := by
        calc ‖z - vertexPoint ε η b‖ = ‖(z - y) + (y - vertexPoint ε η b)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖z - y‖ ≤ ‖z - vertexPoint ε η b‖ + ‖y - vertexPoint ε η b‖ := by
        calc ‖z - y‖ = ‖(z - vertexPoint ε η b) - (y - vertexPoint ε η b)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      constructor <;> linarith [hb'.2.1]
    · intro b hb
      have hb' := Finset.mem_filter.1 hb
      exact ⟨hεβ₂.trans_le hb'.2.1, hb'.2.2⟩
    · exact mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hM₂ hMz) (by positivity)
  -- the far range
  have hK3 : 0 ≤ C * Real.log (1 / r) + C := by
    have : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr (by linarith))
    positivity
  have hfar : ((S.filter fun b => r ≤ ‖z - vertexPoint ε η b‖).card : ℝ) * (ε * (C * Real.log (1 / r) + C)) ≤
      (C * Real.log (1 / r) + C) * (ε * S.card) := by
    have hc : ((S.filter fun b => r ≤ ‖z - vertexPoint ε η b‖).card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hε.le hK3)
    linarith
  linarith [hsum, hnearB, hmid, hfar]

/-- **The missing sites of the stopped cluster** (the first part of the consultant's answer to target 9): for every
`κ > 0`, on `{t < T}`, with probability tending to one, `ε #(V^ε(Λ_t) \ Λ^ε_t) ≤ κ`. Open: the answer derives it from the
interior bound of target 8, the null overlaps of the cells and `μ_h(∂Λ_t) = 0`. -/
def StoppedMissingSitesStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ κ : ℝ, 0 < κ →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ε * ((cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤ κ}

/-- `ε ↦ ε^x` tends to `0` as `ε → 0⁺`, for `x > 0`. -/
theorem tendsto_rpow_nhdsGT_zero_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => ε ^ x) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε ^ x) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ x)) :=
    ((Real.continuousAt_rpow_const 0 x (Or.inr hx.le)).tendsto).mono_left nhdsWithin_le_nhds
  rwa [Real.zero_rpow hx.ne'] at h

/-- `r ↦ (2r)^p` tends to `0` as `r → 0⁺`, for `p > 0`. -/
theorem tendsto_two_mul_rpow {p : ℝ} (hp : 0 < p) : Tendsto (fun r : ℝ => (2 * r) ^ p) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun r : ℝ => (2 * r) ^ p :=
    (continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hp.le
  have h : Tendsto (fun r : ℝ => (2 * r) ^ p) (𝓝[>] 0) (𝓝 ((2 * (0 : ℝ)) ^ p)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa [Real.zero_rpow hp.ne'] using h

/-- **`StoppedLayerPotentialStep` from Lemma 2.14 and the missing sites** (target 9). For `κ > 0` and a target
probability `η`, the radius `r` is chosen with `C (1 + log 2) (2r)^q < κ/3` and the failure probability of Lemma 2.17 at
`2r` below `η/3`; then `eps_mul_layerSum_le` bounds `ε ∑_{b ∈ S} g^ε_A(a, b)` by `κ` on the events of Lemmas 2.14,
2.15, (5.41), 2.8 and 2.17 and on `ε #S ≤ κ / (3 (C log(1/r) + C))`. -/
theorem stoppedLayerPotential_of_missingSites (𝒮 : SpaceFillingSLEModel) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (hmiss : StoppedMissingSitesStep 𝒮) : StoppedLayerPotentialStep 𝒮 := by
  intro _ _ _ _ _ _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht κ hκ
  have := hS.isProbabilityMeasure
  obtain ⟨β, hβ, h214'⟩ := h214 γ hγ hγ2
  obtain ⟨C, hC, h214''⟩ := h214' ρ hρ hρ1
  -- exponents
  have he0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have he1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hee : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
  obtain ⟨β₂, hβ₂def⟩ : ∃ β₂ : ℝ, β₂ = min β (1 / (2 + γ) ^ 2 / 2) := ⟨_, rfl⟩
  have hβ₂ : 0 < β₂ := by rw [hβ₂def]; exact lt_min hβ (by positivity)
  have hβ₂β : β₂ ≤ β := by rw [hβ₂def]; exact min_le_left _ _
  have hβ₂e : 2 * β₂ ≤ 1 / (2 + γ) ^ 2 := by
    rw [hβ₂def]
    linarith [min_le_right β (1 / (2 + γ) ^ 2 / 2)]
  obtain ⟨α₀, hα₀def⟩ : ∃ α₀ : ℝ, α₀ = nearCountExponent γ β₂ := ⟨_, rfl⟩
  have hα₀ : 0 < α₀ := by rw [hα₀def]; exact nearCountExponent_pos hγ hγ2 hβ₂
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = min (α₀ / 2) (1 / 2) := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by rw [hζdef]; exact lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := by rw [hζdef]; exact (min_le_right _ _).trans_lt (by norm_num)
  have hαζ : 0 < α₀ - ζ := by
    rw [hζdef]
    linarith [min_le_left (α₀ / 2) (1 / 2)]
  -- the events of polynomially high probability
  have hG14 := h214'' Ω S hS
  have hG15 := greenFunctionCrudeBoundStmt_holds 𝒮 γ hγ hγ2 ρ ζ hρ hρ1 hζ0 hζ1 Ω S hS
  have hNear := hS.polyHighProb_card_cellVertices_ball_le_exponent FirstPass.Derived.volumeGrowthStmt_holds
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮) hγ hγ2 hβ₂ hρ hρ1
  have hCell := FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 (1 / (2 + γ) ^ 2) ρ he0 he1 hρ hρ1 Ω S hS
  have hpoly := FirstPass36.polyHighProb_inter
    (FirstPass36.polyHighProb_inter (FirstPass36.polyHighProb_inter hG14 hG15) hNear) hCell
  -- Lemma 2.17 on small balls
  obtain ⟨q, hq, h217⟩ := firstPass_2_17 FirstPass.Derived.volumeGrowthStmt_holds γ hγ hγ2
  obtain ⟨p17, hp17, C17, r17, hr17, h17b⟩ := (h217 ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).2
  -- almost sure properties
  have hae : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)) ∧ IsConeHarmonicBallFamily (S.μ ω) (Λ ω) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      FirstPass.Derived.ae_isLocallyFiniteMult_of_isValid hS, hΛ] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  unfold TendsToOneOn
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  -- the radius `r`
  have hlimA : Tendsto (fun r : ℝ => ENNReal.ofReal (C17 * (2 * r) ^ p17)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_two_mul_rpow hp17).const_mul C17
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  have hlimB : Tendsto (fun r : ℝ => C * (1 + Real.log 2) * (2 * r) ^ q) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_two_mul_rpow hq).const_mul (C * (1 + Real.log 2))
    rwa [mul_zero] at h
  have hev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (min (1 / 2) (r17 / 2)) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (half_pos hr17))
  obtain ⟨r, hrI, hrA, hrB⟩ := (hev1.and
    ((ENNReal.tendsto_nhds_zero.1 hlimA (η / 3) hη3).and
      (hlimB.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < κ / 3))))).exists
  have hr : 0 < r := hrI.1
  have hr2 : 2 * r ≤ 1 := by linarith [hrI.2.trans_le (min_le_left _ _)]
  have hr17' : 2 * r < r17 := by linarith [hrI.2.trans_le (min_le_right _ _)]
  have hK₃ : 0 < C * Real.log (1 / r) + C := by
    have : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr (by linarith))
    positivity
  have hmissE := hmiss γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht (κ / (3 * (C * Real.log (1 / r) + C)))
    (by positivity)
  obtain ⟨G17, hG17def⟩ : ∃ G : Set Ω, G = {ω | ∀ y ∈ ball (0 : ℂ) ρ,
      largestExitTimeRV (S.μ ω) (ball y (2 * r)) ≤ ENNReal.ofReal ((2 * r) ^ q)} := ⟨_, rfl⟩
  have hG17P : S.P G17ᶜ ≤ η / 3 := by
    rw [hG17def]
    exact (h17b (2 * r) (by positivity) hr17').trans hrA
  -- the thresholds for `ε`
  have hr₁ : 0 < min 1 (min ((κ / 3) ^ (α₀ - ζ)⁻¹) ((min r (min (1 / 2) (ρ / 3))) ^ β₂⁻¹)) :=
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (lt_min hr (lt_min (by norm_num) (by positivity))) _))
  have hA : HarmonicBalls.PolyHighProb S.P fun ε => {ω | t < clusterExitTime (Λ ω) ρ →
      ε * ((cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤
        κ / (3 * (C * Real.log (1 / r) + C)) →
      ω ∈ G17 → ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b ≤ κ / ε} := by
    refine S3cBridge.polyHighProb_mono_ae_small hr₁ hpoly hae ?_
    intro ε hε hεr ω hω hgood hT hmissω hGω a ha
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hω
    obtain ⟨⟨⟨h14ω, h15ω⟩, hnearω⟩, hcellω⟩ := hω
    obtain ⟨hpar, hp, hlf, hΛω⟩ := hgood
    have hε1 : ε < 1 := hεr.trans_le (min_le_left _ _)
    have hεα : ε ^ (α₀ - ζ) < κ / 3 := rpow_lt_of_lt_rpow_inv hε.le (by positivity) hαζ
      (hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hεβ : ε ^ β₂ < min r (min (1 / 2) (ρ / 3)) :=
      rpow_lt_of_lt_rpow_inv hε.le (lt_min hr (lt_min (by norm_num) (by positivity))) hβ₂
        (hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hεβr : ε ^ β₂ ≤ r := hεβ.le.trans (min_le_left _ _)
    have hεβ12 : ε ^ β₂ ≤ 1 / 2 := hεβ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεβρ : ε ^ β₂ ≤ ρ / 3 := hεβ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hηc : Continuous (S.η ω) := hpar.1
    have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛω.2.1.monotoneOn ht hT
    have hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ β₂ / 2 := by
      intro k hk
      have h := (hcellω k hk).2
      rw [hee] at h
      have h1 : ε ^ (1 / (2 + γ) ^ 2) ≤ ε ^ (2 * β₂) := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hβ₂e
      have h2 : ε ^ (2 * β₂) = ε ^ β₂ * ε ^ β₂ := by rw [two_mul, Real.rpow_add hε]
      have h3 : ε ^ β₂ * ε ^ β₂ ≤ ε ^ β₂ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hεβ12 (Real.rpow_nonneg hε.le _)
      linarith
    have hAsub : cellVertices ε (S.η ω) (Λ ω t) ⊆ interiorCellVertices ε (S.η ω) (ball 0 ρ) := by
      intro k hk
      obtain ⟨w, hwc, hwΛ⟩ := hk
      have hw : ‖w‖ < ρ / 3 := mem_ball_zero_iff.1 (hΛt hwΛ)
      have hd := hdiam k ⟨w, hwc, mem_ball_zero_iff.2 (by linarith)⟩
      have hcellsub : ∀ x ∈ cell ε (S.η ω) k, ‖x‖ < 2 * ρ / 3 := by
        intro x hx
        have h1 : dist x w ≤ diam (cell ε (S.η ω) k) := dist_le_diam_of_mem (isBounded_cell hηc k) hx hwc
        have h2 : ‖x‖ ≤ ‖w‖ + dist x w := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
            _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
        linarith
      refine ⟨⟨w, hwc, mem_ball_zero_iff.2 (by linarith)⟩, ?_⟩
      rintro ⟨x, hxc, hxf⟩
      rw [frontier_ball (0 : ℂ) hρ.ne', mem_sphere_zero_iff_norm] at hxf
      linarith [hcellsub x hxc]
    have hAfin : (cellVertices ε (S.η ω) (Λ ω t)).Finite :=
      (cellVertices_ball_finite_of_proper hηc hp hε 0 (ρ / 3)).subset
        (fun k ⟨w, hwc, hwΛ⟩ => ⟨w, hwc, hΛt hwΛ⟩)
    have hDfin : (interiorCellVertices ε (S.η ω) (ball 0 ρ)).Finite :=
      (cellVertices_ball_finite_of_proper hηc hp hε 0 ρ).subset Set.sdiff_subset
    have hSfin := hAfin.sdiff (t := matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    have hSsub : (↑hSfin.toFinset : Set ℤ) ⊆ cellVertices ε (S.η ω) (Λ ω t) := by
      intro b hb
      exact (hSfin.mem_toFinset.1 hb).1
    have hGω' : ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball y (2 * r)) ≤
        ENNReal.ofReal ((2 * r) ^ q) := by
      rw [hG17def] at hGω
      exact hGω
    have hnear' : ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : Finset ℤ,
        (↑s : Set ℤ) ⊆ cellVertices ε (S.η ω) (ball z (ε ^ β₂)) → (s.card : ℝ) ≤ ε ^ (-1 + α₀) := by
      rw [hα₀def]
      exact hnearω
    have hmain := eps_mul_layerSum_le hpar (hlf ε hε) (fun k => S.mult_succ_ne_zero hε.le ω k) hε hε1.le
      hβ₂β hC.le hr hr2 hεβr (by positivity) hAfin hAsub hDfin h14ω h15ω
      hnear' hdiam hGω' hSfin.toFinset hSsub a ha
    rw [← Set.ncard_eq_toFinset_card _ hSfin] at hmain
    have hK : (C * Real.log (1 / r) + C) *
        (ε * ((cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ)) ≤
        κ / 3 := by
      have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (C * Real.log (1 / r) + C))).1 hmissω
      nlinarith [h3]
    rw [le_div_iff₀ hε]
    linarith [hmain, hεα.le, hrB.le, hK]
  have hE'' := StoppedMeanValue.tendsToOneOn_of_inter_on
    (E := fun ε => {ω | ω ∈ G17 → ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b ≤ κ / ε})
    hmissE (HarmonicBalls.PolyHighProb.probTendsToOne hA)
    (Eventually.of_forall fun ε ω hω hG => hω.2 hω.1.1 hω.1.2 hG)
  unfold TendsToOneOn at hE''
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hE'' (η / 3) hη3] with ε hε
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans ((add_le_add hε hG17P).trans ?_))
  · rintro ω ⟨hF, hE⟩
    by_cases hG : ω ∈ G17
    · exact Or.inl ⟨hF, fun h => hE (h hG)⟩
    · exact Or.inr hG
  · calc η / 3 + η / 3 ≤ η / 3 + η / 3 + η / 3 := le_self_add
      _ = η := ENNReal.add_thirds η

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.eps_mul_layerSum_le
#print axioms MatedCRT.stoppedLayerPotential_of_missingSites
