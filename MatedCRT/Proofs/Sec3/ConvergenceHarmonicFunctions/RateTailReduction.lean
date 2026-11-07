import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateDiscrepancy
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry

/-! # Reduction of the quenched exit-value tail to the excursion tail -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls Filter Topology
open scoped NNReal

/-- For a walk started at an interior cell, a tail bound on the separation
of its two stopping locations bounds the same-walk exit-value tail. Finite
Euclidean exit is stated explicitly; it is supplied by the finite-domain
walk argument in the annulus iteration. -/
theorem srwLaw_sameWalkExitDiscrepancy_tail_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) (v : ℤ)
    (hη : Continuous (S.η ω))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    (hfin : ∀ᵐ x ∂srwLaw (S.mult ε ω) v,
      pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤)
    (s : ℝ) :
    (srwLaw (S.mult ε ω) v)
      {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
    (srwLaw (S.mult ε ω) v)
      {x | s < dist (pathExitPosition (ball z r)
          (interpolatedWalk ε (S.η ω) (S.mε ε) x))
        (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))} := by
  apply measure_mono_ae
  filter_upwards [srwLaw_ae_start (S.mult ε ω) v, hfin] with x hx hxf
  intro hbad
  have hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r := by
    have hzero : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 =
        vertexPoint ε (S.η ω) v := by
      simp [interpolatedWalk, hx]
    rw [hzero]
    exact Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hv
      (Sec7.vertexPoint_mem_cell hε v)
  exact location_distance_lt_of_sameWalkExitDiscrepancy_gt S hr z ψ hψ ε ω x hstart hxf hbad

/-- A walk on a locally finite graph containing the consecutive edges has
finite Euclidean exit time from a bounded disk whenever the embedded curve
is proper and the interpolation has positive speed. -/
theorem srwLaw_ae_interpolatedWalk_exit_ball_lt_top
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z : ℂ) (r : ℝ) (v : ℤ) :
    ∀ᵐ x ∂srwLaw m v, pathExitTime (ball z r) (interpolatedWalk ε η c x) < ⊤ := by
  let A : Set ℤ := {k | vertexPoint ε η k ∈ ball z r}
  have hA : A.Finite := by
    apply (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset
    intro k hk
    exact ⟨vertexPoint ε η k, Sec7.vertexPoint_mem_cell hε.le k, hk⟩
  have hmean := Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hA v
  filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A v hmean] with x hx
  have hex : ∃ n, x n ∉ A := by
    by_contra hn
    apply hx
    simp [vExitTime, hn]
  obtain ⟨n, hn⟩ := hex
  have hout : interpolatedWalk ε η c x ((n / c : ℝ).toNNReal) ∉ ball z r := by
    rw [interpolatedWalk_natCast_div hc]
    exact hn
  unfold pathExitTime
  exact lt_of_le_of_lt (sInf_le ⟨_, rfl, hout⟩) ENNReal.coe_lt_top

/-- The polynomial discrepancy threshold in the corrected lemma reduces to
the excursion scale `ε^(q/χ)/2`, with no dependence on the Hölder constant
in the excursion event. -/
theorem srwLaw_sameWalkExitDiscrepancy_rpow_tail_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hχ : 0 < χ) (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hη : Continuous (S.η ω))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    (hfin : ∀ᵐ x ∂srwLaw (S.mult ε ω) v,
      pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤)
    (q : ℝ) :
    (srwLaw (S.mult ε ω) v)
      {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
    (srwLaw (S.mult ε ω) v)
      {x | ε ^ (q / (χ : ℝ)) / 2 < dist (pathExitPosition (ball z r)
          (interpolatedWalk ε (S.η ω) (S.mε ε) x))
        (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))} := by
  let s : ℝ := ε ^ (q / (χ : ℝ)) / 2
  have hχ' : (χ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hχ)
  have hs : (2 * s) ^ (χ : ℝ) = ε ^ q := by
    dsimp [s]
    rw [show 2 * (ε ^ (q / (χ : ℝ)) / 2) = ε ^ (q / (χ : ℝ)) by ring,
      ← Real.rpow_mul hε.le]
    congr 1
    exact div_mul_cancel₀ q hχ'
  have hthresh : (H : ℝ) * (2 * s) ^ (χ : ℝ) ≤ (1 + (H : ℝ)) * ε ^ q := by
    rw [hs]
    have he := Real.rpow_nonneg hε.le q
    nlinarith
  calc
    (srwLaw (S.mult ε ω) v)
        {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
      (srwLaw (S.mult ε ω) v)
        {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} :=
          measure_mono (fun _ hx => hthresh.trans_lt hx)
    _ ≤ _ := srwLaw_sameWalkExitDiscrepancy_tail_le S hr z ψ hψ hε.le ω v hη hv hfin s

end MatedCRT
