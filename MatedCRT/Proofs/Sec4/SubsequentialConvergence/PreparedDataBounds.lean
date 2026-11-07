import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedLocalBounds
import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer
import MatedCRT.External.SLE

/-! The vertex estimates needed for prepared odometer compactness. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The small-mesh median scaling, equiboundedness and the corrected
Laplacian estimate imply the vertex bounds in the proof of Lemma 4.6. -/
theorem odometerPreparedDataBoundsStep_of_mepsScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) :
    OdometerPreparedDataBoundsStep 𝒮 := by
  intro h47 h44 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨K, hK, hscale⟩ := hm γ hγ hγ'
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  obtain ⟨φ, hφ, hbound⟩ := h47 γ hγ hγ' ρ hρ hρ' Ω S hS e he he0
  have hsmall : ∀ᶠ n in atTop, e (φ n) < ε₀ :=
    (he0.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hε₀)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hbound, h44 γ hγ hγ' ρ hρ hρ' Ω S hS,
    hS.isAreaParametrized, etaProperStep_holds 𝒮 γ hγ hγ' Ω S hS] with ω hb hl hη hp
  obtain ⟨B, hB⟩ := hb
  let C : ℝ := 1 + (|B| + 1) * K
  have hK0 : 0 < K := by linarith
  have hB0 : 0 < |B| + 1 := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsmall] with n hn
  have hε := he (φ n)
  have hs := hscale (e (φ n)) hε hn
  have hmpos : 0 < S.mε (e (φ n)) :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hK0) (inv_pos.mpr hε)) hs.1
  have hClarge : 1 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB0.le hK0.le]
  constructor
  · intro a ha
    have hla := (hl t (e (φ n)) ht hε).2.1 a ha
    have hi : ((matedDeg (S.mult (e (φ n)) ω) a : ℕ) : ℝ)⁻¹ ≤ 1 :=
      Nat.cast_inv_le_one _
    rw [abs_of_nonneg hla.1]
    exact hla.2.trans (hi.trans hClarge)
  · intro a ha
    by_cases hai : a ∈ ballInterior (e (φ n)) (S.η ω) ρ
    · obtain ⟨x, hx, hval⟩ := exists_rescale_eq_at_cell_of_area_parametrized
        hη hp hε a (S.mε (e (φ n)))
        (matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t)
      have hxball : x ∈ ball (0 : ℂ) ρ := Tightness.cell_subset_ball hη.1 hρ hai hx
      have hnrm := hB t ht n x hxball
      change |rescale (S.mε (e (φ n))) (e (φ n)) (S.η ω)
        (matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t) x| ≤ B at hnrm
      rw [hval, abs_mul, abs_of_pos (inv_pos.mpr hmpos)] at hnrm
      have hraw : |matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t a| ≤
          (|B| + 1) * S.mε (e (φ n)) := by
        have hmul := mul_le_mul_of_nonneg_left hnrm hmpos.le
        have hBabs : B ≤ |B| + 1 := by linarith [le_abs_self B]
        have hmul' := mul_le_mul_of_nonneg_right hBabs hmpos.le
        have hmne : S.mε (e (φ n)) ≠ 0 := ne_of_gt hmpos
        rw [← mul_assoc, mul_inv_cancel₀ hmne, one_mul] at hmul
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hs.2 hB0.le
      have hinv : 0 ≤ (e (φ n))⁻¹ := inv_nonneg.mpr hε.le
      have hfinal : (|B| + 1) * S.mε (e (φ n)) ≤ C / e (φ n) := by
        dsimp [C]
        rw [div_eq_mul_inv]
        nlinarith
      exact hraw.trans hfinal
    · have haW := Sec7.cellVertices_mono ball_subset_closedBall ha
      have hlo := Sec7.matedObstacle_le_matedLeastSupersolution
        (m := S.mult (e (φ n)) ω) (η := S.η ω) (ρ := ρ) hε ht haW
      have hhi := Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior
        (m := S.mult (e (φ n)) ω) hε ht haW hai
      have hz : matedObstacle (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t a = 0 :=
        matedObstacle_eq_zero_of_not_mem hai
      have hw : matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t a = 0 := by
        linarith
      rw [hw, abs_zero]
      exact div_nonneg hC.le hε.le

/-- Prepared local odometer compactness follows from the cited median scaling. -/
theorem odometerPreparedLocalCompactnessStep_of_mepsScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) :
    OdometerPreparedLocalCompactnessStep 𝒮 :=
  odometerPreparedLocalCompactnessStep_of_dataBounds 𝒮
    (odometerPreparedDataBoundsStep_of_mepsScaling 𝒮 hm)

/-- Corrected Lemma 4.6 follows from the cited estimates and the boundary
upgrade. -/
theorem subsequentialConvergencePrepared_of_mepsScaling_boundary
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hb : OdometerBoundaryUpgradeCorrectedStep 𝒮) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_local_boundary 𝒮 h47 h44 h31 h35
    (odometerPreparedLocalCompactnessStep_of_mepsScaling 𝒮 hm) hb

end MatedCRT
