import HarmonicBalls.Proofs.Potential.GreenBall

/-! # Continuum boundary estimate for the Green kernel -/

open Set Metric

namespace MatedCRT

/-- A continuous function which vanishes on the sphere is uniformly small on a sufficiently
thin outer annulus. Continuity is only needed on an annulus away from an interior pole. -/
theorem exists_annulus_bound_of_continuousOn {z : ℂ} {r R : ℝ} {f : ℂ → ℝ}
    (hR : 0 ≤ R) (hRr : R < r)
    (hf : ContinuousOn f (closedBall z r \ ball z R))
    (hzero : ∀ x ∈ sphere z r, f x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ x ∈ closedBall z r \ closedBall z r', |f x| < δ := by
  let K := closedBall z r \ ball z R
  have hKclosed : IsClosed K := isClosed_closedBall.inter isOpen_ball.isClosed_compl
  have hKcompact : IsCompact K := (isCompact_closedBall (x := z) (r := r)).of_isClosed_subset hKclosed sdiff_subset
  let T := K ∩ (fun x => |f x|) ⁻¹' Ici δ
  have hTclosed : IsClosed T := hf.abs.preimage_isClosed_of_isClosed hKclosed isClosed_Ici
  have hTcompact : IsCompact T := hKcompact.of_isClosed_subset hTclosed inter_subset_left
  have hex : ∃ a : ℝ, R ≤ a ∧ a < r ∧ ∀ x ∈ T, dist x z ≤ a := by
    by_cases hT : T.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hTcompact.exists_isMaxOn hT ((continuous_id.dist continuous_const).continuousOn : ContinuousOn (fun x : ℂ => dist x z) T)
      have hxle : dist x z ≤ r := hx.1.1
      have hxR : R ≤ dist x z := le_of_not_gt hx.1.2
      have hxlt : dist x z < r := by
        refine lt_of_le_of_ne hxle ?_
        intro heq
        have hxsp : x ∈ sphere z r := heq
        have hfzero := hzero x hxsp
        have hbad : δ ≤ |f x| := hx.2
        rw [hfzero, abs_zero] at hbad
        linarith
      exact ⟨dist x z, hxR, hxlt, hmax⟩
    · exact ⟨R, le_rfl, hRr, fun x hx => (hT ⟨x, hx⟩).elim⟩
  obtain ⟨a, haR, har, ha⟩ := hex
  refine ⟨(a + r) / 2, by linarith, by linarith, ?_⟩
  intro x hx
  by_contra h
  have hbad : δ ≤ |f x| := le_of_not_gt h
  have hxr : (a + r) / 2 < dist x z := lt_of_not_ge hx.2
  have hxK : x ∈ K := ⟨hx.1, by change ¬ dist x z < R; linarith⟩
  have hxT : x ∈ T := ⟨hxK, hbad⟩
  linarith [ha x hxT]

/-- The continuum Green function of a ball centered at zero is uniformly small near
its boundary, including after multiplication by a fixed constant. -/
theorem greenFunction_centered_ball_boundary_small {r : ℝ} {y : ℂ}
    (hy : y ∈ ball (0 : ℂ) r) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧ ∀ x ∈ closedBall (0 : ℂ) r \ closedBall 0 r',
      |c * HarmonicBalls.greenFunction (ball 0 r) y x| < δ := by
  have hyr : dist y 0 < r := hy
  let R : ℝ := (dist y 0 + r) / 2
  have hR0 : 0 ≤ R := by dsimp [R]; linarith [dist_nonneg (x := y) (y := 0)]
  have hRr : R < r := by dsimp [R]; linarith
  have hyR : y ∈ ball (0 : ℂ) R := by change dist y 0 < R; dsimp [R]; linarith
  apply exists_annulus_bound_of_continuousOn hR0 hRr _ _ hδ
  · apply continuousOn_const.mul
    apply (HarmonicBalls.continuousOn_greenFunction_ball hy).mono
    intro x hx
    change x ≠ y
    intro hxy
    subst x
    exact hx.2 hyR
  · intro x hx
    have hxout : x ∉ ball (0 : ℂ) r := by
      intro hxb
      have hdist : dist x 0 = r := hx
      have hdist' : dist x 0 < r := hxb
      linarith
    rw [HarmonicBalls.greenFunction_of_notMem_right hxout, mul_zero]

end MatedCRT
