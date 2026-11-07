import MatedCRT.Proofs.Sec4.SubsequentialProperties.ProjectedHatDirichlet
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability

/-! Boundary comparison for finite discrete Dirichlet problems. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- The difference of two discrete harmonic extensions is bounded by the
difference of their boundary values. -/
theorem abs_dirichletData_sub_le_of_boundary {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hsucc : ∀ k, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (g h : ℤ → ℝ) {c : ℝ}
    (hbd : ∀ b ∈ vBoundary m A, |g b - h b| ≤ c) :
    ∀ a ∈ A ∪ vBoundary m A, |dirichletData m A g a - dirichletData m A h a| ≤ c := by
  let u := dirichletData m A g
  let v := dirichletData m A h
  have hlap : ∀ a ∈ A, lapSum hlf u a = 0 ∧ lapSum hlf v a = 0 := by
    intro a ha
    constructor <;> rw [← mLaplacian_mul_mdeg hlf] <;>
      simp [u, v, mLaplacian_dirichletData hlf hsucc hA _ ha]
  have hb : ∀ b ∈ vBoundary m A, |u b - v b| ≤ c := by
    intro b hb
    have hnot : b ∉ A := hb.1
    simpa [u, v, dirichletData_of_not_mem hA _ hnot] using hbd b hb
  have hupper : ∀ a ∈ A, u a - v a ≤ c := by
    have hw : ∀ a ∈ A, (u a - v a) - c ≤ 0 := by
      apply nonpos_of_lapSum_nonneg hlf hA (escape_of_adjacent_succ hsucc hA)
      · intro a ha
        have heq : lapSum hlf (fun b => u b - v b - c) a =
            lapSum hlf u a - lapSum hlf v a := by
          simp only [lapSum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [heq, (hlap a ha).1, (hlap a ha).2]
        norm_num
      · intro a ha b hab hbA
        have := (abs_le.mp (hb b ⟨hbA, a, ha, hab⟩)).2
        linarith
    intro a ha
    linarith [hw a ha]
  have hlower : ∀ a ∈ A, -(u a - v a) ≤ c := by
    have hw : ∀ a ∈ A, (v a - u a) - c ≤ 0 := by
      apply nonpos_of_lapSum_nonneg hlf hA (escape_of_adjacent_succ hsucc hA)
      · intro a ha
        have heq : lapSum hlf (fun b => v b - u b - c) a =
            lapSum hlf v a - lapSum hlf u a := by
          simp only [lapSum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [heq, (hlap a ha).1, (hlap a ha).2]
        norm_num
      · intro a ha b hab hbA
        have := (abs_le.mp (hb b ⟨hbA, a, ha, hab⟩)).1
        linarith
    intro a ha
    linarith [hw a ha]
  intro a ha
  rcases ha with ha | ha
  · exact abs_le.mpr ⟨by linarith [hlower a ha], hupper a ha⟩
  · exact hb a ha

/-- On a disk, comparison at the cells meeting its circle controls the two
harmonic extensions at every cell meeting its interior. -/
theorem abs_dirichletData_sub_le_on_disk {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hsucc : ∀ k, m k (k + 1) ≠ 0)
    {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} (hr : 0 < r)
    (hcells : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hA : (interiorCellVertices ε η (ball z r)).Finite) (g h : ℤ → ℝ) {c : ℝ}
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), |g b - h b| ≤ c) :
    ∀ a ∈ cellVertices ε η (ball z r),
      |dirichletData m (interiorCellVertices ε η (ball z r)) g a -
        dirichletData m (interiorCellVertices ε η (ball z r)) h a| ≤ c := by
  have hcmp := abs_dirichletData_sub_le_of_boundary hlf hsucc hA g h
    (fun b hb => hbd b (vBoundary_interiorCellVertices_subset hη hr hcells hb))
  intro a ha
  by_cases haA : a ∈ interiorCellVertices ε η (ball z r)
  · exact hcmp a (Or.inl haA)
  · have hs := mem_cellVertices_sphere_of_not_mem_interior hr ha haA
    simpa [dirichletData_of_not_mem hA _ haA] using hbd a hs

/-- A marked point in a cell meeting the circle is within three cell diameters
of its radial retraction onto the closed disk. -/
theorem dist_vertexPoint_ballRetraction_le_of_cell_sphere
    {ε r d : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {z : ℂ} (hr : 0 < r) {b : ℤ}
    (hb : b ∈ cellVertices ε η (sphere z r)) (hd : diam (cell ε η b) ≤ d) :
    dist (vertexPoint ε η b) (ballRetraction z r (vertexPoint ε η b)) ≤ 3 * d := by
  obtain ⟨y, hycell, hysphere⟩ := hb
  have hyball : y ∈ closedBall z r := sphere_subset_closedBall hysphere
  have hxy : dist (vertexPoint ε η b) y ≤ d :=
    (dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded
      (Tightness.vertexPoint_mem_cell hε b) hycell).trans hd
  have hret := dist_ballRetraction_le hr z (vertexPoint ε η b) y (mem_closedBall.mp hyball)
  rw [ballRetraction_of_mem z hr hyball] at hret
  have htri := dist_triangle (vertexPoint ε η b) y (ballRetraction z r (vertexPoint ε η b))
  rw [dist_comm y] at htri
  have hrdiv : r / r = 1 := div_self hr.ne'
  rw [hrdiv] at hret
  linarith

/-- Small boundary cells control the difference between the projected and
unprojected hat-data solutions on cells meeting the closed disk. -/
theorem abs_hat_dirichletData_projection_le
    {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hsucc : ∀ k, m k (k + 1) ≠ 0) {ε r d t : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hε : 0 < ε) {z : ℂ} (hr : 0 < r)
    (ht : 0 ≤ t)
    (hcells : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hA : (interiorCellVertices ε η (ball z r)).Finite)
    (hdiam : ∀ b ∈ cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (n : ℕ) (j l : ℤ) :
    ∀ a ∈ cellVertices ε η (closedBall z r),
      |dirichletData m (interiorCellVertices ε η (ball z r))
          (fun b => t * hat n j l (vertexPoint ε η b)) a -
        dirichletData m (interiorCellVertices ε η (ball z r))
          (fun b => t * hat n j l (ballRetraction z r (vertexPoint ε η b))) a| ≤
        t * (2 * n * (3 * d)) := by
  let g := fun b => t * hat n j l (vertexPoint ε η b)
  let h := fun b => t * hat n j l (ballRetraction z r (vertexPoint ε η b))
  have hbd : ∀ b ∈ cellVertices ε η (sphere z r), |g b - h b| ≤ t * (2 * n * (3 * d)) := by
    intro b hb
    have hd' := dist_vertexPoint_ballRetraction_le_of_cell_sphere hη hε hr hb (hdiam b hb)
    have hh := abs_hat_sub_le n j l (vertexPoint ε η b) (ballRetraction z r (vertexPoint ε η b))
    change |t * _ - t * _| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left hd' (by positivity))) ht
  have hcmp := abs_dirichletData_sub_le_on_disk hlf hsucc hη hr hcells hA g h hbd
  intro a ha
  obtain ⟨x, hxcell, hx⟩ := ha
  by_cases hxb : x ∈ ball z r
  · exact hcmp a ⟨x, hxcell, hxb⟩
  · have hxs : x ∈ sphere z r := by
      rw [mem_sphere]
      have hle := mem_closedBall.mp hx
      have hge : r ≤ dist x z := le_of_not_gt hxb
      exact le_antisymm hle hge
    have haA : a ∉ interiorCellVertices ε η (ball z r) := by
      intro haA
      exact haA.2 (by rw [frontier_ball z hr.ne']; exact ⟨x, hxcell, hxs⟩)
    simpa [g, h, dirichletData_of_not_mem hA _ haA] using hbd a ⟨x, hxcell, hxs⟩

/-- The projected and unprojected hat boundary data have asymptotically
equivalent harmonic extensions. -/
theorem hatDirichletProjectionStabilityStep (𝒮 : SpaceFillingSLEModel) :
    HatDirichletProjectionStabilityStep 𝒮 := by
  intro _h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hzr n j l δ hδ
  let d : ℝ := δ / (12 * ((n : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hsmall : 2 * (n : ℝ) * (3 * d) ≤ δ := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [d]
    have hden : 0 < 12 * ((n : ℝ) + 1) := by positivity
    have heq : 2 * (n : ℝ) * (3 * (δ / (12 * ((n : ℝ) + 1)))) =
        (6 * (n : ℝ) * δ) / (12 * ((n : ℝ) + 1)) := by ring
    rw [heq, div_le_iff₀ hden]
    nlinarith
  have hprob := hS.probTendsToOne_small_cells ρ d hd
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have hev := ENNReal.tendsto_nhds_zero.1 hprob e he
  filter_upwards [hev, self_mem_nhdsWithin] with ε hE hε
  calc
    S.P {ω | ∃ x ∈ closedBall z r,
      δ < |(rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b))) x -
        rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (ballRetraction z r (vertexPoint ε (S.η ω) b)))) x) - 0|} ≤
      S.P {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        diam (cell ε (S.η ω) k) ≤ d}ᶜ := by
      apply measure_mono_ae
      filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮),
        adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS,
        hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hlf hcells hp harea
      rintro ⟨x, hx, hbig⟩ hgood
      have hA : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
        (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset fun b hb => hb.1
      have hdiam : ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
          diam (cell ε (S.η ω) b) ≤ d := by
        intro b hb
        apply hgood b
        obtain ⟨y, hy, hys⟩ := hb
        refine ⟨y, hy, ?_⟩
        rw [mem_ball]
        have hyz := mem_sphere.mp hys
        have htri := dist_triangle y z 0
        simp only [dist_zero_right] at htri ⊢
        linarith
      have hbound := abs_hat_dirichletData_projection_le (t := S.mε ε) (hlf ε hε)
        (S.mult_succ_ne_zero hε.le ω) harea.1 hε hr (medianOf_nonneg _)
        (hcells ε hε) hA hdiam n j l (vertexOf ε (S.η ω) x)
        ⟨x, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x, hx⟩
      have hm : 0 ≤ S.mε ε := medianOf_nonneg _
      simp only [sub_zero, rescale, ← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hm)] at hbig
      have hmul := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hm)
      by_cases hm0 : S.mε ε = 0
      · simp [hm0] at hbig
        linarith
      · rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul] at hmul
        linarith
    _ ≤ e := hE

end MatedCRT
