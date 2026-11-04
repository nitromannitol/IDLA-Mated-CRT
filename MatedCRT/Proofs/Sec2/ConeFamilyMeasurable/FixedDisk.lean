import MatedCRT.Steps.Sec2.ConeHarmonicBalls

/-!
# The stopped cone family and a fixed obstacle problem

Before the half-ball stopping time, the obstacle characterization can be taken in
one fixed disk. This gives a reduction of process measurability to a simultaneous
measurable version of that obstacle process and the stopping time.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Every member of a half-ball stopped family is the regularized cluster in the disk of radius 3/4. -/
theorem IsConeHarmonicBallFamilyOn.eq_threeQuarterDisk_cluster {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T t : ℝ}
    (hf : IsConeHarmonicBallFamilyOn μ Λ T) (hs : IsStoppedAtHalfBall Λ T) (ht : t ∈ Ioo 0 T) :
    Λ t = interior (closure (cluster μ (3 / 4) 0 t)) := by
  exact (hf.2.2 t (1 / 2) ht (by norm_num) (hs.1 t ht) (3 / 4) (by norm_num)).1

/-- A simultaneous measurable obstacle process and a measurable stopping time
give a measurable stopped family process, up to a single null set. -/
theorem aemeasurable_familyProcess_of_threeQuarterDisk_cluster {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Ω → Measure ℂ} {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hT : AEMeasurable T P)
    (hcluster : AEMeasurable (fun ω (p : ℝ × ℂ) =>
      p.2 ∈ interior (closure (cluster (μ ω) (3 / 4) 0 p.1))) P)
    (hf : ∀ᵐ ω ∂P, IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P := by
  let T' := hT.mk T
  let C' := hcluster.mk _
  have hmeas : Measurable (fun ω (p : ℝ × ℂ) =>
      (0 < p.1 ∧ p.1 < T' ω) ∧ C' ω p) := by
    apply measurable_pi_iff.mpr
    intro p
    apply measurableSet_setOfPred.mp
    exact ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const hT.measurable_mk)).inter
        (measurableSet_setOfPred.mpr ((measurable_pi_apply p).comp hcluster.measurable_mk))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hf, hT.ae_eq_mk, hcluster.ae_eq_mk] with ω hω hTω hCω
  funext p
  apply propext
  dsimp only [T', C']
  simp only [familyProcess, mem_Ioo]
  rw [← hTω, ← hCω]
  constructor
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [hω.1.eq_threeQuarterDisk_cluster hω.2 ht]
    exact hx
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [hω.1.eq_threeQuarterDisk_cluster hω.2 ht] at hx
    exact hx

end MatedCRT
