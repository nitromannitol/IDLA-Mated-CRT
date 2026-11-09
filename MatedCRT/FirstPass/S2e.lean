import MatedCRT.FirstPass.S2d
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppingTime
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ClusterDecoder

/-! # FIRST PASS S2e: measurability of the stopped cone family without strict growth

The Sec2 chain (`Proofs/Sec2/ConeFamilyMeasurable/StoppingTime.lean`) proves the measurability of the half-ball
stopping time from `ConeHarmonicBallStrictGrowthStep`, through `IsStrictlyGrowingOn`. That input is not a result of the
paper (`Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:109`). Its only use in the reverse direction of
`halfBallTest_iff_lt` is the containment `closure (Λ q) ⊆ B_{1/2}` for `0 < q < T`, which
`ConeHalfBallClosureInsideStep` (`FirstPass/S2d.lean`, NEW, proved from EXTERNAL inputs) supplies directly.

This file re-proves the first conjunct of `ConeFamilyAEMeasurableStep` with that closure input in place of strict growth.
Written argument: `notes/fp-gaps/G-S2-measurable.md` Sections 4 (the endpoint identity `T = τ(μ)`) and the stopping
time reduction; the Lean reduction is the one of `StoppingTime.lean`, with the hypotheses changed as stated. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- Strict-growth-free form of `halfBallTest_iff_lt`: with the closure containment `closure (Λ t) ⊆ B_{1/2}` for
`0 < t < T` in place of `IsStrictlyGrowingOn Λ T`, the rational half-ball test of `C q` is `q < T`. -/
theorem halfBallTest_iff_lt_of_closureInside {C : Ioi (0 : ℝ) → Set ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (ho : ∀ t, IsOpen (C t)) (hm : Monotone C)
    (heq : ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t)
    (hs : IsStoppedAtHalfBall Λ T) (hcl : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2))
    (q : PositiveRational) : halfBallTest (C ⟨q, q.property⟩) ↔ (q : ℝ) < T := by
  constructor
  · rintro ⟨r, hr, htest⟩
    by_contra hq
    have hTq : T ≤ (q : ℝ) := le_of_not_gt hq
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    obtain ⟨t, ht, hx⟩ := hs.2 r' hr'
    have hsub := (closure_subset_closedBall_of_halfBallTest (ho ⟨q, q.property⟩) htest)
    apply hx
    intro x hxΛ
    have hxC : x ∈ C ⟨t, ht.1⟩ := by rwa [heq t ht]
    have hxq := (hm (show (⟨t, ht.1⟩ : Ioi (0 : ℝ)) ≤ ⟨q, q.property⟩ from
      le_of_lt (ht.2.trans_le hTq))) hxC
    have hdist : dist x 0 ≤ (r : ℝ) := hsub (subset_closure hxq)
    exact hdist.trans_lt hrr'
  · intro hq
    obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball isClosed_closure (hcl (q : ℝ) ⟨q.property, hq⟩)
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    refine ⟨r', hr', fun n hn => ?_⟩
    rw [heq q ⟨q.property, hq⟩] at hn
    exact le_of_lt ((hsub (subset_closure hn)).trans hrr')

/-- Strict-growth-free form of `aemeasurable_stoppingTime_of_open_family`: a stopped family agreeing with a measurable
increasing open family, with the closure containment `closure (Λ t) ⊆ B_{1/2}` for `0 < t < T`, has an a.e. measurable
stopping time. -/
theorem aemeasurable_stoppingTime_of_open_family_closureInside
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {C : Ω → Ioi (0 : ℝ) → Set ℂ} {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hC : AEMeasurable C P)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ (∀ t, IsOpen (C ω t)) ∧ Monotone (C ω) ∧
      (∀ t (ht : t ∈ Ioo 0 (T ω)), C ω ⟨t, ht.1⟩ = Λ ω t) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧
      (∀ t ∈ Ioo 0 (T ω), closure (Λ ω t) ⊆ ball (0 : ℂ) (1 / 2))) :
    AEMeasurable T P := by
  let C' := hC.mk C
  have hmeas : Measurable (fun ω => (halfBallTestHorizon (C' ω)).toReal) :=
    (measurable_halfBallTestHorizon.comp hC.measurable_mk).ennreal_toReal
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hf, hC.ae_eq_mk] with ω hω heq
  have htest : ∀ q : PositiveRational,
      halfBallTest (C ω ⟨q, q.property⟩) ↔ (q : ℝ) < T ω :=
    fun q => halfBallTest_iff_lt_of_closureInside hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1 hω.2.2.2.2.2 q
  have hh := congrArg ENNReal.toReal (halfBallTestHorizon_eq htest)
  simpa only [← heq, C', ENNReal.toReal_ofReal hω.1.le] using hh

/-- Strict-growth-free form of `aemeasurable_coneHalfBallStoppingTime`: the half-ball stopping time of a cone
harmonic-ball family (Lemma 2.4 properties on `(0, T)`, stopped at `∂B_{1/2}`, with closure containment) is a.e.
measurable. The canonical open family `C ω t = int (closure (cluster (μ ω) (3/4) 0 t))` is a.e. measurable by
`aemeasurable_regularizedClusterFamily_of_volumeGrowth` (volume growth and the LQG measure), and monotone by
`cluster_subset_of_general` (Harmonic-Balls-LQG). -/
theorem aemeasurable_coneHalfBallStoppingTime_closureInside
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hcl : ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T →
      IsStoppedAtHalfBall Λ T → ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2))
    {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) : AEMeasurable T P := by
  let C : Ω → Ioi (0 : ℝ) → Set ℂ := fun ω t =>
    interior (closure (cluster (μ ω) (3 / 4) 0 t))
  let curry : ((Ioi (0 : ℝ) × ℂ) → Prop) → Ioi (0 : ℝ) → Set ℂ :=
    fun F t x => F (t, x)
  have hcurry : Measurable curry := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro x
    exact measurable_pi_apply (t, x)
  have hg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) (3 / 4) βminus βplus :=
    hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)
  have hCm : AEMeasurable C P := hcurry.comp_aemeasurable
    (aemeasurable_regularizedClusterFamily_of_volumeGrowth (by norm_num)
      hcone.aemeasurable_lqgMeasure hg)
  apply aemeasurable_stoppingTime_of_open_family_closureInside hCm
  filter_upwards [hf, hg, hcl] with ω hω hv hclω
  refine ⟨hω.1, (fun _ => isOpen_interior), ?_, ?_, hω.2.2, hclω _ _ hω.2.1 hω.2.2⟩
  · intro s t hst
    apply interior_mono (closure_mono ?_)
    obtain ⟨hμω, βm, βp, hV⟩ := hv
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hμω (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  · intro t ht
    exact (hω.2.1.eq_threeQuarterDisk_cluster hω.2.2 ht).symm

/-- Strict-growth-free form of `aemeasurable_coneHalfBallPair`: the pair (circle average process, stopped family
process) of a cone harmonic-ball family is a.e. measurable, with the closure containment in place of strict growth. -/
theorem aemeasurable_coneHalfBallPair_closureInside
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hcl : ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T →
      IsStoppedAtHalfBall Λ T → ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2))
    {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω))) P := by
  have hT := aemeasurable_coneHalfBallStoppingTime_closureInside hγ hγ2 hcone h27 hcl hf
  have hΛ := aemeasurable_coneFamilyProcess hγ hγ2 hcone h27 hT (hf.mono fun _ h => h.2)
  have hc : Measurable (fun ω => circleProcess (hcirc ω)) := by
    apply Measurable.of_eval
    intro p
    exact hcone.2.1.measurable_circle p.1 p.2 p.1.property
  exact hc.aemeasurable.prodMk hΛ

end MatedCRT
