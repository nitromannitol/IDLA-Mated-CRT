import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRestrictedLawTransfer
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapVolumeGrowthRepresentative

/-! # Transfer of fixed-time regularization -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls

/-- Fixed-time absence of confined regularization defects transfers across
identical laws of the restricted measures, provided both measures have the
regularity needed for the common measurable defect representative. -/
theorem ae_no_regularization_defect_of_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {μ : Ω → Measure ℂ} {ν : Ω' → Measure ℂ}
    {r t : ℝ} {z : ℂ} (hr : 0 < r) (ht : 0 < t) (hz : z ∈ ball 0 r)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (μ ω) r βm βp)
    (hν : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (ν ω) r βm βp)
    (hident : IdentDistrib (fun ω => (μ ω).restrict (ball 0 r))
      (fun ω => (ν ω).restrict (ball 0 r)) P Q)
    (hgood : ∀ᵐ ω ∂Q, closure (cluster (ν ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (ν ω) r z t)) = cluster (ν ω) r z t) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (μ ω) r z t)) = cluster (μ ω) r z t := by
  obtain ⟨E, hE, hrep⟩ := exists_measurable_restricted_cluster_regularity_defect hr hz ht
  have hnotν : ∀ᵐ ω ∂Q, (ν ω).restrict (ball 0 r) ∉ E := by
    filter_upwards [hν, hgood] with ω hν hgood
    intro hmem
    have hbad := (hrep (ν ω) hν.1 hν.2).mp hmem
    exact hbad.2 (hgood hbad.1)
  have hnotμ : ∀ᵐ ω ∂P, (μ ω).restrict (ball 0 r) ∉ E :=
    hident.symm.ae_mem_snd hE.compl hnotν
  filter_upwards [hμ, hnotμ] with ω hμ hnot hcl
  by_contra hne
  exact hnot ((hrep (μ ω) hμ.1 hμ.2).mpr ⟨hcl, hne⟩)

end MatedCRT
