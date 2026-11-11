import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DyadicAnnulusScales

/-! # Geometric admissibility of nested annuli -/

namespace MatedCRT

open Metric Set MeasureTheory

/-- Dyadic annuli obey the scale and containment requirements of the GMS
boundary-hitting estimate when the cutoff dominates the mesh scale and the
boundary clearance, and the outer radius remains inside the ambient disk. -/
theorem exists_admissible_dyadic_annulus_scales
    {cutoff distance ε β ρ R buffer margin : ℝ} {η : ℝ → ℂ} {z x : ℂ}
    (hc : 0 < cutoff) (hd : cutoff ≤ distance)
    (hmesh : 2 * ε ^ β ≤ cutoff)
    (hclear : 4 * (R + buffer - dist z x + margin) < cutoff)
    (hcontain : 2 * distance + dist z 0 ≤ ρ) :
    ∃ (n : ℕ) (r : ℕ → ℝ),
      Antitone r ∧ r n = cutoff ∧ r 0 ≤ distance ∧
      distance ≤ cutoff * (2 : ℝ) ^ (n + 1) ∧
      (∀ i ≤ n, 0 < r i ∧
        R + buffer - dist z x + margin < r i / 4 ∧
        ball z (2 * r i) ⊆ ball 0 ρ) ∧
      (∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧
        ball z (2 * (r i / 2)) ⊆ ball 0 ρ) ∧
      (∀ i < n, cellVertices ε η (sphere z (r (i + 1))) ∩
        cellVertices ε η (ball z (r (i + 1))) ⊆
          cellVertices ε η (ball z (r i / 2))) := by
  obtain ⟨n, r, hanti, hpos, hlast, hfirst, _, hstep, hscale⟩ :=
    exists_dyadic_annulus_scales hc hd
  have hbounds : ∀ i ≤ n, cutoff ≤ r i ∧ r i ≤ distance := by
    intro i hi
    exact ⟨hlast ▸ hanti hi, (hanti (Nat.zero_le i)).trans hfirst⟩
  refine ⟨n, r, hanti, hlast, hfirst, hscale, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hlow, hhigh⟩ := hbounds i hi
    refine ⟨hpos i, by linarith, ?_⟩
    apply Metric.ball_subset_ball'
    linarith
  · intro i hi
    obtain ⟨hlow, hhigh⟩ := hbounds i hi
    have hp := hpos i
    have hdist := dist_nonneg (x := z) (y := (0 : ℂ))
    refine ⟨by linarith, by linarith, ?_⟩
    apply Metric.ball_subset_ball'
    linarith
  · apply nested_disk_restart_subset r n
    intro i hi
    exact (hstep i hi).le

/-- For a walk starting in the smaller disk, the probability of hitting a
larger concentric boundary before a target is bounded by the corresponding
probability for the smaller boundary. -/
theorem srwLaw_sphere_hit_order_le_of_radius_le
    {m : ℤ → ℤ → ℕ} {ε r R : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hη : Continuous η) (hr : 0 < r) (hrR : r ≤ R)
    (ha : a ∈ interiorCellVertices ε η (ball z r))
    (hnb : ∀ ρ ∈ ({r, R} : Set ℝ),
      ∀ v ∈ interiorCellVertices ε η (ball z ρ), ∀ w,
        m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z ρ) ∪
          cellVertices ε η (sphere z ρ))
    (hfin : ∀ᵐ path ∂srwLaw m a,
      vExitTime (interiorCellVertices ε η (ball z R)) path ≠ ⊤)
    (B : Set ℤ) :
    srwLaw m a {path | vHitTime (cellVertices ε η (sphere z R)) path ≤
      vHitTime B path} ≤
    srwLaw m a {path | vHitTime (cellVertices ε η (sphere z r)) path ≤
      vHitTime B path} := by
  apply measure_mono_ae
  filter_upwards [ae_sphereCellHits_ordered hη hr hrR ha hnb hfin] with path horder
  intro h
  exact horder.2.2.trans h

end MatedCRT

#print axioms MatedCRT.exists_admissible_dyadic_annulus_scales
#print axioms MatedCRT.srwLaw_sphere_hit_order_le_of_radius_le
