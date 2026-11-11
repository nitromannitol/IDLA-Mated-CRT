import MatedCRT.Proposed.GwynneMillerSheffield
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusPolynomialBound

/-! # Nested-disk survival under the GMS annulus estimate -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The GMS estimate may be used with a strictly subunit disconnection
probability, without changing its mesh exponents or exceptional-event bound. -/
theorem GMSAnnulusDisconnectionStmt.with_subunit_probability
    {𝒮 : SpaceFillingSLEModel} (hGMS : GMSAnnulusDisconnectionStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ p : ℝ, 0 < p ∧ p < 1 ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 1 →
      S.P {ω | ¬ ∀ z ∈ ball (0 : ℂ) ρ, ∀ r : ℝ,
        ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball 0 ρ →
        ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
            {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (r / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * r))) y w}} ≤
        ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨α, β, hα, hβ, hρ⟩ := hGMS γ hγ hγ2
  refine ⟨α, β, hα, hβ, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨p, hp, henv⟩ := hρ ρ hρ0 hρ1
  refine ⟨min p (1 / 2), lt_min hp (by norm_num), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro Ω _ S hS
    obtain ⟨C, ε₀, hC, hε₀, hbound⟩ := henv Ω S hS
    refine ⟨C, ε₀, hC, hε₀, ?_⟩
    intro ε hε hεsmall hε1
    calc
      _ ≤ S.P {ω | ¬ ∀ z ∈ ball (0 : ℂ) ρ, ∀ r : ℝ,
          ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball 0 ρ →
          ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
            ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
              {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (r / 2)),
                walkDisconnectsBeforeHit (S.mult ε ω)
                  (cellVertices ε (S.η ω) (sphere z (2 * r))) y w}} := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro z hz r hl hu hball x hx
        exact (ENNReal.ofReal_le_ofReal (min_le_left p (1 / 2))).trans
          (hgood z hz r hl hu hball x hx)
      _ ≤ _ := hbound ε hε hεsmall hε1

/-- On a good environment for the GMS annulus estimate, the probability of
surviving through nested disk boundaries has polynomial decay. The planar
separating walks and admissibility of the radii are kept explicit. -/
theorem measure_nested_disk_survival_le_power_of_gms
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (m : ℤ → ℤ → ℕ) (ε β ρ : ℝ) (η : ℝ → ℂ)
      (z : ℂ) (a : ℤ) (r : ℕ → ℝ) (n : ℕ) (U : ℕ → Set ℤ)
      (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      Continuous η → Antitone r → (∀ i ≤ n, 0 < r i) →
      a ∈ interiorCellVertices ε η (ball z (r n)) →
      a ∈ cellVertices ε η (ball z (r n / 2)) →
      (∀ v w, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty) →
      (∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (ball z (r i)), ∀ w,
        m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z (r i)) ∪
          cellVertices ε η (sphere z (r i))) →
      (∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z (r 0))) x ≠ ⊤) →
      (∀ i < n, cellVertices ε η (sphere z (r (i + 1))) ∩
        cellVertices ε η (ball z (r (i + 1))) ⊆
          cellVertices ε η (ball z (r i / 2))) →
      (∀ i ≤ n, ∃ y b, y ∈ cellVertices ε η (sphere z (r i / 4)) ∧
        b ∈ cellVertices ε η (sphere z (r i)) ∧
        ∃ w : (adjGraph m).Walk y b, ∀ u ∈ w.support, u ∉ U i) →
      z ∈ ball 0 ρ →
      (∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧
        ball z (2 * (r i / 2)) ⊆ ball 0 ρ) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε η (ball z s),
        ENNReal.ofReal p ≤ srwLaw m v
          {x | ∀ y ∈ cellVertices ε η (sphere z (s / 2)),
            walkDisconnectsBeforeHit m (cellVertices ε η (sphere z (2 * s))) y x}) →
      srwLaw m a {x | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
        vHitTime (cellVertices ε η (sphere z (r i))) x → x j ∈ U i} ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := measure_nested_disk_survival_le_power_of_disconnection hp hp1
  refine ⟨ν, hν, ?_⟩
  intro m ε β ρ η z a r n U cutoff distance factor hcut hdist hfactor hscale
    hη hr hpos ha haS hadj hnb hfin hnext hgeom hz hadmiss hgood
  apply hbound m ε η z a r n
    (fun i => cellVertices ε η (sphere z (r i / 4))) U
    (fun i => cellVertices ε η (ball z (r i / 2))) cutoff distance factor
    hcut hdist hfactor hscale hη hr hpos ha haS hadj hnb hfin hnext hgeom
  intro i hi v hv
  obtain ⟨hlow, hhigh, hball⟩ := hadmiss i hi
  have h := hgood z hz (r i / 2) hlow hhigh hball v hv
  convert h using 1; congr 2; ring

end MatedCRT
