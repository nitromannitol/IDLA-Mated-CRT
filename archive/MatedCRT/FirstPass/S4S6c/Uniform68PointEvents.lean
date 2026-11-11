import MatedCRT.FirstPass.S4S6c.Uniform68Point
import MatedCRT.FirstPass.S4S6c.Uniform68Local

/-!
# The local test `hloc` at one sphere-band start vertex, from the probabilistic events

`hloc_band_point_events` is `Uniform68Point.hloc_band_point` with its two event inputs supplied by the Draft event forms
that is proved uniform in scale and vertex (`Uniform68Point` inputs `hGreenLow`, `hdraft`):

* `hG`: the Green event of Draft Lemma 2.16 at one `ω` (the event `G` of `FirstPass/S6f.lean`, `draft68_events_probTendsToOne`),
  turned into `hGreenLow` by `Uniform68Local.greenLow_of_event` at the radius `R/8`;
* `hD`: the exit-moment event of Draft Lemma 2.18 at one `ω` (the event `X` of `S6f.lean`, with the mass threshold `ε^α`),
  turned into `hdraft` by `Uniform68Local.exitMoment_of_event` with `δ = ε^α` and the exit constant `CE`.

The thickening parameter of `hloc_band_point` is `δ = ε^α`, and `ε^α ≤ R/100` is a parameter relation (small `ε`).

Terminology: Duplantier-Sheffield annulus; Armitage-Gardiner potential kernel; Green kernel of the walk (Lawler, Berestycki-Gwynne).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace MatedCRT

theorem hloc_band_point_events {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {b : ℤ} {ctr : ℂ}
    {ε ρ ω₀ α R r c0 CG Cg CE KL d s1 β : ℝ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hεα : ε ^ α ≤ R / 100) (hCE : 0 < CE) (hCg : 0 < Cg) (hKL : 0 < KL) (hCG : 0 < CG)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0_24 : c0 ≤ 1 / 24)
    (hc0C : c0 ≤ Real.exp (-(2 * CG)) / 16) (hεc : ε ≤ 16 * c0)
    (hd : d ≤ R / 100)
    (hsm : ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d)
    (hband : (closure (cell ε η b) ∩ sphere ctr (4 * R / 3)).Nonempty)
    (hA : A.Finite) (hsparse : (A.ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hs : s1 * r ^ (2 * β) ≤ (μ (ball (vertexPoint ε η b) (c0 * R))).toReal / 4)
    (hmr : 0 < (μ (ball (vertexPoint ε η b) (c0 * R))).toReal)
    (hgood : IsGoodAnnulusEvent μ c0 Cg R ctr)
    (hRr : c0 * R ≤ r)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η b) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ c0 * R)
    -- the Green event of Draft Lemma 2.16 at one ω (event G of S6f)
    (hG : ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r' : ℝ, ε ^ ω₀ ≤ r' →
      r' ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) →
      ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r' / 3)),
      CG⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min (r' / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r')) a b')
    (hb : b ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀))) (hlo : ε ^ ω₀ ≤ R / 8)
    (hup : R / 8 ≤ infDist (vertexPoint ε η b) (sphere 0 ρ))
    -- the exit-moment event of Draft Lemma 2.18 at one ω (event X of S6f), mass threshold ε^α
    (hD : ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ^ N)
    (hsub : ball (vertexPoint ε η b) (R / 4) ⊆ ball 0 ρ)
    (hmass : ENNReal.ofReal (ε ^ α) ≤ μ (ball (vertexPoint ε η b) (R / 4)))
    (hb' : b ∈ cellVertices ε η (ball (vertexPoint ε η b) (R / 4)))
    (hLR : 1 + Real.log (1 / R) ≤ KL * (1 + Real.log (1 / r))) :
    srwLaw m b (TestBound68.stayIn
        (fun b' => innerVertices (cell ε η) (ball (vertexPoint ε η b') (R / 4))) A b) ≤
      ENNReal.ofReal (1 - min 1 (1 / (32 * (CE * KL) ^ 2 * (Uniform68Events.kappaAnn Cg) ^ 2 * 1 ^ 2)) /
        (1 + Real.log (1 / r)) ^ 2) :=
  hloc_band_point hap hη hp hε hR hR1 hr hr1 hεα hCE hCg hKL hCG hc0 hc0' hc0C hεc hd hsm hband hA hsparse hs hmr
    hgood hRr hdiam (Uniform68Local.greenLow_of_event hR.le hc0_24 hG hb hlo hup)
    (Uniform68Local.exitMoment_of_event hD hsub hmass hb') hLR

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.hloc_band_point_events
