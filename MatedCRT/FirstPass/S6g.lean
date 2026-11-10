import MatedCRT.FirstPass.S4S6c.CellSize68
import MatedCRT.FirstPass.S4S6c.BandInduction68

/-!
# Sphere-band start cells satisfy the cell-size hypothesis `hsm` (q3, task fp-S6g-6-8-sphere-band-cell)

Item 2 of q2's uniform Lemma 6.8 (`FirstPass/S4S6c/Uniform68*.lean`, reports/q2.md): a start cell `cell ε η b` whose
closure meets the sphere `sphere c (4R/3)` (the sphere-band condition `hband` of `Uniform68Band` and `Uniform68Point`)
satisfies the pairwise bound `hsm : ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d`.

The cell-size input is the closure form `hsm0` of `CellSize68` (for cells meeting `ball 0 ρ`), which the
configuration gets from `CellSizeEstimateStmt` (Draft/Section2.lean:131, via `CellSize68.hsm0_of_cellSize`). The
sphere-band cell meets `ball 0 ρ` because the sphere lies in that ball, which holds for a band centre (`BandInduction68.band`).

Terminology: cells `H^ε_k = η([ε(k-1), εk])` of the space-filling SLE curve (Duplantier-Sheffield mating of trees;
Armstrong-Kuusi-Mourrat for the cell and vertex terminology). The band is the layer around the cluster boundary of
`BandInduction68`.
-/

open MeasureTheory Set Metric

namespace MatedCRT
namespace S6g

/-- **Sphere-band start cell satisfies `hsm`.** Let the closure of `cell ε η b` contain a point `p` of the sphere
`sphere c (4R/3)`, and let `‖c‖ + 4R/3 < ρ`, so that `p ∈ ball 0 ρ`. Then `cell ε η b` meets `ball 0 ρ` (the ball is an
open neighbourhood of `p` in the closure of the cell), and the cell-size hypothesis `hsm0` bounds the distance of any two
points of the closure of the cell by `d`. -/
theorem sphere_band_hsm {ε ρ d R : ℝ} {η : ℝ → ℂ} {c : ℂ} {b : ℤ}
    (hsm0 : ∀ v : ℤ, (cell ε η v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (cell ε η v),
      ∀ u' ∈ closure (cell ε η v), dist u u' ≤ d)
    (hband : (closure (cell ε η b) ∩ sphere c (4 * R / 3)).Nonempty)
    (hc : ‖c‖ + 4 * R / 3 < ρ) :
    ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d := by
  obtain ⟨p, hpcl, hps⟩ := hband
  have hpn : ‖p‖ < ρ := by
    have h1 : ‖p - c‖ = 4 * R / 3 := by
      rw [← dist_eq_norm]
      exact mem_sphere.1 hps
    have h2 : ‖p‖ - ‖c‖ ≤ ‖p - c‖ := norm_sub_norm_le p c
    linarith
  obtain ⟨x, hxball, hxcell⟩ :=
    mem_closure_iff.1 hpcl (ball (0 : ℂ) ρ) isOpen_ball (mem_ball_zero_iff.2 hpn)
  exact hsm0 b ⟨x, hxcell, hxball⟩

/-- **Centre bound for a band vertex.** Let `v` lie in the frontier band `BandInduction68.band P F r d` of the cluster
`F ⊆ ball 0 (ρ/2)`, and let the centre `c` satisfy `dist c (P v) ≤ g`. If `0 ≤ g`, `g + d ≤ r/1000`, `R ≤ r/1000`
and `r ≤ ρ/100`, then `‖c‖ + 4R/3 < ρ`, so the sphere `sphere c (4R/3)` lies in `ball 0 ρ`. -/
theorem centre_add_radius_lt_of_band {P : ℤ → ℂ} {F : Set ℂ} {r d g R ρ : ℝ} {v : ℤ} {c : ℂ}
    (hρ : 0 < ρ) (hF : F ⊆ ball (0 : ℂ) (ρ / 2)) (hFne : F.Nonempty)
    (hv : v ∈ BandInduction68.band P F r d) (hctr : dist c (P v) ≤ g) (hg : 0 ≤ g)
    (hgd : g + d ≤ r / 1000) (hRr : R ≤ r / 1000) (hr : r ≤ ρ / 100) :
    ‖c‖ + 4 * R / 3 < ρ := by
  have hb : |infDist (P v) F - r / 2| ≤ 3 * r / 100 + 2 * d := BandInduction68.mem_band_iff.1 hv
  have h1 : infDist (P v) F < r / 2 + 3 * r / 100 + 2 * d + ρ / 4 := by
    have := (abs_le.1 hb).2
    linarith
  have h2 : ‖P v‖ < ρ / 2 + (r / 2 + 3 * r / 100 + 2 * d + ρ / 4) :=
    BandInduction68.norm_lt_of_infDist hF hFne h1
  have h3 : ‖c‖ ≤ ‖P v‖ + g := by
    have h := norm_sub_norm_le c (P v)
    rw [← dist_eq_norm] at h
    linarith
  linarith

/-- **`hsm` for a sphere-band start cell, from the band.** The form consumed by q2's `Uniform68Point`: the sphere-band
hypothesis `hband` about the centre `c` of a band vertex `v` gives `hsm` for the start cell `b`, with the cell-size
hypothesis `hsm0` and the band geometry of `centre_add_radius_lt_of_band`. -/
theorem sphere_band_hsm_of_band {ε ρ d R g r : ℝ} {η : ℝ → ℂ} {P : ℤ → ℂ} {F : Set ℂ} {c : ℂ} {b v : ℤ}
    (hρ : 0 < ρ) (hF : F ⊆ ball (0 : ℂ) (ρ / 2)) (hFne : F.Nonempty)
    (hv : v ∈ BandInduction68.band P F r d) (hctr : dist c (P v) ≤ g) (hg : 0 ≤ g)
    (hgd : g + d ≤ r / 1000) (hRr : R ≤ r / 1000) (hr : r ≤ ρ / 100)
    (hsm0 : ∀ w : ℤ, (cell ε η w ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (cell ε η w),
      ∀ u' ∈ closure (cell ε η w), dist u u' ≤ d)
    (hband : (closure (cell ε η b) ∩ sphere c (4 * R / 3)).Nonempty) :
    ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d :=
  sphere_band_hsm hsm0 hband (centre_add_radius_lt_of_band hρ hF hFne hv hctr hg hgd hRr hr)

#print axioms MatedCRT.S6g.sphere_band_hsm
#print axioms MatedCRT.S6g.centre_add_radius_lt_of_band
#print axioms MatedCRT.S6g.sphere_band_hsm_of_band

end S6g
end MatedCRT
