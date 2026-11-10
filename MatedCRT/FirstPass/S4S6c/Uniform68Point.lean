import MatedCRT.FirstPass.S4S6c.Uniform68Events
import MatedCRT.FirstPass.S4S6c.Uniform68Local
import MatedCRT.FirstPass.S4S6c.Uniform68Band
import MatedCRT.FirstPass.S4S6c.GoodAnnulusHF68
import MatedCRT.FirstPass.S4S6c.Uniform68Inputs
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# The local test `hloc` at one sphere-band start vertex, from the band and good-annulus inputs (q2, task fp-S4S6c-envscaling-6-7-6-8)

`hloc_band_point` is `Uniform68Events.hloc_point` with its geometric and finiteness inputs discharged:

* `hap`, `hη`, `hp`: the area parametrization of `μ` by `η` (`IsValid.isAreaParametrized`), continuity and properness of `η`;
* `hDA`, `hEA`, `hx`: the sphere-band geometry of the start cell (`Uniform68Band.disk_and_thickening_subset_of_band`);
* `hμA`, `hmfin`: finiteness of `μ` on bounded sets (`IsFiniteMeasureOnCompacts μ`, the local finiteness part of
  `LQGMeasurePropertiesStmt`, passed as an instance);
* `hF`, `hint`: the good-annulus event `IsGoodAnnulusEvent μ c0 Cg R ctr` (`GoodAnnulusHF68`);
* `hfinD`, `hfinr`: finiteness of the cell vertices of bounded sets (`cellVertices_finite_of_isCompact`);
* `hsp`: the configuration sparsity `(A).ncard < s₁ r^(2β)/ε` (`Uniform68Inputs.ncard_inter_lt_of_ncard_lt`).

Still inputs (events and parameter relations, named by their source):
`hGreenLow` (Draft Lemma 2.16 at one `ω`, `Uniform68Local.greenLow_of_event`), `hdraft` (Draft Lemma 2.18,
`Uniform68Local.exitMoment_of_event`), `hdiam` (cell-size bound on cells meeting the test disk), `hs`, `hmr` (ball mass),
`hRr`, `hLR` (radius relations). The conclusion has the constant `min 1 X` (`Uniform68Local.prob_le_min_q0`).

Terminology: Armitage-Gardiner potential kernel; Duplantier-Sheffield annulus; LQG measure `μ`; Berestycki-Powell cells.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace MatedCRT

theorem hloc_band_point {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {b : ℤ} {ctr : ℂ}
    {ε R r c0 CG Cg C_E δ s1 β KL d : ℝ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hδR : δ ≤ R / 100) (hCE : 0 < C_E) (hCg : 0 < Cg) (hKL : 0 < KL) (hCG : 0 < CG)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * CG)) / 16) (hεc : ε ≤ 16 * c0)
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
    (hGreenLow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η b) (c0 * R)),
      CG⁻¹ * Real.log (if vertexPoint ε η b = vertexPoint ε η b' then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η b - vertexPoint ε η b'‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 8))) b b')
    (hdraft : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4))) b 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C_E ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ v ∈ ball (vertexPoint ε η b) (R / 4), ∫⁻ u in thickening δ (ball (vertexPoint ε η b) (R / 4)),
          ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ^ (2 : ℕ))
    (hLR : 1 + Real.log (1 / R) ≤ KL * (1 + Real.log (1 / r))) :
    srwLaw m b (TestBound68.stayIn
        (fun b' => innerVertices (cell ε η) (ball (vertexPoint ε η b') (R / 4))) A b) ≤
      ENNReal.ofReal (1 - min 1 (1 / (32 * (C_E * KL) ^ 2 * (Uniform68Events.kappaAnn Cg) ^ 2 * 1 ^ 2)) /
        (1 + Real.log (1 / r)) ^ 2) := by
  have hδ' : δ ≤ 1 / 2 := by linarith
  obtain ⟨hDA, hEA⟩ := disk_and_thickening_subset_of_band hε.le hR hsm hd hδR hband
  have hXmem : vertexPoint ε η b ∈ openAnnulus ctr R := hDA (mem_ball_self (by positivity))
  have hmfin : μ (ball (vertexPoint ε η b) (c0 * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_closedBall_ne_top (μ := μ) (vertexPoint ε η b) (c0 * R))
      (measure_mono ball_subset_closedBall)
  have hμA : μ (openAnnulus ctr R) ≠ ⊤ := measure_openAnnulus_ne_top ctr R
  have hF : ∀ w ∈ openAnnulus ctr R, ∫ u in openAnnulus ctr R, (Real.log (R / ‖u - w‖) + 1) ∂μ
      ≤ Cg * (μ (ball (vertexPoint ε η b) (c0 * R))).toReal :=
    hF_of_goodAnnulus hCg.le hXmem hgood hmfin
  have hint : ∀ v ∈ ball (vertexPoint ε η b) (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (openAnnulus ctr R) μ :=
    fun v hv => hint_of_goodAnnulus hXmem hgood hmfin hμA v (hDA hv)
  have hfinD : (cellVertices ε η (ball (vertexPoint ε η b) (c0 * R))).Finite :=
    (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (vertexPoint ε η b) (c0 * R))).subset
      (fun _ hk => Uniform68Local.cellVertices_mono_local ball_subset_closedBall hk)
  have hfinr : (cellVertices ε η (ball (vertexPoint ε η b) r)).Finite :=
    (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (vertexPoint ε η b) r)).subset
      (fun _ hk => Uniform68Local.cellVertices_mono_local ball_subset_closedBall hk)
  have hsp : ((A ∩ cellVertices ε η (ball (vertexPoint ε η b) r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε :=
    ncard_inter_lt_of_ncard_lt hA hsparse
  exact Uniform68Local.prob_le_min_q0
    (Uniform68Events.hloc_point (μ := μ) (η := η) (m := m) (A := A) (b := b) (ε := ε) (R := R) (r := r)
      (c0 := c0) (C := CG) (C_E := C_E) (Cg := Cg) (δ := δ) (s1 := s1) (β := β) (KL := KL)
      (mr := (μ (ball (vertexPoint ε η b) (c0 * R))).toReal)
      hap hε hR hR1 hr hr1 hδ' hCE hCg hKL hCG hc0 hc0' hc0C hεc rfl hmfin hmr hfinD hfinr hRr hsp hs hdiam
      hGreenLow hdraft ctr hμA hDA hEA hint hF hLR)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.hloc_band_point
