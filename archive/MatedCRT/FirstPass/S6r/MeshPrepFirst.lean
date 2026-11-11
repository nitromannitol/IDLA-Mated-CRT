import MatedCRT.FirstPass.S6r.MeshPrep
import MatedCRT.FirstPass.S6r.OneTest.FirstMoment
import MatedCRT.FirstPass.S4S6c.HcGreen68

/-!
# First-moment inputs from the prepared event (PRO step 8, Lemma 6.8 window)

`firstMoment_of_events` discharges the omega-wise hypotheses of `firstMoment_occCount_fm` (`OneTest/FirstMoment.lean`)
from the Draft-level events at a single `ω`, for a start `y` with centre `vp = vertexPoint ε (S.η ω) y`, the ball
`D₀ = B_{c₀R}(vp)` and the window `‖vp‖ + 3R ≤ ρ`, `d = R`. The events are passed as their bodies (the predicates of
`greenLowEvent68`, `cellSizeEvent68`, `ballMassLowerEvent68`, `exitTimeEvent68` of `S6f/UniformEvents.lean`), because
`S6f/UniformEvents` and `OneTest/FirstMoment` cannot be imported together: both `MatedCRT.measurable_logKernel`
(`S4S6c/GoodAnnulusHF68.lean:74`, via FirstMoment) and `MatedCRT.measurable_logKernel` (`Proofs/Measurability/GoodScale.lean:210`,
via UniformEvents) would be in the environment.
-/

open MeasureTheory Metric

namespace MatedCRT
namespace Lemma68Window

/-- **First-moment inputs discharged from the prepared event** (PRO step 8; the omega-wise hypotheses of
`firstMoment_occCount_fm`). Start `y`, centre `vp = vertexPoint ε (S.η ω) y`, window `‖vp‖ + 3R ≤ ρ`, `d = R`.
From the events at `ω` (bodies as in the docstring): `hGr` (Lemma 2.16: the greenLowEvent body at `a = y`, radius `R/8`,
first conjunct `HcGreen68.greenKernel_le_greenFn`), `hdiam` (Lemma 2.8: cellSizeEvent body, `ε^κ ≤ c₀R/100`), `hvol`
(Lemma 2.7: ballMassLowerEvent body at `δ = c₀R`), `hmass` (`4ε^α ≤ μ(D₀)`, mesh `mesh_prep_uniform`), `hfinE`
(Lemma 2.18: exitTimeEvent body, with the a.s. input `hfinL`), and `ε ≤ 16 c₀`.
Remaining named inputs (not discharged here): `Continuous (S.η ω)` and `Tendsto (S.η ω) cocompact cocompact` (a.s.
field properties), `hfinL` (a.s. finiteness, the first conjunct of `BoundedExitTimeRVStmt`), `hfinμ` (`μ(D₀) < ⊤`; the
upper half of Lemma 2.7 would give it, no Lean event for it), `hsp` (Lemma 6.8 sparsity at every centre), `hL29` (the
lower count, `SLERef/Corrected.lean` counting-measure input), and the shell window `r² ≤ R`, `10ε^ω ≤ r`, `c₀R ≤ r`. -/
theorem firstMoment_of_events {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {γ ρ : ℝ}
    (K : Constants68 γ ρ) {ζc CE ωm ωG α : ℝ}
    (hωm : 0 < ωm) (hκ : 2 * ωm < 2 / (2 + γ) ^ 2 - ζc) (hωG : 2 * ωm < ωG)
    (hα : 2 * K.βm * ωm < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (ω : Ω) (y : ℤ) (R r : ℝ) (A : Set ℤ),
      Continuous (S.η ω) → Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ) →
      (∀ a ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (ρ - ε ^ ωG)), ∀ r' : ℝ, ε ^ ωG ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere (0 : ℂ) ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
            else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b) →
      (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc)) →
      (∀ z ∈ ball (0 : ℂ) (1 - K.c0 * R), ENNReal.ofReal ((K.c0 * R) ^ K.βm) ≤ S.μ ω (ball z (K.c0 * R))) →
      (∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ a ∈ cellVertices ε (S.η ω) D,
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
          ENNReal.ofReal (CE * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D)) →
      (⨆ (D : Set ℂ) (_ : D ⊆ ball (0 : ℂ) ρ), largestExitTimeRV (S.μ ω) D) < ⊤ →
      0 < R → r ^ 2 ≤ R → 10 * ε ^ ωm ≤ r → K.c0 * R ≤ r →
      ‖vertexPoint ε (S.η ω) y‖ + 3 * R ≤ ρ →
      S.μ ω (ball (vertexPoint ε (S.η ω) y) (K.c0 * R)) ≠ ⊤ →
      (∀ w : ℂ, ((A ∩ cellVertices ε (S.η ω) (ball w r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε) →
      ε⁻¹ * (S.μ ω (ball (vertexPoint ε (S.η ω) y) (K.c0 * R))).toReal - ε ^ (-1 + α) ≤
        ((cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (K.c0 * R))).ncard : ℝ) →
      (1 / 4 : ℝ) * ε⁻¹ * (S.μ ω (ball (vertexPoint ε (S.η ω) y) (K.c0 * R))).toReal ≤
        ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε (S.η ω)
          (ball (vertexPoint ε (S.η ω) y) (R / 4))) w).toNat) w ∂(srwLaw (S.mult ε ω) y) := by
  obtain ⟨ε₀, hε₀, hmesh⟩ := mesh_prep_uniform ωm (2 / (2 + γ) ^ 2 - ζc) ωG α α K.βm 1 K.c0
    hωm K.one_le_βm hκ hωG hα hα one_pos K.hc0
  refine ⟨min ε₀ (16 * K.c0), lt_min hε₀ (by linarith [K.hc0]), fun ε hε hεle ω y R r A hηc hprop
    hGev hCev hBev hEev hfinL hR hr2 hr10 hcR hreg hfinμ hsp hL29 => ?_⟩
  have hε₀le : ε ≤ ε₀ := le_trans hεle (min_le_left _ _)
  have hεc : ε ≤ 16 * K.c0 := le_trans hεle (min_le_right _ _)
  obtain ⟨_, m2, m3, m4, m5⟩ := hmesh ε (ε ^ (2 / (2 + γ) ^ 2 - ζc)) r R hε hε₀le hr10 hr2 le_rfl
  set vp := vertexPoint ε (S.η ω) y with hvpdef
  have hεω : 0 < ε ^ ωm := Real.rpow_pos_of_pos hε _
  have hr0 : 0 < r := by linarith
  have hc0R : K.c0 * R ≤ R / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR.le
    linarith
  have hcpos : 0 ≤ K.c0 * R := mul_nonneg K.hc0.le hR.le
  have hεG : ε ^ ωG ≤ R / 8 := m2
  have hεα : ε ^ α ≤ R / 100 := le_trans m4 (min_le_left _ _)
  have hsub : ball vp (R / 4) ⊆ ball (0 : ℂ) ρ := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    rw [mem_ball, dist_zero_right]
    have hn := norm_add_le (u - vp) vp
    rw [sub_add_cancel] at hn
    linarith
  have hvpbig : vp ∈ ball (0 : ℂ) (1 - K.c0 * R) := by
    rw [mem_ball, dist_zero_right]
    linarith [K.hρ1]
  have hvcell : vp ∈ cell ε (S.η ω) y :=
    ⟨ε * (y : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  -- Lemma 2.7: the volume lower bound at the centre
  have hvol : (K.c0 * R) ^ K.βm ≤ (S.μ ω (ball vp (K.c0 * R))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinμ).1 (hBev vp hvpbig)
  -- PRO step 8: the scale condition `4 ε^α ≤ μ(D₀)`
  have hmass : 4 * ε ^ α ≤ (S.μ ω (ball vp (K.c0 * R))).toReal := by
    have e : (K.c0 * R) ^ K.βm = K.c0 ^ K.βm * R ^ K.βm := Real.mul_rpow K.hc0.le hR.le
    have hX : 0 ≤ (K.c0 * R) ^ K.βm := Real.rpow_nonneg hcpos _
    have h3 : ε ^ α ≤ 1 / 8 * (K.c0 * R) ^ K.βm := by
      rw [e]
      linarith [m3]
    linarith [hvol, hX, h3]
  -- Lemma 2.8: the cell diameters meeting the ball `B_{R/4}(vp)`
  have hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball vp (R / 4)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ K.c0 * R := by
    intro k hk
    have hk' : (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ).Nonempty :=
      hk.mono (Set.inter_subset_inter_right _ hsub)
    have := hCev k hk'
    linarith [m5, hcpos]
  -- Lemma 2.16: the Green kernel bounds on `V(D₀)`
  have hGr : ∀ b ∈ cellVertices ε (S.η ω) (ball vp (K.c0 * R)),
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball vp (R / 8))) y b
          ≤ greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball vp (R / 8))) y b ∧
        K.C⁻¹ * Real.log (if vp = vertexPoint ε (S.η ω) b then ε⁻¹
            else min ((R / 8) / ‖vp - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
          ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball vp (R / 8))) y b := by
    intro b hb
    refine ⟨MatedCRT.HcGreen68.greenKernel_le_greenFn _ _ _ _, ?_⟩
    have hyA : y ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (ρ - ε ^ ωG)) := by
      refine ⟨vp, hvcell, ?_⟩
      rw [mem_ball, dist_zero_right]
      linarith
    have hinf : R / 8 ≤ infDist vp (sphere (0 : ℂ) ρ) := by
      have hne : (sphere (0 : ℂ) ρ).Nonempty :=
        ⟨(ρ : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg K.hρ0.le]⟩
      refine (Metric.le_infDist hne).2 (fun w hw => ?_)
      rw [mem_sphere_zero_iff_norm] at hw
      rw [dist_eq_norm, norm_sub_rev]
      linarith [norm_sub_norm_le w vp]
    have hb' : b ∈ cellVertices ε (S.η ω) (ball vp (R / 8 / 3)) :=
      (show (cell ε (S.η ω) b ∩ ball vp (K.c0 * R)).Nonempty from hb).mono
        (Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith [hc0R])))
    exact hGev y hyA (R / 8) hεG hinf b hb'
  -- Lemma 2.18: finiteness of the expected exit time of `ID`
  have hfinE : expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball vp (R / 4))) y ≠ ⊤ := by
    have hyD : y ∈ cellVertices ε (S.η ω) (ball vp (R / 4)) :=
      ⟨vp, hvcell, mem_ball_self (by linarith)⟩
    have hbound := hEev (ball vp (R / 4)) hsub y hyD
    have hTsub : thickening (ε ^ α) (ball vp (R / 4)) ⊆ ball (0 : ℂ) ρ := by
      intro u hu
      obtain ⟨z, hz, hdu⟩ := Metric.mem_thickening_iff.1 hu
      rw [mem_ball, dist_eq_norm] at hz
      rw [dist_eq_norm] at hdu
      rw [mem_ball, dist_zero_right]
      have h1 := norm_add_le (u - z) z
      have h2 := norm_add_le (z - vp) vp
      rw [sub_add_cancel] at h1 h2
      linarith
    have hL : largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball vp (R / 4))) ≠ ⊤ :=
      ((le_iSup₂ (f := fun (D : Set ℂ) (_ : D ⊆ ball (0 : ℂ) ρ) => largestExitTimeRV (S.μ ω) D)
        _ hTsub).trans_lt hfinL).ne
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) hbound
  exact firstMoment_occCount_fm K (μ := S.μ ω) (η := S.η ω) (m := S.mult ε ω) (A := A)
    (ID := interiorCellVertices ε (S.η ω) (ball vp (R / 4))) (ε := ε) (R := R) (r := r) (α := α)
    (y := y) hηc hprop hε hεc hR hr0 hr2 hcR rfl hdiam hsp hvol hGr hfinE hL29 hmass

end Lemma68Window
end MatedCRT
