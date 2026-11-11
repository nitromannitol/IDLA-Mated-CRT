import MatedCRT.FirstPass.S6r.MeshPrep
import MatedCRT.FirstPass.S6r.OneTest.SecondMoment
import MatedCRT.FirstPass.S6f.UniformEvents

open MeasureTheory Metric HarmonicBalls

namespace MatedCRT
namespace Lemma68Window

/-- **Second-moment inputs discharged from the prepared event** (PRO step 8; the omega-wise hypotheses of
`secondMoment_occCount`). For a shell test `(z, R, r, d, b)` with `d ≤ R ≤ 1`, `r² ≤ d`, `10 ε^ω ≤ r`, and
`ρ < 1`, `‖z‖ + 3R ≤ ρ` (the relevant `B_{3R}(z)` lies in the prepared region), the four events of the Draft
statements at `ω` discharge `hmom` (Lemma 2.18, `exitTimeEvent68`), `hvol` (Lemma 2.7, `ballMassLowerEvent68`), the
cell-size input `hcell`, `hh` (Lemma 2.8, `cellSizeEvent68`), the `hεα`, `hεmass`, `hx1`, `hρ` side conditions, and the
mesh inequalities of `mesh_prep_uniform`. Remaining named inputs: `IsGoodAnnulusEvent` (`hgood`), the a.s. properties
`hpos`, `hfin`, `hatom`, `hfinD` of the field, and the covering `hN`. -/
theorem secondMoment_of_events {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ρ ζc αex CE ωm ωG αcnt βm c0 C_good : ℝ} (N_cov : ℕ)
    (hωm : 0 < ωm) (hβ : 1 ≤ βm) (hκ : 2 * ωm < 2 / (2 + γ) ^ 2 - ζc) (hωG : 2 * ωm < ωG)
    (hcnt : 2 * βm * ωm < αcnt) (hex : 2 * βm * ωm < αex) (hc0 : 0 < c0) (hc0' : c0 < 1 / 5)
    (hCg : 0 ≤ C_good) (hρ1 : ρ < 1)
    (hN : ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
      (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (ω : Ω) (z x : ℂ) (R r d : ℝ) (b : ℤ) (A : Set ℤ),
      Continuous (S.η ω) → ω ∈ cellSizeEvent68 S γ ζc ρ ε → ω ∈ exitTimeEvent68 S αex ρ CE ε →
      ω ∈ ballMassLowerEvent68 S βm (R / 4) → 0 < R → R ≤ 1 → d ≤ R → r ^ 2 ≤ d → 10 * ε ^ ωm ≤ r →
      ‖z‖ + 3 * R ≤ ρ → b ∈ cellVertices ε (S.η ω) (sphere z (4 * R / 3)) → x = S.η ω (ε * b) →
      IsGoodAnnulusEvent (S.μ ω) c0 C_good R z → 0 < ⨅ w ∈ annulus z R (2 * R), S.μ ω (ball w (c0 * R)) →
      S.μ ω (ball z (3 * R)) ≠ ⊤ → (∀ v ∈ annulus z R (2 * R), S.μ ω {v} = 0) →
      S.μ ω (ball x (3 * c0 * R)) ≠ ⊤ →
      ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε (S.η ω) (ball x (R / 4))) w).toNat) w ^ 2
          ∂(srwLaw (S.mult ε ω) b)
        ≤ 32 * CE ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * ε⁻¹ ^ 2 * (1 + Real.log (1 / R)) ^ 2
          * (S.μ ω (ball x (3 * c0 * R))).toReal ^ 2 := by
  obtain ⟨ε₀, hε₀, hmesh⟩ := mesh_prep_uniform ωm (2 / (2 + γ) ^ 2 - ζc) ωG αcnt αex βm 1 c0
    hωm hβ hκ hωG hcnt hex one_pos hc0
  refine ⟨ε₀, hε₀, fun ε hε hεle ω z x R r d b A hηc hcell hexit hvol hR hR1 hdR hr2 hr hreg hb hx
    hgood hpos hfin hatom hfinD => ?_⟩
  obtain ⟨_, _, _, m4, m5⟩ := hmesh ε (ε ^ (2 / (2 + γ) ^ 2 - ζc)) r d hε hεle hr hr2 le_rfl
  have hd0 : 0 ≤ d := le_trans (sq_nonneg r) hr2
  have hcellω := hcell
  simp only [cellSizeEvent68, Set.mem_ofPred_eq] at hcellω
  have hexit' := hexit
  simp only [exitTimeEvent68, Set.mem_ofPred_eq] at hexit'
  have hvol' := hvol
  simp only [ballMassLowerEvent68, Set.mem_ofPred_eq] at hvol'
  -- the boundary point p of the cell of b (`b ∈ V^ε(∂B_{4R/3}(z))`)
  obtain ⟨p, hp1, hp2⟩ := id hb
  have hpz : ‖p - z‖ = 4 * R / 3 := by
    rw [← dist_eq_norm]; exact mem_sphere.1 hp2
  have hpball : p ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' p z
    linarith
  have hbd : Bornology.IsBounded (cell ε (S.η ω) b) :=
    (isCompact_Icc.image hηc).isBounded
  have hdiam : diam (cell ε (S.η ω) b) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) :=
    (hcellω b ⟨p, hp1, hpball⟩).2
  have hxcell : x ∈ cell ε (S.η ω) b := by
    refine ⟨ε * b, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, hx.symm⟩
  have hkR : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R / 100 := by
    have hc0d : c0 * d ≤ R := by nlinarith
    linarith [m5]
  have hdistpx : dist x p ≤ R / 100 := by
    have := Metric.dist_le_diam_of_mem hbd hxcell hp1
    linarith [hdiam, hkR]
  have hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100 := by
    have h3 := abs_norm_sub_norm_le (x - z) (p - z)
    rw [show (x - z) - (p - z) = x - p by ring, ← dist_eq_norm x p, hpz] at h3
    have h5 := abs_le.1 (h3.trans hdistpx)
    constructor <;> linarith [h5.1, h5.2]
  have hxnorm : ‖x‖ < ρ - R / 4 := by
    have hn := norm_add_le (x - z) z
    rw [sub_add_cancel] at hn
    linarith [hxz.2, hreg]
  have hx1 : ‖x‖ < 1 - R / 4 := by linarith
  have hxball : x ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right]; linarith
  have hρ' : ball x (R / 4) ⊆ ball (0 : ℂ) ρ := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    rw [mem_ball, dist_zero_right]
    have hn := norm_add_le (u - x) x
    rw [sub_add_cancel] at hn
    linarith
  have hεα : ε ^ αex ≤ R / 100 := by
    have := le_trans m4 (min_le_left _ _)
    linarith
  have hpow : d ^ βm ≤ R ^ βm := Real.rpow_le_rpow hd0 hdR (by linarith)
  have h4 : (0 : ℝ) ≤ 4 ^ (-βm) := Real.rpow_nonneg (by norm_num) _
  have hR4 : (R / 4) ^ βm = 4 ^ (-βm) * R ^ βm := by
    rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_inv_mul]
  have hX : 0 ≤ 4 ^ (-βm) * d ^ βm := mul_nonneg h4 (Real.rpow_nonneg hd0 _)
  have hεmass : ε ^ αex ≤ (R / 4) ^ βm := by
    have m4b := le_trans m4 (min_le_right _ _)
    rw [hR4]
    nlinarith [mul_le_mul_of_nonneg_left hpow h4]
  have hcellb : ∀ q ∈ cell ε (S.η ω) b, ∀ q' ∈ cell ε (S.η ω) b, dist q q' ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) :=
    fun q hq q' hq' => (Metric.dist_le_diam_of_mem hbd hq hq').trans hdiam
  have hmom := hexit'.1
  have hvol'' : ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ S.μ ω (ball y (R / 4)) :=
    hvol'
  exact secondMoment_occCount (m := S.mult ε ω) (μ := S.μ ω) (η := S.η ω)
    (ID := interiorCellVertices ε (S.η ω) (ball x (R / 4))) (A := A) (ε := ε) (R := R) (α := αex)
    (ρ := ρ) (C_exit := CE) (c₀ := c0) (C_good := C_good) (βm := βm)
    (h := ε ^ (2 / (2 + γ) ^ 2 - ζc)) N_cov (z := z) (x := x) (b := b) rfl hε hR hR1 hc0 hc0'
    hCg hεα hεmass hb hx hcellb hkR hx1 hvol'' hρ' hmom hgood hN hpos hfin hatom hfinD
end Lemma68Window
end MatedCRT
