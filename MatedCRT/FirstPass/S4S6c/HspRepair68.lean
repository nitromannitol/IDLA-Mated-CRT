import MatedCRT.FirstPass.S6r.LocalBudget
import MatedCRT.FirstPass.S6r.OneTest.WalkStateFirst
import MatedCRT.FirstPass.S4S6c.HoneInputsDirect

/-!
# The mass-relative sparsity of the walk-centred hone (fp-S4S6c-hsp-repair; chat 226 l.117-186, patch item 1)

The binder `hsp` of `hone_exitQ_walk_of_env_direct` (S4S6c/HoneInputsDirect.lean:83) asks for
`#(A ∩ V^ε(B_{c0 R_k}(w))) < s1 (c0 R_k)^{2 βm} / ε`. Chat 226 shows that this is false for the intended scales: the
Lemma 6.8 sparsity at the theorem radius `r` gives `s1 r^{2 βm} / ε` with `r² ≤ R_k`, so only `R_k^{βm}` is available.

This file gives the repaired binder in mass-relative form, `ε #(A ∩ V^ε(B_{c0 R_k}(w))) ≤ (1/16) μ(B_{c0 R_k}(w))`:
* `hsp_massRel_of_lemma68` derives it from the Lemma 6.8 sparsity at radius `r`, `c0 R ≤ r`, `r² ≤ R`, `16 s1 ≤ c0^βm`
  and a volume lower bound `(c0 R)^βm ≤ μ(B_{c0 R}(w))` (named binder; Lemma 2.7, `VolumeGrowthStmt`).
* `firstMoment_walkState_massRel`, `hone_exitQ_walk_massRel`, `hone_exitQ_walk_of_env_massRel` and
  `hone_exitQ_walk_of_env_direct_massRel` are copies of `firstMoment_walkState` (WalkStateFirst.lean:18),
  `hone_exitQ_walk` (HoneWalk.lean:37), `hone_exitQ_walk_of_env` (HoneInputs.lean:39) and
  `hone_exitQ_walk_of_env_direct` (HoneInputsDirect.lean:83), with only `hsp` replaced; all other binders are unchanged.
* The first-moment proof uses the sparsity at the centre only: `firstMoment_occCount_fm_loc` is
  `firstMoment_occCount_fm` (FirstMoment.lean:120) with the radius-`r` sparsity and the ball mass replaced by the
  centre count `hloc` (the conclusion of `localCount_of_ball`, LocalBudget.lean:33, at `x = η(εy)`, radius `c0 R`).

The original chain is not changed. Its `hsp` is the exponent-`2 βm` form that chat 226 shows to be false.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
open Lemma68WalkBridge (coordFiltration)
open Lemma68ShellParam (measurable_coord_toNat_stop)

namespace Lemma68Window


/-- **The mass-relative sparsity from the Lemma 6.8 sparsity (chat 226 l.117-170).** Let `r` be the radius of the
Lemma 6.8 sparsity `#(A ∩ V^ε(B_r(z))) < s1 r^{2β⁻} ε⁻¹` at every centre `z`. If the local radius satisfies
`c0 R ≤ r` (so `V^ε(B_{c0R}(w)) ⊆ V^ε(B_r(w))`, no covering), `r² ≤ R` (`R_k ≥ r²`), `16 s1 ≤ c0^{β⁻}`, and the ball
mass has the volume lower bound `(c0 R)^{β⁻} ≤ μ(B_{c0R}(w))` (`hvol`, a named input), then
`ε #(A ∩ V^ε(B_{c0R}(w))) ≤ (1/16) μ(B_{c0R}(w))`. The exponent of `R` is `β⁻`, not `2β⁻`, since
`r^{2β⁻} ≤ R^{β⁻}`. -/
theorem hsp_massRel_of_lemma68 {μ : Measure ℂ} {η : ℝ → ℂ} {A : Set ℤ} {ε s1 β c0 r R : ℝ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hs0 : 0 ≤ s1) (hβ0 : 0 ≤ β) (hc0 : 0 < c0) (hR : 0 < R)
    (hs1 : 16 * s1 ≤ c0 ^ β) (hcR : c0 * R ≤ r) (hr2 : r ^ 2 ≤ R)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : ∀ w : ℂ, (c0 * R) ^ β ≤ (μ (ball w (c0 * R))).toReal) :
    ∀ w : ℂ, ε * ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
      ≤ (1 / 16 : ℝ) * (μ (ball w (c0 * R))).toReal := by
  intro w
  have hr : 0 < r := lt_of_lt_of_le (mul_pos hc0 hR) hcR
  have hfin : (cellVertices ε η (ball w r)).Finite :=
    S6j.perState_cellVertices_ball_finite hη hprop hε w r
  have hsub : cellVertices ε η (ball w (c0 * R)) ⊆ cellVertices ε η (ball w r) :=
    cellVertices_mono_win (Metric.ball_subset_ball hcR)
  have hncard : ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
      ≤ ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right _ hsub)
      (hfin.subset inter_subset_right)
  have hmono : ε * ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
      ≤ ε * ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hncard hε.le
  -- the radius-`r` sparsity, times `ε`: `ε #(A ∩ V(B_r)) < s1 r^{2β}`
  have h1 : ε * ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) ≤ s1 * r ^ (2 * β) :=
    calc ε * ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ)
        = ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) * ε := mul_comm _ _
      _ ≤ s1 * r ^ (2 * β) := ((lt_div_iff₀ hε).mp (hL68 w)).le
  -- `r^{2β} ≤ R^β` from `r² ≤ R`
  have hpow : r ^ (2 * β) ≤ R ^ β := by
    have e : r ^ (2 * β) = (r ^ 2) ^ β := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
      congr 1
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hr2 hβ0
  have hRβ : 0 ≤ R ^ β := Real.rpow_nonneg hR.le β
  have hmain : s1 * r ^ (2 * β) ≤ s1 * R ^ β := mul_le_mul_of_nonneg_left hpow hs0
  have h44 : 16 * s1 * R ^ β ≤ c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hs1 hRβ
  have hv := hvol w
  rw [Real.mul_rpow hc0.le hR.le] at hv
  linarith


/-- **The first moment of the one-test count, from the centre count (chat 226 l.176-182 route).** This is the proof of
`firstMoment_occCount_fm` (FirstMoment.lean:120) with the radius-`r` sparsity `hsp` and the ball mass `hvol` replaced by
the centre count `hloc` at `x = η(εy)` and radius `c0 R` (the conclusion of `localCount_of_ball`). The radius of the
test is `c0 R`; no other use of `r` occurs in the proof. -/
theorem firstMoment_occCount_fm_loc {γ ρ : ℝ} (K : Constants68 γ ρ) {μ : Measure ℂ} {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A ID : Set ℤ} {ε R α : ℝ} {y : ℤ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hεc : ε ≤ 16 * K.c0) (hR : 0 < R)
    (hID : ID = interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4)))
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ K.c0 * R)
    (hloc : ((A ∩ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ)
      ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal / (4 * ε))
    (hGr : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        K.C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hfinE : expectedExitTime m ID y ≠ ⊤)
    (hL29 : ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal - ε ^ (-1 + α)
      ≤ ((cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ))
    (hsc : 4 * ε ^ α ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal) :
    (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal
      ≤ ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ∂(srwLaw m y) := by
  have hfinD : (cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).Finite :=
    S6j.perState_cellVertices_ball_finite hη hprop hε _ _
  set V := cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)) with hVdef
  set m0 := (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal with hm0
  obtain ⟨S, hS⟩ : ∃ S : Set ℤ, S = V \ A := ⟨_, rfl⟩
  have hSV : S ⊆ V := by rw [hS]; exact Set.sdiff_subset
  have hSA : ∀ b ∈ S, b ∉ A := by
    intro b hb
    rw [hS] at hb
    exact hb.2
  have hSfin : S.Finite := hfinD.subset hSV
  -- (B10): `|S| ≥ ε⁻¹ m₀ / 2`
  have hcardSum : ((V \ A).ncard : ℝ) + ((V ∩ A).ncard : ℝ) = V.ncard := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard V A hfinD
    have h2 : (V \ A).ncard + (V ∩ A).ncard = V.ncard := by rw [add_comm]; exact h
    exact_mod_cast h2
  have hrpow : ε ^ (-1 + α) = ε⁻¹ * ε ^ α := by
    rw [Real.rpow_add hε, Real.rpow_neg_one]
  have hloc' : ((V ∩ A).ncard : ℝ) ≤ m0 / (4 * ε) := by
    rw [Set.inter_comm]
    exact hloc
  have hS_lower : ε⁻¹ * m0 / 2 ≤ (S.ncard : ℝ) := by
    have e1 : m0 / (4 * ε) = ε⁻¹ * (m0 / 4) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    have e2 : ε⁻¹ * ε ^ α ≤ ε⁻¹ * (m0 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hε.le)
    rw [hrpow] at hL29
    rw [hS]
    linarith [e1, e2, hL29, hloc', hcardSum]
  -- (B13): the Green lower bound `1/2 ≤ G_{I(D)}(y, b)` for `b ∈ S`
  have hG : ∀ b ∈ S, ENNReal.ofReal (1 / 2) ≤ ∫⁻ w, visitsBeforeExit ID b w ∂srwLaw m y := by
    intro b hb
    have hbV : b ∈ V := hSV hb
    rw [GreenTest68.lintegral_visits_eq_tsum, hID]
    exact GreenTest68.hG_of_green hη hε hR K.hC K.hc0 K.c0_lt_eighth K.hc0C hεc hdiam hbV (hGr b hbV)
  -- (B14): Tonelli, `∫⁻ visitCount ID S = ∑_{b∈S} ∫⁻ visits_b`
  have hsum : ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
      = ∑' b : S, ∫⁻ w, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y := by
    calc ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
        = ∫⁻ w, ∑' b : S, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y :=
          lintegral_congr fun w => (ConstantOrderDiv.tsum_visitsBeforeExit ID S w).symm
      _ = ∑' b : S, ∫⁻ w, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y :=
          lintegral_tsum fun b => (ConstantOrderDiv.measurable_visitsBeforeExit ID b).aemeasurable
  have hlow : ∑' _ : S, ENNReal.ofReal (1 / 2)
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y := by
    rw [hsum]
    exact ENNReal.tsum_le_tsum fun b => hG b.1 b.2
  have hcard : ∑' _ : S, ENNReal.ofReal (1 / 2) = (S.ncard : ℝ≥0∞) * ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.tsum_set_const, ← hSfin.cast_ncard_eq]
    simp
  -- the upper side is finite, and `V_occ ≤ σ` and the visit count are dominated by `σ`
  have hVA_ne : ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y ≠ ⊤ :=
    ne_top_of_le_ne_top hfinE (lintegral_mono fun w => ConstantOrderDiv.visitCount_le ID Aᶜ w)
  have hle : ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y :=
    lintegral_mono fun w => visitCount_mono_set_fm (fun b hb => hSA b hb) w
  have hfinal : (S.ncard : ℝ≥0∞) * ENNReal.ofReal (1 / 2)
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y := by
    rw [← hcard]
    exact hlow.trans hle
  have hreal := ENNReal.toReal_mono hVA_ne hfinal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by norm_num)] at hreal
  -- identify the Bochner integral with the lintegral of the visit count (a.e., on `{σ < ∞}`)
  have hae : ∀ᵐ w ∂srwLaw m y,
      ENNReal.ofReal (occCount A (fun w => (vExitTime ID w).toNat) w)
        = ConstantOrderDiv.visitCount ID Aᶜ w := by
    filter_upwards [ae_exitTime_lt_top_fm hfinE] with w hw
    exact ofReal_occCount_eq_visitCount_fm hw
  have hmeas : AEStronglyMeasurable (fun w => occCount A (fun w => (vExitTime ID w).toNat) w)
      (srwLaw m y) := by
    refine ((ENNReal.measurable_toReal.comp
      (ConstantOrderDiv.measurable_visitCount ID Aᶜ)).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with w hw
    simp only [Function.comp_apply]
    rw [← hw, ENNReal.toReal_ofReal (occCount_nonneg_fm _ _ w)]
  have hint : ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ∂srwLaw m y
      = (∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => occCount_nonneg_fm _ _ w)
      hmeas]
    exact congrArg ENNReal.toReal (lintegral_congr_ae hae)
  rw [hint]
  linarith [hS_lower, hreal]


/-- **The first moment at a walk state, mass-relative sparsity (chat 226 l.176-182).** Copy of `firstMoment_walkState`
(WalkStateFirst.lean:18) whose `hsp` is `ε #(A ∩ V^ε(B_{c0R}(w))) ≤ (1/16) μ(B_{c0R}(w))` for every centre `w`. Only
the centre `w = η(εy)` is used. The binders `_hR1` and `_hvol` (the window bound `R ≤ 1` and the centre volume
bound of `firstMoment_walkState`) are kept so that the chain calls keep their argument order; the mass-relative `hsp`
replaces them in the proof. -/
theorem firstMoment_walkState_massRel {γ ρc : ℝ} (K : Constants68 γ ρc) {μ : Measure ℂ} {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε R α : ℝ} {y : ℤ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hεc : ε ≤ 16 * K.c0) (hR : 0 < R) (_hR1 : R ≤ 1)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ K.c0 * R)
    (hsp : ∀ w : ℂ, ε * ((A ∩ cellVertices ε η (ball w (K.c0 * R))).ncard : ℝ)
      ≤ (1 / 16 : ℝ) * (μ (ball w (K.c0 * R))).toReal)
    (_hvol : (K.c0 * R) ^ K.βm ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal)
    (hGr : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        K.C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hfinE : expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) y ≠ ⊤)
    (hL29 : ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal - ε ^ (-1 + α)
      ≤ ((cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ))
    (hsc : 4 * ε ^ α ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal) :
    (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal
      ≤ ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) w).toNat) w ∂(srwLaw m y) := by
  have hc0 : 0 < K.c0 := K.hc0
  have hc1 : K.c0 ≤ 1 / 24 := K.hc0'
  have hcR : 0 < K.c0 * R := mul_pos hc0 hR
  have hx : K.c0 * R ≤ R := by nlinarith
  have hloc : ((A ∩ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ)
      ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal / (4 * ε) := by
    have h := hsp (vertexPoint ε η y)
    have hμ0 : 0 ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal := ENNReal.toReal_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact firstMoment_occCount_fm_loc K hη hprop hε hεc hR rfl hdiam hloc hGr hfinE hL29 hsc

-- Copy of `hone_exitQ_walk` (HoneWalk.lean:37) with hsp replaced by its mass-relative form
-- (fp-S4S6c-hsp-repair; chat 226 l.176-182). Other binders unchanged.
/-- **The hone of `exitQ_le_pow` at the walk-centred test end** (family over `k ≤ n`). The parameter is
`ρ_k = walkParam (R k) (T k)`, the test end is `L_k = testEndExit ε η ρ_k (T k)`, the count is `σ_D` for
`D = B_{R_k/4}(η(ε X_{T_k}))`. `hstep1` and `hstep2` are derived (`firstMoment_walkState_massRel`,
`secondMoment_walkState`); their omega-wise side conditions are named over the prefix set. `hmom1`, `hmom2`
(finite exit-time moments), `hRr` (parameter range), and the mass comparison `hdbl` stay named. -/
theorem hone_exitQ_walk_massRel {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    -- first-moment side conditions at the walk state `y = ω (T k ω).toNat`
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ε * ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball w (K.c0 * R k ω))).toReal)
    (hvol : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (hGr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
          (ω (T k ω).toNat) b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b ∧
        K.C⁻¹ * Real.log (if vertexPoint ε η (ω (T k ω).toNat) = vertexPoint ε η b then ε⁻¹
            else min ((R k ω / 8) / ‖vertexPoint ε η (ω (T k ω).toNat) - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hL29 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ))
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    -- second-moment side conditions at the walk state `b = ω (T k ω).toNat`, centre `vertexPoint ε η b`,
    -- shell centre `Z k ω`, mesh `H k ω`, outer radius `Rb k ω`
    {Z : ℕ → (ℕ → ℤ) → ℂ} {H Rb : ℕ → (ℕ → ℤ) → ℝ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ H k ω)
    (hh : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, H k ω ≤ R k ω / 100)
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hvol2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (hρS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4) ⊆ ball 0 (Rb k ω))
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Rb k ω) → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hfin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      μ (ball (Z k ω) (3 * R k ω)) ≠ ⊤)
    (hatom : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ v ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ {v} = 0)
    (hfinD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω)) ≠ ⊤)
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  have hc : (0 : ℝ) < 1 / 4 := by norm_num
  have hc0' : K.c0 < 1 / 5 := by linarith [K.hc0']
  have hstep1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal
        ≤ ∫ w, occCount A (ballExitSigma ε η (walkParam ε η (R k) (T k) ω)) w
            ∂(srwLaw m (ω (T k ω).toNat)) := by
    intro k ω hω
    have hR0 : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    exact firstMoment_walkState_massRel K hη hprop hε hεc hR0 (hRr k ω hω).2 (hdiam k ω hω) (hsp k ω hω)
      (hvol k ω hω) (hGr k ω hω) (hfinE k ω hω) (hL29 k ω hω) (hsc k ω hω)
  have hstep2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∫ w, occCount A (ballExitSigma ε η (walkParam ε η (R k) (T k) ω)) w ^ 2
          ∂(srwLaw m (ω (T k ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2
          * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal ^ 2 := by
    intro k ω hω
    have hR0 : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hS := secondMoment_walkState (μ := μ) (η := η) (m := m) (A := A) (ε := ε) (R := R k ω)
      (α := α) (ρ := Rb k ω) (C_exit := C_exit) (c₀ := K.c0) (C_good := C_good) (βm := K.βm)
      (h := H k ω) (N_cov := N_cov) (z := Z k ω) (b := ω (T k ω).toNat) (Dbl := Dbl)
      hε hR0 (hRr k ω hω).2 K.hc0 hc0' hCg (hεα k ω hω) (hεmass k ω hω) (hb k ω hω) (hcell k ω hω)
      (hh k ω hω) (hx1 k ω hω) (hvol2 k ω hω) (hρS k ω hω) (hmomS k ω hω) (hgood k ω hω) (hN k ω hω)
      (hpos k ω hω) (hfin k ω hω) (hatom k ω hω) (hfinD k ω hω) (hdbl k ω hω)
    have hX : 0 ≤ ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2
        * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCw hX
    exact hS.trans (le_trans (le_of_eq (by ring)) (h3.trans (le_of_eq (by ring))))
  have hm : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := fun k ω hω =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (mul_pos K.hc0 (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1)) _)
      (hvol k ω hω)
  exact hone_exitQ_concrete ε η hη hε m a A hA n hc hC hr hr1 hq0c hq hT
    (ρ := fun k => walkParam ε η (R k) (T k)) (fun k => measurable_walkParam (hT k) (hR k) ε η)
    hmom1 hmom2 (mm := fun k ω => (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (R := R) hm hRr hstep1 hstep2

-- Copy of `hone_exitQ_walk_of_env` (HoneInputs.lean:39) with hsp replaced by its mass-relative form
-- (fp-S4S6c-hsp-repair; chat 226 l.176-182). Other binders unchanged.
/-- **The hone of `exitQ_le_pow` at the walk-centred test end, with the discharged environment inputs removed.**
Same conclusion as `hone_exitQ_walk_massRel`. The finiteness, null-singleton, `ρS`, `hvol`, `hvol2` and `hGrLow` inputs are derived
from the good-event hypotheses `hVol` (volume lower bound at all scales in `[rmin, 1/4]`), `hGreen` (lower Green bound)
and `hWalk` (walk state in its domain). The moment, parameter, sparsity and configuration inputs stay named. -/
theorem hone_exitQ_walk_of_env_massRel {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ε * ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball w (K.c0 * R k ω))).toReal)
    -- scale range of the good event: every walk test radius satisfies `rmin ≤ c₀ R` (configuration input, q2)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    -- good event of the volume lower bound (lower half of `VolumeGrowthStmt`, all scales in `[rmin, 1/4]`)
    (hVol : ∀ δ : ℝ, rmin ≤ δ → δ ≤ 1 / 4 → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ K.βm) ≤ μ (ball z δ))
    -- good event of the lower Green bound (second conjunct of `GreenKernelLowerBoundStmt`, exponent `K.ω`,
    -- constant `K.C`, radius `ρc`)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    -- the walk state lies in the domain of the good Green bound, with margin `R/8` to `∂B_ρ` (configuration input, q2)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hL29 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ))
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ} {H : ℕ → (ℕ → ℤ) → ℝ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ H k ω)
    (hh : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, H k ω ≤ R k ω / 100)
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  -- `ρS` with `Rb := 1`: a ball of radius `R/4` about a point of norm `< 1 - R/4` lies in the unit ball.
  have hρS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4) ⊆ ball 0 1 := by
    intro k ω hω u hu
    have hx := hx1 k ω hω
    have hd : ‖u - vertexPoint ε η (ω (T k ω).toNat)‖ < R k ω / 4 := by
      simpa [dist_eq_norm] using hu
    have htri := norm_add_le (vertexPoint ε η (ω (T k ω).toNat)) (u - vertexPoint ε η (ω (T k ω).toNat))
    have hsum : vertexPoint ε η (ω (T k ω).toNat) + (u - vertexPoint ε η (ω (T k ω).toNat)) = u := by ring
    rw [hsum] at htri
    rw [mem_ball_zero_iff]
    linarith
  -- scale bookkeeping: `c₀ ≤ 1/24` gives `c₀R ≤ R/24 ≤ R/4` and `c₀R ≤ R/24`, and `R > 0` from `r² ≤ R`
  have hRpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, 0 < R k ω :=
    fun k ω hω => lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
  have hcR : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      K.c0 * R k ω ≤ R k ω / 24 := fun k ω hω => by
    have h := mul_le_mul_of_nonneg_right K.hc0' (hRpos k ω hω).le
    linarith
  -- `hvol`: the good volume bound at `δ = c₀R`, centre `v` with `‖v‖ < 1 - R/4 ≤ 1 - c₀R`
  have hvol : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
    intro k ω hω
    have hR1 := (hRr k ω hω).2
    have hc := hcR k ω hω
    have hR0 := hRpos k ω hω
    have hz : vertexPoint ε η (ω (T k ω).toNat) ∈ ball (0 : ℂ) (1 - K.c0 * R k ω) := by
      rw [mem_ball_zero_iff]
      linarith [hx1 k ω hω]
    have hlow := hVol (K.c0 * R k ω) (hRmin k ω hω) (by linarith) _ hz
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top (μ := μ)).ne).mp hlow
  -- `hvol2`: the good volume bound at `δ = R/4`, centres `y ∈ B_{1-R/4}`
  have hvol2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)) := by
    intro k ω hω y hy
    exact hVol (R k ω / 4) (by linarith [hRmin k ω hω, hcR k ω hω, hRpos k ω hω])
      (by linarith [(hRr k ω hω).2]) y hy
  -- `hGrLow`: the good Green bound at the walk state with `r = R/8`; `B(v, c₀R) ⊆ B(v, R/8/3)` since `c₀ ≤ 1/24`
  have hGrLow : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)),
      K.C⁻¹ * Real.log (if vertexPoint ε η (ω (T k ω).toNat) = vertexPoint ε η b then ε⁻¹
            else min ((R k ω / 8) / ‖vertexPoint ε η (ω (T k ω).toNat) - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b := by
    intro k ω hω b hb
    obtain ⟨hA1, hA2, hA3⟩ := hWalk k ω hω
    have hsub : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆
        ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8 / 3) :=
      ball_subset_ball (by linarith [hcR k ω hω])
    exact hGreen (ω (T k ω).toNat) hA1 (R k ω / 8) hA2 hA3 b
      (Set.Nonempty.mono (Set.inter_subset_inter_right _ hsub) hb)
  exact hone_exitQ_walk_massRel K ε η hη hprop hε hεc m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hdiam hsp
    hvol (fun k ω hω b hb => ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hGrLow k ω hω b hb⟩)
    hfinE hL29 hsc (Z := Z) (H := H) (Rb := fun _ _ => 1) hεα hεmass hb hcell hh hx1 hvol2 hρS hmomS hgood hN hpos
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) (fun k ω _ v _ => hμNull v)
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) hdbl

-- Copy of `hone_exitQ_walk_of_env_direct` (HoneInputsDirect.lean:83) with hsp replaced by its mass-relative form
-- (fp-S4S6c-hsp-repair; chat 226 l.176-182). Other binders unchanged.
/-- **The hone of `exitQ_le_pow` at the walk-centred test end, direct inputs discharged from good events.**
Same conclusion as `hone_exitQ_walk_of_env_massRel`. Removed binders: `hL29` (derived from `hCountGood`), `hcell` and `hh`
(derived from `hCellGood` and `hεcell`, with `H := ε^θ`). New good-event binders: `hCountGood`, `hCellGood`, `hεcell`,
with the exponent parameter `ζc`. Kept binders: `hfinE` and `hdiam` (the test balls `B(v, R/4)` leave the good-event
domain `B_{ρc}`; see the report), and all configuration, moment and sparsity binders of `hone_exitQ_walk_of_env_massRel`. -/
theorem hone_exitQ_walk_of_env_direct_massRel {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ε * ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball w (K.c0 * R k ω))).toReal)
    -- scale range of the good event: every walk test radius satisfies `rmin ≤ c₀ R` (configuration input, q2)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    -- good event of the volume lower bound (lower half of `VolumeGrowthStmt`, all scales in `[rmin, 1/4]`)
    (hVol : ∀ δ : ℝ, rmin ≤ δ → δ ≤ 1 / 4 → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ K.βm) ≤ μ (ball z δ))
    -- good event of the lower Green bound (second conjunct of `GreenKernelLowerBoundStmt`)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    -- the walk state lies in the domain of the good Green bound, with margin `R/8` to `∂B_ρ` (configuration input, q2)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    -- NEW good-event input: lower half of Lemma 2.9 (`CountingMeasureConvergenceStmt`) at `f ≡ 1`, for `D ⊆ B_{ρc}`
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    -- NEW good-event input: upper half of Lemma 2.8 (`CellSizeEstimateStmt`) at radius `ρc`, exponent `2/(2+γ)² − ζc`
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρc).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    -- NEW configuration input: the cell-size exponent is below the scale range `rmin` (ε small, as in Lemma 2.8's `ε → 0`)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  classical
  -- the single exponent `θ = 2/(2+γ)² − ζc` of the cell-size good event
  -- (1) every vertex cell of the walk has diameter `≤ ε^θ`, from `hCellGood` (its cell meets `B_{ρc}` by `hWalk`)
  have hcellD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) := by
    intro k ω hω p hp q hq
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have hxρ : x ∈ ball (0 : ℂ) ρc := by
      have h1 := mem_ball_zero_iff.mp hxb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      exact mem_ball_zero_iff.mpr (by linarith)
    exact (dist_le_diam_cell_direct hη _ hp hq).trans (hCellGood _ ⟨x, hxc, hxρ⟩)
  -- (2) the diameter bound is below `R/100`, from `hεcell` and `rmin ≤ c₀R ≤ R`
  have hsmallAll : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 100 := by
    intro k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hrmin : rmin ≤ R k ω :=
      le_trans (hRmin k ω hω) (mul_le_of_le_one_left hRpos.le (by linarith [K.hc0']))
    linarith
  -- (3) the lower counting bound (`hL29`) at the walk test ball `B(v, c₀R)`, from `hCountGood`
  have hL29' : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
    intro k ω hω
    obtain ⟨⟨p, hpc, hpb⟩, -, hW3⟩ := hWalk k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hpnorm : ‖p‖ < ρc := by
      have h1 := mem_ball_zero_iff.mp hpb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      linarith
    have hvp : dist (vertexPoint ε η (ω (T k ω).toNat)) p < R k ω / 8 := by
      have h1 := hcellD k ω hω _ (vertexPoint_mem_cell_direct hε _) p hpc
      have h2 := hsmallAll k ω hω
      linarith
    have hfar : ∀ x ∈ sphere (0 : ℂ) ρc, R k ω / 8 ≤ dist (vertexPoint ε η (ω (T k ω).toNat)) x :=
      fun x hx => le_trans hW3 (infDist_le_dist_of_mem hx)
    have hD : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆ ball (0 : ℂ) ρc :=
      (ball_subset_ball (by nlinarith [K.hc0'])).trans
        (ball_subset_ball0_of_sphere_far hfar hpnorm hvp)
    obtain ⟨w, hw⟩ := exists_cellPoint_choice_direct (ε := ε) (η := η)
      (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))
    have hfinD : (cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).Finite :=
      (cellVertices_finite_of_isCompact hη hprop hε (isCompact_closedBall (0 : ℂ) ρc)).subset
        (fun k' hk' => Set.Nonempty.mono (inter_subset_inter_right _ (hD.trans ball_subset_closedBall)) hk')
    have hc := hCountGood _ hD w hw
    have hint : ∫ _ in ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω), (1 : ℝ) ∂μ
        = (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have hsum : ∑' _ : cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)), (1 : ℝ)
        = ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
      have := hfinD.fintype
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [hint, hsum] at hc
    exact hc
  -- the direct inputs of `hone_exitQ_walk_of_env_massRel`: `hL29`, `hcell` and `hh` (with `H := ε^θ`) are discharged
  exact hone_exitQ_walk_of_env_massRel K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2
    hRr hdiam hsp rmin hRmin hVol hGreen hWalk hfinE hL29' hsc hεα hεmass hb (H := fun _ _ => ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (fun k ω hω p hp q hq => hcellD k ω hω p hp q hq) (fun k ω hω => hsmallAll k ω hω) hx1 hmomS hgood hN hpos hdbl

end Lemma68Window
end MatedCRT

#print axioms MatedCRT.Lemma68Window.hsp_massRel_of_lemma68
#print axioms MatedCRT.Lemma68Window.firstMoment_walkState_massRel
#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_massRel
#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env_massRel
#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env_direct_massRel
