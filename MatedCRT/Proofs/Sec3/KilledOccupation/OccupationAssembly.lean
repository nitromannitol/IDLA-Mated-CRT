import Mathlib
import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClock
import MatedCRT.Proofs.Sec3.KilledOccupation.MainOccupation
import MatedCRT.Proofs.Sec3.KilledOccupation.Potential
import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightIdentity
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock

/-!
# Appendix B: reduction of `FrozenLBMGreenOccupationRescaled` to the named inputs

Source: Bou-Rabee and Gwynne, arXiv:2211.04891, Appendix B, Theorem B.1 (`paper/appendix-occupation-C16.tex`,
`thm:occ-main` printed at :53-78, proof :429-470; corrected draft `thm:main`, `paper/idla_mated_crt-corrected.tex:4572`).
The Frozen target is `MatedCRT.FrozenLBMGreenOccupationRescaled` (`MatedCRT/FirstPass/Frozen/S3S4b.lean:51-62`), not edited.

This file proves the Prop-level reduction: the conclusion of `rescaled_occupation_green_identity`
(`MainOccupation.lean`) is the body of the Frozen Prop, and each of its hypotheses is either
discharged here from a committed producer or stated as an explicit named input of
`frozenLBMGreenOccupationRescaled_of_appendixB`, quantified as in the Frozen Prop (for each `γ`, `ρ`, `Ω`,
`S` with `S.IsValid 𝒮 γ`, and almost surely where the source says almost surely).

Discharged here (not inputs):
* `hclock` (`IsTimeChangeClock (S.clock ω b)`, a.s.): the field `MatedCRTEnv.IsValid.isLQGClock` already
  contains the time-change property for every starting point `z`; instantiated at `z = y`.
* `hweight` (eq:occ-weight, tex:256-258, its `g`-form): from the Prop `OccWeightIdentity` by
  `lintegral_eq_of_occWeight` (Mathlib `withDensity`).
* `hS3` (eq:occ-potential, tex:262-270): `ae_sup_greenPotential_finite` (`Potential.lean`) with the
  mass bound `ae_ballMass_le_rpow` (eq:occ-mass, tex:245-250).
* `hσexit` (first exit time attained, tex:37): `exitNN_props_of_lt_top`, from the a.s. finiteness input.
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- A disc `ball z r` contained in `ball 0 ρ` has radius at most `ρ` (used for the hypothesis `r ≤ ρ` of
`ae_sup_greenPotential_finite`). Proof: the two points `z ± t` with `ρ < t < r` lie in `ball z r`, hence in
`ball 0 ρ`, and their distance `2t` is at most the sum of their norms `< 2ρ`. -/
lemma radius_le_of_ball_subset {z : ℂ} {r ρ : ℝ} (hr : 0 < r) (h : ball z r ⊆ ball (0 : ℂ) ρ) :
    r ≤ ρ := by
  by_contra hlt
  rw [not_le] at hlt
  have hz : ‖z‖ < ρ := by
    have := h (mem_ball_self hr)
    rwa [mem_ball, dist_zero_right] at this
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  set t : ℝ := (r + ρ) / 2 with ht
  have ht0 : 0 < t := by linarith
  have hp : z + (t : ℂ) ∈ ball z r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    linarith
  have hm : z - (t : ℂ) ∈ ball z r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
    linarith
  have h1 := h hp
  have h2 := h hm
  rw [mem_ball, dist_zero_right] at h1 h2
  have htri : ‖(z + (t : ℂ)) - (z - (t : ℂ))‖ ≤ ‖z + (t : ℂ)‖ + ‖z - (t : ℂ)‖ := norm_sub_le _ _
  have hdiff : (z + (t : ℂ)) - (z - (t : ℂ)) = (2 : ℂ) * (t : ℂ) := by ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] at htri
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n] at htri
  linarith

/-- The exit time `exitNN z r b` (tex:37) of a path that leaves `ball z r` in finite time is attained: the path
stays in the disc strictly before it and lies outside the open disc at it. Proof: the set of times at which the
path is outside the disc is closed and nonempty, so its infimum belongs to it (`IsClosed.sInf_mem`). -/
lemma exitNN_props_of_lt_top {z : ℂ} {r : ℝ} {b : ContinuousPath ℂ}
    (hfin : pathExitTime (ball z r) ⇑b < ⊤) :
    (∀ s : ℝ≥0, s < exitNN z r b → ⇑b s ∈ ball z r) ∧ ⇑b (exitNN z r b) ∉ ball z r := by
  set T : Set ℝ≥0 := {t | ⇑b t ∉ ball z r} with hT
  have hTc : IsClosed T := isOpen_ball.isClosed_compl.preimage b.continuous
  have hne : T.Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    have hset : {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ ⇑b t ∉ ball z r} = ∅ := by
      ext s
      constructor
      · rintro ⟨t, -, ht⟩
        have htT : t ∈ T := ht
        rw [hem] at htT
        simp at htT
      · intro h
        simp at h
    have hτtop : pathExitTime (ball z r) ⇑b = ⊤ := by
      unfold pathExitTime
      rw [hset, sInf_empty]
    exact absurd (hτtop ▸ hfin) (lt_irrefl _)
  have ht₀ : sInf T ∈ T := hTc.csInf_mem hne (OrderBot.bddBelow T)
  have hτ : pathExitTime (ball z r) ⇑b = ((sInf T : ℝ≥0) : ℝ≥0∞) := by
    unfold pathExitTime
    apply le_antisymm
    · exact sInf_le ⟨sInf T, rfl, ht₀⟩
    · apply le_sInf
      rintro s ⟨t, rfl, ht⟩
      exact ENNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow T) ht)
  have hex : exitNN z r b = sInf T := by
    unfold exitNN
    rw [hτ, ENNReal.toNNReal_coe]
  refine ⟨fun s hs => ?_, by rw [hex]; exact ht₀⟩
  by_contra hsB
  have hsT : s ∈ T := hsB
  have hle : sInf T ≤ s := csInf_le (OrderBot.bddBelow T) hsT
  rw [hex] at hs
  exact absurd hle (not_le.mpr hs)

/-- The weight identity eq:occ-weight (tex:256-258) in the `g`-form: from `μ(A) = ∫_A |x|^{-γ²} dν` for measurable
`A ⊆ B_1`, the measures `μ` and `ν.withDensity (gammaWeight γ)` agree on `B_1`, and `∫_A g dμ = ∫_A g · gammaWeight γ dν`. -/
lemma lintegral_eq_of_occWeight {γ : ℝ} {μ ν : Measure ℂ}
    (h : ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 →
      μ A = ∫⁻ x in A, ENNReal.ofReal (‖x‖ ^ (-(γ ^ 2))) ∂ν)
    (A : Set ℂ) (hA : MeasurableSet A) (hAb : A ⊆ ball (0 : ℂ) 1) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in A, g x ∂μ = ∫⁻ x in A, g x * gammaWeight γ x ∂ν := by
  have hw : Measurable (gammaWeight γ) := by
    unfold gammaWeight
    fun_prop
  have hrestr : μ.restrict A = (ν.withDensity (gammaWeight γ)).restrict A := by
    refine Measure.ext fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter hA)]
    exact h (B ∩ A) (hB.inter hA) (inter_subset_right.trans hAb)
  calc ∫⁻ x in A, g x ∂μ = ∫⁻ x, g x ∂(μ.restrict A) := rfl
    _ = ∫⁻ x, g x ∂((ν.withDensity (gammaWeight γ)).restrict A) := by rw [hrestr]
    _ = ∫⁻ x, g x ∂((ν.restrict A).withDensity (gammaWeight γ)) := by
        rw [restrict_withDensity hA]
    _ = ∫⁻ x, (gammaWeight γ * g) x ∂(ν.restrict A) :=
        lintegral_withDensity_eq_lintegral_mul _ hw hg
    _ = ∫⁻ x in A, g x * gammaWeight γ x ∂ν :=
        lintegral_congr fun x => by simp [mul_comm]

/-- The weight identity of `rescaled_occupation_green_identity` (its `hweight`) from the Prop `OccWeightIdentity`
(eq:occ-weight, tex:256-258). -/
lemma weight_identity_of_occWeight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ ν : Ω → Measure ℂ}
    {γ : ℝ} (h : OccWeightIdentity P μ ν γ) :
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in A, g x ∂(μ ω) = ∫⁻ x in A, g x * gammaWeight γ x ∂(ν ω) :=
  h.mono fun _ hω A hA hAb g hg => lintegral_eq_of_occWeight hω.2 A hA hAb g hg

/-- The Green potential at the pole is finite almost surely (`eq:occ-potential`, tex:262-270, at `v = y`), from the
dyadic mass bound `BGMassUpperBoundDyadic` (eq:occ-BGmass, exponent `e`) and the Green disc formula. -/
lemma ae_greenFunction_lintegral_lt_top {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) {e ρ : ℝ} (he : 0 < e) (hBG : BGMassUpperBoundDyadic P μ e) (hρ1 : ρ < 1)
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ ball (0 : ℂ) ρ) (hG : GreenDiskFormula z r)
    (hy : y ∈ ball z r) :
    ∀ᵐ ω ∂P, ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) ∂(μ ω) < ⊤ := by
  have hρ₁ : (ρ + 1) / 2 < 1 := by linarith
  have hρρ₁ : ρ < (ρ + 1) / 2 := by linarith
  have hmass := ae_ballMass_le_rpow P μ he hρ₁ hBG
  filter_upwards [ae_sup_greenPotential_finite P μ he hρ₁ hρρ₁ hmass z hr
    (radius_le_of_ball_subset hr hball) hball hG] with _ hω
  obtain ⟨K, hK⟩ := hω
  exact lt_of_le_of_lt (hK y hy) ENNReal.ofReal_lt_top

/-- **Reduction of the Frozen occupation Prop (Appendix B, Theorem B.1).** Given the named inputs below, the
body of `FrozenLBMGreenOccupationRescaled 𝒮` holds. The conclusion of `rescaled_occupation_green_identity` is
exactly that body; its hypotheses are supplied as follows.

Named inputs (all quantified as in the Frozen Prop: `γ ∈ (0,2)`, `ρ ∈ (0,1)`, `S.IsValid 𝒮 γ`, `ball z r ⊆ ball 0 ρ`,
`y ∈ ball z r`; almost surely where the source says so):
* `ν`, `dA` : the regularized field measure `ν` (eq:occ-weight; `ν ω` the nonsingular regularization of the
  circle-average clock, tex:122-140) and the base clock `dA ω b` (lem:occ-base, tex:140-151). Data families,
  not constrained except through the inputs below.
* `hm0` : `0 < S.m₀` (positivity of the median exit time `m₀`, tex:450-458, eq:mo tex:727). MQ gap.
* `hBase` : `BaseOccupationIdentity` with base exit time `exitNN z r` (lem:occ-base, tex:140-151, with the cone
  transfer tex:462-468). MQ-li-8 gap.
* `hWeight` : `OccWeightIdentity S.P S.μ (ν γ Ω S) γ` (eq:occ-weight, tex:256-258). MQ-li-10b gap.
* `hMeas` : measurability of the inner occupation `b ↦ ∫_{[0,σ b]} q(b u) dA_b` (no written argument). MQ gap.
* `hS6` : the identification `S.clock = weightedClock dA ... ` on `[0, σ]` (identification `φ = Φ`, tex:370-425). MQ gap.
* `hBG` : the dyadic mass bound `BGMassUpperBoundDyadic` for some exponent `e > 0` (eq:occ-BGmass, tex:110-115). Literature.
* `hGreen` : the Green disc formula `GreenDiskFormula z r` for `ball z r ⊆ ball 0 ρ` (eq:occ-green, tex:44-47). Literature.
* `hExit` : planar Brownian motion from `y` leaves the disc `ball z r` in finite time, a.s. (standard). Literature.
-/
theorem frozenLBMGreenOccupationRescaled_of_appendixB (𝒮 : SpaceFillingSLEModel)
    (ν : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → Measure ℂ)
    (dA : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hm0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → 0 < S.m₀)
    (hBase : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      BaseOccupationIdentity S.P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y)
        (ν γ Ω S) (dA γ Ω S) (exitNN z r))
    (hWeight : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → OccWeightIdentity S.P S.μ (ν γ Ω S) γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(dA γ Ω S ω b))
    (hS6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s ≤ exitNN z r b,
        S.clock ω b s = (weightedClock (dA γ Ω S ω b) (fun u => gammaWeight γ (b u)) (exitNN z r b) s).toReal)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ e : ℝ, 0 < e ∧ BGMassUpperBoundDyadic S.P S.μ e)
    (hGreen : ∀ ρ : ℝ, ∀ z : ℂ, ∀ r : ℝ, 0 < r → ball z r ⊆ ball 0 ρ → GreenDiskFormula z r)
    (hExit : ∀ (z y : ℂ) (r : ℝ), 0 < r → y ∈ ball z r →
      ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion y, pathExitTime (ball z r) ⇑b < ⊤) :
    FrozenLBMGreenOccupationRescaled 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS r z y hr hball hy
  obtain ⟨e, he, hBGe⟩ := hBG γ hγ0 hγ2 Ω S hS
  have hS3 : ∀ᵐ ω ∂S.P, ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) ∂(S.μ ω) < ⊤ :=
    ae_greenFunction_lintegral_lt_top S.P S.μ he hBGe hρ1 hr hball (hGreen ρ z r hr hball) hy
  have hclock : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b) :=
    hS.isLQGClock.mono fun _ hω => (hω y).2
  have hσexit : ∀ᵐ b ∂planarBrownianMotion y,
      (∀ s < exitNN z r b, b s ∈ ball z r) ∧ b (exitNN z r b) ∉ ball z r :=
    (hExit z y r hr hy).mono fun b hb => exitNN_props_of_lt_top hb
  exact rescaled_occupation_green_identity S γ ρ hγ0 hγ2 hρ0 hρ1 𝒮 hS r z y hr hball hy
    (ν γ Ω S) (dA γ Ω S) (exitNN z r) (hm0 γ hγ0 hγ2 Ω S hS) hclock hσexit
    (hBase γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    (weight_identity_of_occWeight (hWeight γ hγ0 hγ2 Ω S hS))
    (hS6 γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy) hS3

end MatedCRT.KilledOccupation
