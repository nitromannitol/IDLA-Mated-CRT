import MatedCRT.FirstPass.S4d.ConeScaleConstancy
import MatedCRT.FirstPass.S4d.JumpTimes
import MatedCRT.FirstPass.S4d.StrictGapReduction
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# Fixed-time union `Λ_t = ⋃_{0<s<t} Λ_s` almost surely (FIRST PASS, S4d, B1 assembly)

Proves `StrictGapFixedTimeUnionStep 𝒮` (`StrictGapReduction.lean`) from three inputs, all explicit:
* `ConeScaleInvarianceStmt` (Lemma 2.6 of arXiv:2211.04891, law invariance of the pair under cone scaling);
* `ConeGlobalFamilyPairAEMeasurableStep` (B2, OPEN named step) and `ConeRescaledPairAEMeasurableStep` (B2R, OPEN);
* `FrozenConeScalingLaw 𝒮` (FIRST-PASS FROZEN; positivity of `R_b`).

Route (ChatGPT Sections 3-5, operator 00:08): `P(E_t)` is constant in `t > 0` (`strictGapEvent_const`); a
measurable version of the pair gives a gated family `gatedFamily N Gm` that is good everywhere and has measurable
coordinates; `strictGapJump_pos_countable` makes `{t | P(E_t) > 0}` countable, so the constant is `0`
(`strictGapJump_null_of_const`); hence `Λ_t = ⋃_{0<s<t} Λ_s` a.s.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- The gated family: `gatedFamily N G s ω = {x | ω ∉ N ∧ (G ω).2 (s, x)}`, with `G` a measurable version of the
pair (circle averages, global family process) and `N` a measurable null set outside which the cone family is good. -/
def gatedFamily {Ω : Type} (N : Set Ω) (G : Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop)) :
    ℝ → Ω → Set ℂ :=
  fun s ω => {x : ℂ | ω ∉ N ∧ (G ω).2 (s, x)}

/-- Union over `(0, t)` of a family, reindexed pointwise (a congruence for `iUnion` over `Ioo 0 t`). -/
theorem iUnion_Ioo_congr {f g : ℝ → Set ℂ} {t : ℝ} (h : ∀ u : ℝ, 0 < u → f u = g u) :
    (⋃ u ∈ Ioo (0 : ℝ) t, f u) = ⋃ u ∈ Ioo (0 : ℝ) t, g u := by
  ext x
  simp only [mem_iUnion, exists_prop]
  exact exists_congr fun u => and_congr_right fun hu => by rw [h u hu.1]

/-- **Fixed-time union from the probabilistic inputs.** For a cone family `Λ` with the measurability and
scaling inputs, `Λ_t = ⋃_{0<s<t} Λ_s` almost surely, for each deterministic `t > 0`. -/
theorem fixedTimeUnion_of_pair {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hG : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P)
    (hG' : ∀ b : ℝ, 0 < b → AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) P)
    (hlaw : ∀ b : ℝ, 0 < b →
      P.map (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =
        P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
          globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))))
    (hpos : ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, Λ ω t = ⋃ s ∈ Ioo (0 : ℝ) t, Λ ω s := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  -- a measurable version of the pair, and a measurable null set off which the family is good and the pair agrees
  obtain ⟨Gm, hGmm, hGmae⟩ : ∃ Gm : Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop), Measurable Gm ∧
      (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =ᵐ[P] Gm :=
    ⟨hG.mk _, hG.measurable_mk, hG.ae_eq_mk⟩
  have hQ : ∀ᵐ ω ∂P, GoodFamily (Λ ω) ∧ (circleProcess (hcirc ω), globalFamilyProcess (Λ ω)) = Gm ω := by
    filter_upwards [hΛ, hGmae] with ω h1 h2
    exact ⟨goodFamily_of_isConeHarmonicBallFamily h1, h2⟩
  obtain ⟨N, hsubN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hQ)
  have hgood : ∀ ω, ω ∉ N → GoodFamily (Λ ω) ∧
      (circleProcess (hcirc ω), globalFamilyProcess (Λ ω)) = Gm ω := by
    intro ω hω
    by_contra hc
    exact hω (hsubN hc)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => not_not.1 hω) hN0
  -- the gated family on the good part of Ω
  have hA : ∀ ω, ω ∉ N → ∀ s : ℝ, 0 < s → gatedFamily N Gm s ω = Λ ω s := by
    intro ω hω s hs
    have hsnd : (Gm ω).2 = globalFamilyProcess (Λ ω) := congrArg Prod.snd (hgood ω hω).2.symm
    ext x
    change (ω ∉ N ∧ (Gm ω).2 (s, x)) ↔ x ∈ Λ ω s
    rw [hsnd]
    exact ⟨fun h => h.2.2, fun h => ⟨hω, hs, h⟩⟩
  have hB : ∀ ω s, ¬ 0 < s → gatedFamily N Gm s ω = ∅ := by
    intro ω s hs
    ext x
    change (ω ∉ N ∧ (Gm ω).2 (s, x)) ↔ x ∈ (∅ : Set ℂ)
    by_cases hω : ω ∈ N
    · exact ⟨fun h => absurd hω h.1, fun h => by simp at h⟩
    · have hsnd : (Gm ω).2 = globalFamilyProcess (Λ ω) := congrArg Prod.snd (hgood ω hω).2.symm
      rw [hsnd]
      exact ⟨fun h => absurd h.2.1 hs, fun h => by simp at h⟩
  have hE : ∀ ω s, ω ∈ N → gatedFamily N Gm s ω = ∅ := by
    intro ω s hω
    ext x
    change (ω ∉ N ∧ (Gm ω).2 (s, x)) ↔ x ∈ (∅ : Set ℂ)
    exact ⟨fun h => absurd hω h.1, fun h => by simp at h⟩
  have hopen : ∀ s : ℝ, ∀ ω : Ω, IsOpen (gatedFamily N Gm s ω) := by
    intro s ω
    by_cases hs : 0 < s
    · by_cases hω : ω ∈ N
      · rw [hE ω s hω]
        exact isOpen_empty
      · rw [hA ω hω s hs]
        exact ((hgood ω hω).1).2.1 s hs
    · rw [hB ω s hs]
      exact isOpen_empty
  have hmono : ∀ ω : Ω, ∀ s t : ℝ, 0 < s → s ≤ t → gatedFamily N Gm s ω ⊆ gatedFamily N Gm t ω := by
    intro ω s t hs hst
    by_cases hω : ω ∈ N
    · rw [hE ω s hω]
      exact empty_subset _
    · rw [hA ω hω s hs, hA ω hω t (lt_of_lt_of_le hs hst)]
      exact ((hgood ω hω).1).1 (mem_Ioi.2 hs) (mem_Ioi.2 (lt_of_lt_of_le hs hst)) hst
  -- measurability of the gated coordinates and of the ball events
  have hcoord : ∀ (t : ℝ) (d : ℂ), MeasurableSet {ω : Ω | d ∈ {x : ℂ | (Gm ω).2 (t, x)}} := by
    intro t d
    exact measurableSet_setOfPred.2 ((measurable_pi_apply (t, d)).comp (measurable_snd.comp hGmm))
  have hK : ∀ K ∈ ratBallCover D, ∀ t : ℝ, MeasurableSet {ω | K ⊆ gatedFamily N Gm t ω} := by
    intro K hKmem t
    obtain ⟨⟨p, r⟩, ⟨hpD, hr⟩, rfl⟩ := hKmem
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_of_lt hr
    show MeasurableSet {ω | closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω}
    by_cases ht : 0 < t
    · have hset : {ω | closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω} =
          {ω : Ω | ω ∈ Nᶜ ∧ ProxySub D {x : ℂ | (Gm ω).2 (t, x)} p (r : ℝ)} := by
        ext ω
        change closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω ↔ ω ∈ Nᶜ ∧
          ProxySub D {x : ℂ | (Gm ω).2 (t, x)} p (r : ℝ)
        by_cases hω : ω ∈ N
        · have hL : ¬ closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω := by
            rw [hE ω t hω]
            intro h
            have hp := h (mem_closedBall_self hr0)
            simp at hp
          exact ⟨fun h => absurd h hL, fun h => absurd h.1 (not_not.2 hω)⟩
        · have hVt : {x : ℂ | (Gm ω).2 (t, x)} = Λ ω t := by
            have hsnd : (Gm ω).2 = globalFamilyProcess (Λ ω) := congrArg Prod.snd (hgood ω hω).2.symm
            ext x
            change (Gm ω).2 (t, x) ↔ x ∈ Λ ω t
            rw [hsnd]
            exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
          rw [hVt, hA ω hω t ht]
          obtain ⟨-, hopenT, hregT⟩ := (hgood ω hω).1
          have hb := closedBall_subset_iff_proxy (p := p) (r := (r : ℝ)) hDd (hopenT t ht) (hregT t ht) hr0
          exact ⟨fun h => ⟨hω, hb.1 h⟩, fun h => hb.2 h.2⟩
      rw [hset]
      exact (hNm.compl).inter (measurableSet_proxySub hDc (fun d _ => hcoord t d) p (r : ℝ))
    · have hempty : ∀ ω, gatedFamily N Gm t ω = ∅ := by
        intro ω
        by_cases hω : ω ∈ N
        · exact hE ω t hω
        · exact hB ω t ht
      have hset : {ω | closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω} = ∅ := by
        ext ω
        change closedBall p (r : ℝ) ⊆ gatedFamily N Gm t ω ↔ ω ∈ (∅ : Set Ω)
        rw [hempty ω]
        constructor
        · intro h
          have hp := h (mem_closedBall_self hr0)
          simp at hp
        · intro h
          simp at h
      rw [hset]
      exact MeasurableSet.empty
  -- countability of the positive-probability jump times, and constancy of the probability
  have hcount := strictGapJump_pos_countable hmono hopen (ratBallCover_countable hDc)
    (ratBallCover_cover hDd) hK P
  have hEU : ∀ u : ℝ, 0 < u → P (strictGapJumpEvent (gatedFamily N Gm) u) =
      P {ω | Λ ω u ≠ ⋃ s ∈ Ioo (0 : ℝ) u, Λ ω s} := by
    intro u hu
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hNae] with ω hω
    change gatedFamily N Gm u ω ≠ ⋃ s ∈ Ioo (0 : ℝ) u, gatedFamily N Gm s ω ↔
      Λ ω u ≠ ⋃ s ∈ Ioo (0 : ℝ) u, Λ ω s
    rw [hA ω hω u hu, iUnion_Ioo_congr (f := fun v => gatedFamily N Gm v ω) (g := fun v => Λ ω v)
      (fun v hv => hA ω hω v hv)]
  have hconst : ∀ s t : ℝ, 0 < s → 0 < t →
      P (strictGapJumpEvent (gatedFamily N Gm) s) = P (strictGapJumpEvent (gatedFamily N Gm) t) := by
    intro s t hs ht
    rw [hEU s hs, hEU t ht]
    exact strictGapEvent_const hΛ hG hG' hlaw hpos hs ht
  have hnull := strictGapJump_null_of_const P hcount hconst ht
  rw [hEU t ht] at hnull
  rw [ae_iff]
  exact hnull

/-- **StrictGapFixedTimeUnionStep from the explicit inputs.** Lemma 2.6 (`ConeScaleInvarianceStmt`), the OPEN steps
B2 and B2R, and the frozen positivity of `R_b` (`FrozenConeScalingLaw 𝒮`) give the fixed-time union for every valid
mated-CRT environment. -/
theorem strictGapFixedTimeUnion_of_steps (𝒮 : SpaceFillingSLEModel)
    (hscale : ConeScaleInvarianceStmt) (hB2 : ConeGlobalFamilyPairAEMeasurableStep)
    (hB2R : ConeRescaledPairAEMeasurableStep) (hcone : FrozenConeScalingLaw 𝒮) :
    StrictGapFixedTimeUnionStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ t ht
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hF : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  exact fixedTimeUnion_of_pair hΛ (hB2 γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hF Λ hΛ)
    (fun b hb => hB2R γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hF Λ hΛ b hb)
    (fun b hb => hscale γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hF Λ hΛ b hb)
    (fun b hb => (hcone γ hγ hγ2 Ω S hS b hb).1) ht

end MatedCRT
