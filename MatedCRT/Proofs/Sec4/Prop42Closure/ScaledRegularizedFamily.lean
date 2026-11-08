import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScaleLaw
import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Conditions
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Harmonic
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle
import HarmonicBalls.Proofs.Sec6.GreenDilation
import HarmonicBalls.Audit.GreenSubharmonicTestClass

/-! # Scaled regularized cluster families (Proposition 4.2, z5)

Task `z5-scaled-regularized-family`. The Step is `ScaledRegularizedFamilyStep` (`PlateauScaleLaw.lean`): for `a, c > 0`
the dilation `μ ↦ c⁻¹ μ(a ·)`, `Λ ↦ a⁻¹ Λ(c ·)` of a regularized cluster family at `0` is one at `0`.
Written argument: `notes/prop42-proof/prop42-proof.tex` lines 252-256 (scaling of the mean-value property, mass
parameter and family conditions) and [HB] Lemma 5.7 (`lqg_harmonic_ball-corrected.tex` lines 905-938).

Proved here from existing MatedCRT and HB dilation lemmas:
* the bridges `scaledMeasure = rescaledMeasure` and `scaledFamily = rescaledFamily` for `a, c > 0`;
* the harmonic-ball conditions (a)-(b) under the dilation (`SatisfiesHarmonicBallConditionsOn.rescale`);
* the regularized clusters under the dilation, `regularizedCluster (rescaled) r 0 t = (a·)⁻¹ regularizedCluster μ (a r) 0 (c t)`
  (`cluster_rescaledMeasure`, the pathwise identity of Lemma 5.7, and the homeomorphism invariance of `interior ∘ closure`);
* the sub-mean-value inequality under the dilation, and the transfer of the bounded-domain test functions of the
  subharmonic test class (`HarmonicBalls.greenFunction_dilation`, `HarmonicBalls.greenPotential_dilation`).

Not proved here: the bounded-domain representatives of the dilated subharmonic balls, carried as the named Step
`ScaledBoundedRepresentativesStep`. See its docstring for the boundary. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls InnerProductSpace
open scoped Pointwise ENNReal

/-- **Named input (an explicit hypothesis, not an axiom): bounded-domain representatives of the dilated subharmonic
balls.** For `a, c > 0` and a subharmonic ball `Λ` centred at `0` for `μ`, every test function of the scaled
subharmonic test class `subharmonicBallTestClass ((a·)⁻¹ Λ) 0` agrees, at the centre and `μ_a`-a.e. on `(a·)⁻¹ Λ`,
with a test function of the bounded-domain class `boundedSubharmonicBallTestClass ((a·)⁻¹ Λ) 0`.
This is `HasBoundedSubharmonicRepresentatives` (HB `Audit/GreenSubharmonicTestClass.lean:48`) for the scaled data.
Boundary: the unscaled witnesses `O` of `subharmonicBallTestClass` need not be bounded, and HB's Audit states the
representative assertion as an open potential-theoretic claim (`GreenSubharmonicTestClass.lean:1-6`). HB's
`Proofs/Potential/BoundedSubharmonicRepresentatives.lean` reduces it to the μ-free pointwise criterion
`forall_hasBoundedSubharmonicRepresentatives_iff_pointwise` (line 140) and proves transfer under absolute continuity
(line 160); none of these covers the dilated measure. The written argument (prop42-proof.tex:252-256) scales the
mean-value property but does not treat unbounded witnesses. -/
def ScaledBoundedRepresentativesStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : Set ℂ) (a c : ℝ), 0 < a → 0 < c → IsSubharmonicBall μ Λ 0 →
    HasBoundedSubharmonicRepresentatives (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0

/-! ## Bridges between the Prop 4.2 and the MatedCRT dilation notation -/

theorem scaledMeasure_eq_rescaledMeasure (μ : Measure ℂ) {a c : ℝ} (hc : 0 < c) :
    scaledMeasure μ a c = rescaledMeasure μ a c := by
  unfold scaledMeasure rescaledMeasure
  simp only [div_eq_inv_mul, ENNReal.ofReal_inv_of_pos hc]

theorem scaledFamily_eq_rescaledFamily (Λ : ℝ → Set ℂ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    scaledFamily Λ a c = rescaledFamily Λ a c := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  funext t
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (a : ℂ) * (((a⁻¹ : ℝ) : ℂ) * y) ∈ Λ (c * t)
    rw [Complex.ofReal_inv, mul_inv_cancel_left₀ hac]
    exact hy
  · intro hx
    refine ⟨(a : ℂ) * x, hx, ?_⟩
    show ((a⁻¹ : ℝ) : ℂ) * ((a : ℂ) * x) = x
    rw [Complex.ofReal_inv, inv_mul_cancel_left₀ hac]

/-! ## The harmonic-ball conditions under the dilation -/

theorem satisfiesHarmonicBallConditions_rescaledMeasure {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {R b : ℝ}
    (h : SatisfiesHarmonicBallConditions μ Λ 0) (hR : 0 < R) (hb : 0 < b) :
    SatisfiesHarmonicBallConditions (rescaledMeasure μ R b) (rescaledFamily Λ R b) 0 :=
  MatedCRT.Sec1.satisfiesHarmonicBallConditions_of_forall_on fun _ hT =>
    SatisfiesHarmonicBallConditionsOn.rescale
      (MatedCRT.Sec1.satisfiesHarmonicBallConditionsOn_of_global h (mul_pos hb hT)) hR hb

/-! ## Regularized clusters under the dilation (Lemma 5.7 at the set level) -/

theorem regularizedCluster_rescaledMeasure (μ : Measure ℂ) {R b ρ t : ℝ} (hR : 0 < R) (hb : 0 < b) (hρ : 0 < ρ) :
    regularizedCluster (rescaledMeasure μ R b) ρ 0 t =
      (fun x : ℂ => (R : ℂ) * x) ⁻¹' regularizedCluster μ (R * ρ) 0 (b * t) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  let e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (R : ℂ) hRc
  have he : ⇑e = fun x : ℂ => (R : ℂ) * x := rfl
  unfold regularizedCluster
  rw [cluster_rescaledMeasure μ hR hb hρ, ← he, ← e.preimage_closure, ← e.preimage_interior]

/-! ## Mean-value transfer and bounded test functions under the dilation -/

theorem hasSubMeanValueProperty_rescaledMeasure {μ : Measure ℂ} {S : Set ℂ} {g : ℂ → ℝ} {R b : ℝ}
    (hR : R ≠ 0) (hb : 0 < b) (h : HasSubMeanValueProperty μ S 0 g) :
    HasSubMeanValueProperty (rescaledMeasure μ R b) ((fun x : ℂ => (R : ℂ) * x) ⁻¹' S) 0
      (fun x => g ((R : ℂ) * x)) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  obtain ⟨hint, hineq⟩ := h
  refine ⟨?_, ?_⟩
  · rw [integrableOn_rescaledMeasure_iff μ hR hb]
    simpa only [mul_inv_cancel_left₀ hRc] using hint
  · rw [setIntegral_rescaledMeasure μ hR hb _ S]
    have hreal : (rescaledMeasure μ R b).real ((fun x : ℂ => (R : ℂ) * x) ⁻¹' S) = b⁻¹ * μ.real S := by
      simp only [Measure.real, rescaledMeasure_preimage μ hR b S]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hb.le)]
    simp only [mul_zero, mul_inv_cancel_left₀ hRc]
    rw [hreal]
    have key : g 0 * (b⁻¹ * μ.real S) = b⁻¹ * (g 0 * μ.real S) := by ring
    rw [key]
    exact mul_le_mul_of_nonneg_left hineq (inv_nonneg.2 hb.le)

/-- **Bounded test functions transfer under the dilation.** If `f` is a bounded-domain subharmonic test function for the
dilated set `(R·)⁻¹ S` at `0`, then `y ↦ f(R⁻¹ y)` is one for `S` at `0`. The witness is the dilated bounded domain
`R • O'` (`HarmonicBalls.greenFunction_dilation`, `HarmonicBalls.greenPotential_dilation`, both for bounded domains). -/
theorem boundedSubharmonicBallTestClass_rescaled {S : Set ℂ} {f : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : f ∈ boundedSubharmonicBallTestClass ((fun x : ℂ => (R : ℂ) * x) ⁻¹' S) 0) :
    (fun y : ℂ => f ((R : ℂ)⁻¹ * y)) ∈ boundedSubharmonicBallTestClass S 0 := by
  obtain ⟨O', K', ν₁', ν₂', q', hO'o, hO'b, hcl', hK', hKO', hfin₁, hfin₂, hν₁K, hν₂K, hν₁S, hq', hν₂0, hint, rfl⟩ := hf
  have hR0 : R ≠ 0 := hR.ne'
  have hsmul : ∀ y : ℂ, (R : ℝ) • y = (R : ℂ) * y := fun y => Complex.real_smul
  have hsmul' : ∀ y : ℂ, (R : ℝ)⁻¹ • y = (R : ℂ)⁻¹ * y := fun y => by
    rw [Complex.real_smul, Complex.ofReal_inv]
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero R hR0
  have he : ⇑e = fun z : ℂ => (R : ℝ) • z := rfl
  have hpre : (fun x : ℂ => (R : ℂ) * x) ⁻¹' S = e ⁻¹' S := by
    ext x
    simp only [Set.mem_preimage, he, hsmul]
  have hgp : ∀ (μ : Measure ℂ) (x : ℂ), HarmonicBalls.greenPotential (e '' O') (μ.map e) (e x) =
      HarmonicBalls.greenPotential O' μ x := by
    intro μ x
    have h1 := HarmonicBalls.Section6.greenPotential_dilation hO'o hO'b (μ.map e) hR x
    have hcomp : ((fun z : ℂ => (R : ℝ)⁻¹ • z) ∘ e) = id := by
      funext z
      simp only [Function.comp_apply, he, id, inv_smul_smul₀ hR0]
    rw [Measure.map_map (measurable_const_smul _) e.continuous.measurable, hcomp, Measure.map_id] at h1
    exact h1
  refine ⟨e '' O', e '' K', ν₁'.map e, ν₂'.map e, fun y => q' ((R : ℝ)⁻¹ • y), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.isOpen_image.2 hO'o
  · rw [he, Set.image_smul]
    exact hO'b.smul₀ (R : ℝ)
  · rw [← e.image_preimage S, ← e.image_closure]
    rw [hpre] at hcl'
    exact Set.image_mono hcl'
  · exact hK'.image e.continuous
  · exact Set.image_mono hKO'
  · infer_instance
  · infer_instance
  · rw [e.measurableEmbedding.map_apply, Set.preimage_compl, e.injective.preimage_image]
    exact hν₁K
  · rw [e.measurableEmbedding.map_apply, Set.preimage_compl, e.injective.preimage_image]
    exact hν₂K
  · rw [e.measurableEmbedding.map_apply, ← hpre]
    exact hν₁S
  · unfold InnerProductSpace.HarmonicOnNhd
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : (R : ℝ)⁻¹ • e x = x := inv_smul_smul₀ hR0 x
    apply HarmonicBalls.Section6.harmonicAt_comp_real_dilation (inv_ne_zero hR0)
    rw [hx']
    exact hq' x hx
  · rw [e.measurableEmbedding.map_apply]
    have hpre0 : e ⁻¹' {0} = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, he]
      constructor
      · intro h0
        rcases smul_eq_zero.1 h0 with h | h
        · exact absurd h hR0
        · exact h
      · intro h0
        rw [h0, smul_zero]
    rw [hpre0]
    exact hν₂0
  · rw [(e.measurableEmbedding).integrable_map_iff]
    have hG : (HarmonicBalls.greenFunction (e '' O') 0) ∘ e = HarmonicBalls.greenFunction O' 0 := by
      funext w
      have h1 := HarmonicBalls.Section6.greenFunction_dilation O' hO'b hR 0 w
      rw [smul_zero] at h1
      exact h1
    rw [hG]
    exact hint
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← hsmul']
    have hy1 : e ((R : ℝ)⁻¹ • y) = y := by
      rw [he]
      exact smul_inv_smul₀ hR0 y
    have h1 := hgp ν₁' ((R : ℝ)⁻¹ • y)
    have h2 := hgp ν₂' ((R : ℝ)⁻¹ • y)
    rw [hy1] at h1 h2
    rw [h1, h2]

/-- **Subharmonic balls under the dilation**, conditional on the bounded representatives (`hrep`). -/
theorem isSubharmonicBall_rescaledMeasure {μ : Measure ℂ} {S : Set ℂ} {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (h : IsSubharmonicBall μ S 0)
    (hrep : HasBoundedSubharmonicRepresentatives (rescaledMeasure μ R b) ((fun x : ℂ => (R : ℂ) * x) ⁻¹' S) 0) :
    IsSubharmonicBall (rescaledMeasure μ R b) ((fun x : ℂ => (R : ℂ) * x) ⁻¹' S) 0 := by
  obtain ⟨hopen, hmem, hpos, hfin, hmv⟩ := h
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  refine ⟨hopen.preimage (continuous_const.mul continuous_id), ?_, ?_, ?_, ?_⟩
  · show (R : ℂ) * 0 ∈ S
    rw [mul_zero]
    exact hmem
  · rw [rescaledMeasure_preimage μ hR0 b S]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hb)).ne' hpos.ne'
  · rw [rescaledMeasure_preimage μ hR0 b S]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · refine (HarmonicBalls.subMeanValue_all_iff_bounded_of_representatives hrep).2 ?_
    intro f hf
    have hg := boundedSubharmonicBallTestClass_rescaled hR hf
    have hH := hmv _ (boundedSubharmonicBallTestClass_subset S 0 hg)
    have hT := hasSubMeanValueProperty_rescaledMeasure hR0 hb hH
    simpa only [inv_mul_cancel_left₀ hRc] using hT

/-! ## The Step ScaledRegularizedFamilyStep, conditional on the named representatives -/

/-- **`ScaledRegularizedFamilyStep` from the named bounded-representative input.** Every conjunct of
`IsRegularizedClusterFamily` is transferred: the harmonic-ball conditions and the regularized-cluster identity are
proved; the subharmonic-ball conjunct uses `ScaledBoundedRepresentativesStep` (see its docstring). -/
theorem scaledRegularizedFamilyStep_of_representatives (hrep : ScaledBoundedRepresentativesStep) :
    ScaledRegularizedFamilyStep := by
  intro μ Λ a c ha hc hreg
  unfold IsRegularizedClusterFamily at hreg ⊢
  obtain ⟨h1, h2, h3⟩ := hreg
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  rw [scaledMeasure_eq_rescaledMeasure μ hc, scaledFamily_eq_rescaledFamily Λ ha c]
  refine ⟨satisfiesHarmonicBallConditions_rescaledMeasure h1 ha hc, fun t ht => ?_, fun t ht s hs hcl r hr => ?_⟩
  · have hΛ : IsSubharmonicBall μ (Λ (c * t)) 0 := h2 (c * t) (mul_pos hc ht)
    have hrep' := hrep μ (Λ (c * t)) a c ha hc hΛ
    rw [scaledMeasure_eq_rescaledMeasure μ hc] at hrep'
    exact isSubharmonicBall_rescaledMeasure ha hc hΛ hrep'
  · have hr0 : 0 < r := lt_of_lt_of_le hs hr
    let e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (a : ℂ) ha0
    have hcl' : closure (Λ (c * t)) ⊆ ball 0 (a * s) := by
      intro w hw
      have hxmem : (a : ℂ)⁻¹ * w ∈ e ⁻¹' closure (Λ (c * t)) := by
        show (a : ℂ) * ((a : ℂ)⁻¹ * w) ∈ closure (Λ (c * t))
        rw [mul_inv_cancel_left₀ ha0 w]
        exact hw
      rw [e.preimage_closure] at hxmem
      have hxball : (a : ℂ)⁻¹ * w ∈ ball (0 : ℂ) s := hcl hxmem
      rw [mem_ball_zero_iff] at hxball ⊢
      have hw' : w = (a : ℂ) * ((a : ℂ)⁻¹ * w) := (mul_inv_cancel_left₀ ha0 w).symm
      calc ‖w‖ = ‖(a : ℂ) * ((a : ℂ)⁻¹ * w)‖ := by rw [← hw']
        _ = a * ‖(a : ℂ)⁻¹ * w‖ := norm_dilation ha _
        _ < a * s := mul_lt_mul_of_pos_left hxball ha
    have hΛeq : Λ (c * t) = regularizedCluster μ (a * r) 0 (c * t) :=
      h3 (c * t) (mul_pos hc ht) (a * s) (mul_pos ha hs) hcl' (a * r) (mul_le_mul_of_nonneg_left hr ha.le)
    show (fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ (c * t) = regularizedCluster (rescaledMeasure μ a c) r 0 t
    rw [hΛeq, regularizedCluster_rescaledMeasure μ ha hc hr0]

end MatedCRT
