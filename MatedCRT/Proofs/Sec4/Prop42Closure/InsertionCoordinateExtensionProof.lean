import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionAffineMeasureTransport
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionNormalizedCircleLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionDyadicDecoder

/-!
# Insertion-coordinate extension: assembly of the exact Step (steps3:649-702)

Internal module; it cites no literature input of its own. It proves the exact Step `InsertionCoordinateExtensionStep`
(`InsertionCoordinate.lean`, steps3 Section 2, lines 405-712) from two displayed residual hypotheses:

* `hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt` (Sheffield-Wang, arXiv:1605.06171v2, Theorem 1.1, p. 3;
  staged literature input, compact-interior form), used only for the punctured all-scale convergence away from the
  insertion point (steps3:630);
* `hDec : LocalDirichletHarmonicDecompositionStep` (steps3:609-621, producer residual, not formalized), the local
  Dirichlet/harmonic decomposition.

Everything else is proved here.

* The normalized circle process `(r, z) ↦ h(|a| r, a z) - h(|a|, 0)` is measurable and a.s. continuous, and has the same
  law as the original circle process (`normalized_circle_law_complex`, steps3:473-499).
* Its measurable continuous modification `Gn` and the constructed decoder give the normalized insertion limit
  `μ^a = dyadicDecoder (Gn ·)` (steps3 `μ^a = 𝓜(h^a_∘)`, eq:normalized-measure-law). Equality in law of the modifications
  transfers both the dyadic convergence and the absence of an atom at `0` (steps3 lem:insertion-no-atom); no
  whole-plane GFF property of the normalized field is used.
* The fixed-affine identity `C_a μ^a = (x ↦ x/a)_* μ` (steps3 eq:affine-dilation-measure) follows as in
  `insertion_affine_dilation_measure_ae`, with the atom of `μ^a` supplied by that law transfer.
* The translation `p = b/a` is carried by `lqgApprox_affineArray_eq` (steps3:673-675) and the pushforward of the dyadic
  approximations by `z ↦ z - p`.

Terminology: vague convergence of Radon measures and the dyadic insertion limit (Duplantier-Sheffield 2011, Prop. 1.1;
Berestycki-Powell); test functions are compactly supported continuous functions (Armitage-Gardiner).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- The normalized positive-radius circle process `(r, z) ↦ h(|a| r, a z) - h(|a|, 0)` is measurable in `ω`. -/
theorem measurable_normalizedCircleProc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {a : ℂ} (ha : a ≠ 0) :
    Measurable fun ω => circleProc (normalizedCircleProc a (hcirc ω)) := by
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine Measurable.of_eval fun p => ?_
  show Measurable fun ω => hcirc ω (‖a‖ * (p.1 : ℝ)) (a * p.2) - hcirc ω ‖a‖ 0
  exact (hGFF.measurable_circle (‖a‖ * (p.1 : ℝ)) (a * p.2) (mul_pos hR p.1.2)).sub
    (hGFF.measurable_circle ‖a‖ 0 hR)

/-- The normalized circle process is a.s. continuous on `(0, ∞) × ℂ`. -/
theorem ae_continuous_normalizedCircleProc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {a : ℂ} (ha : a ≠ 0) :
    ∀ᵐ ω ∂P, Continuous (circleProc (normalizedCircleProc a (hcirc ω))) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine continuous_circleProc_of_continuousOn ?_
  have hmap : MapsTo (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2))
      (Set.Ioi 0 ×ˢ Set.univ) (Set.Ioi 0 ×ˢ Set.univ) := by
    intro p hp
    exact ⟨mul_pos hR hp.1, Set.mem_univ _⟩
  have hc : ContinuousOn (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2)) (Set.Ioi 0 ×ˢ Set.univ) :=
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)).continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℂ => hcirc ω (‖a‖ * p.1) (a * p.2)) (Set.Ioi 0 ×ˢ Set.univ) :=
    hω.comp hc hmap
  have h2 : ContinuousOn (fun _ : ℝ × ℂ => hcirc ω ‖a‖ 0) (Set.Ioi 0 ×ˢ Set.univ) := continuousOn_const
  exact h1.sub h2

/-- **Normalized insertion limit (steps3 eq:normalized-measure-law).** For `a ≠ 0` there is a random measure `μ^a`
which is a.s. the insertion-`α` LQG limit of the normalized field `h^a_∘ = normalizedCircleProc a (hcirc ω)` and has no
atom at `0` a.s. It is `μ^a = dyadicDecoder (Gn ·)` for a measurable continuous modification `Gn` of the normalized circle
process; `Gn` and the modification `G` of the original field have the same law, so the dyadic convergence set and the
atom-free event transfer. No whole-plane GFF property of the normalized field is used. -/
theorem normalized_insertion_limit_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {a : ℂ} (ha : a ≠ 0) :
    ∃ μa : Ω → Measure ℂ,
      (∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (normalizedCircleProc a (hcirc ω))) (μa ω)) ∧
      ∀ᵐ ω ∂P, μa ω {0} = 0 := by
  obtain ⟨G, hG, hGω, hμdec⟩ := insertion_identification_ae hGFF hμ
  obtain ⟨Gn, hGn, hGnω⟩ := exists_contModification
    (fun ω => circleProc (normalizedCircleProc a (hcirc ω)))
    (measurable_normalizedCircleProc hGFF ha) (ae_continuous_normalizedCircleProc hGFF ha)
  have hlaw : P.map Gn = P.map G :=
    map_contModification_eq (measurable_normalizedCircleProc hGFF ha) (measurable_circleProc hGFF) hGn hG
      hGnω hGω (normalized_circle_law_complex hGFF ha)
  have hS : MeasurableSet (DyadicConvSet γ α) := measurableSet_dyadicConvSet γ α
  -- the original modification lies in the dyadic convergence set almost surely
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hGmem : ∀ᵐ ω ∂P, G ω ∈ DyadicConvSet γ α := by
    filter_upwards [hGω, hμ'] with ω h1 h2
    refine mem_dyadicConvSet_of_isLQGLimit (m := μ ω) ?_
    rw [h1]
    exact isLQGLimit_circleProc_iff.2 h2
  -- transfer the membership through the equality in law
  have hGnmem : ∀ᵐ ω ∂P, Gn ω ∈ DyadicConvSet γ α := by
    have h1 : ∀ᵐ x ∂(P.map G), x ∈ DyadicConvSet γ α :=
      (ae_map_iff hG.aemeasurable hS).2 hGmem
    rw [← hlaw] at h1
    exact (ae_map_iff hGn.aemeasurable hS).1 h1
  refine ⟨fun ω => dyadicDecoder γ α (Gn ω), ?_, ?_⟩
  · filter_upwards [hGnmem, hGnω] with ω h1 h2
    have h := isLQGLimit_dyadicDecoder h1
    rw [h2] at h
    exact isLQGLimit_circleProc_iff.1 h
  · -- the atom of the decoder at `0` vanishes on `G`, hence on `Gn` by equality in law
    have hNo : ∀ᵐ ω ∂P, μ ω {0} = 0 := insertion_no_atom_zero_ae_unconditional hγ hαQ hGFF hμ
    have hG0 : ∀ᵐ ω ∂P, dyadicDecoder γ α (G ω) {0} = 0 := by
      filter_upwards [hμdec, hNo] with ω h1 h2
      rw [← h1]
      exact h2
    have hset : MeasurableSet {u : ContCircle | dyadicDecoder γ α u {0} = 0} :=
      ((Measure.measurable_coe (measurableSet_singleton 0)).comp
        (measurable_dyadicDecoder γ α)) (measurableSet_singleton 0)
    have hG0' : ∀ᵐ x ∂(P.map G), dyadicDecoder γ α x {0} = 0 :=
      (ae_map_iff hG.aemeasurable (p := fun u => dyadicDecoder γ α u {0} = 0) hset).2 hG0
    rw [← hlaw] at hG0'
    exact (ae_map_iff hGn.aemeasurable (p := fun u => dyadicDecoder γ α u {0} = 0) hset).1 hG0'

/-- **Fixed-affine dilation identity (steps3 eq:affine-dilation-measure).** Let `a ≠ 0`. Suppose that the punctured all-scale
convergence of `μ` holds away from `0` (the conclusion of `punctured_allScales_of_steps_interior`), that `μ` and `μ^a` have
no atom at `0`, and that `μ^a` is the insertion limit of the normalized field. Then almost surely
`C_a μ^a = (x ↦ x/a)_* μ`, where `C_a = affineFactor`. This is `insertion_affine_dilation_measure_ae` with its
hypothesis `hNorm` replaced by the atom of `μ^a` (`hNoaω`), which is supplied by `normalized_insertion_limit_ae`. -/
theorem affine_dilation_ae_of_atoms {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) {hcirc : Ω → ℝ → ℂ → ℝ} {μ μa : Ω → Measure ℂ} {a : ℂ} (ha : a ≠ 0)
    (hP : ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ ({0}ᶜ : Set ℂ) →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))))
    (hNoω_ae : ∀ᵐ ω ∂P, μ ω {0} = 0) (hNoa_ae : ∀ᵐ ω ∂P, μa ω {0} = 0)
    (hμaL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (normalizedCircleProc a (hcirc ω))) (μa ω))
    (hμL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω)) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω
      = Measure.map (fun x : ℂ => x / a) (μ ω) := by
  filter_upwards [hP, hNoω_ae, hNoa_ae, hμaL, hμL] with ω hPω hNoω hNoaω hμaω hμω
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hC0 : affineFactor γ α a (hcirc ω) ≠ 0 := (affineFactor_pos γ α a (hcirc ω)).ne'
  have hdc : Continuous (fun x : ℂ => x / a) := continuous_id.div_const a
  -- Step 1: the identity for test functions vanishing near the atom
  have htest : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ ({0}ᶜ : Set ℂ) →
      ∫ z, g z ∂(μa ω) = (affineFactor γ α a (hcirc ω))⁻¹ * ∫ z, g (z / a) ∂(μ ω) := by
    intro g hg hgc hgs
    have hdiv : Continuous (fun x : ℂ => g (x / a)) := hg.comp hdc
    have hdivc : HasCompactSupport (fun x : ℂ => g (x / a)) := by
      refine HasCompactSupport.intro (K := (fun y : ℂ => a * y) '' tsupport g)
        (hgc.isCompact.image (continuous_const.mul continuous_id)) ?_
      intro x hx
      show g (x / a) = 0
      by_contra hne
      exact hx ⟨x / a, subset_tsupport g hne, by field_simp⟩
    have hdivs : tsupport (fun x : ℂ => g (x / a)) ⊆ ({0}ᶜ : Set ℂ) := by
      have key : tsupport (fun x : ℂ => g (x / a)) ⊆ (fun x : ℂ => x / a) ⁻¹' tsupport g :=
        closure_minimal (fun x hx => subset_tsupport g hx)
          ((isClosed_tsupport g).preimage hdc)
      intro x hx
      have h1 : x / a ∈ tsupport g := key hx
      have h2 : x / a ≠ 0 := hgs h1
      show x ≠ 0
      intro h0
      apply h2
      rw [h0, zero_div]
    have h1 := hμaω.tendsto_integral g hg hgc
    have h2 : ∀ k : ℕ, ∫ z, g z ∂(lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a (hcirc ω)))
          (dyadicScale k))
        = (affineFactor γ α a (hcirc ω))⁻¹ *
            ∫ z, g (z / a) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) (‖a‖ * dyadicScale k)) := by
      intro k
      rw [lqgApprox_normalized_eq hγ ha (hcirc ω) (dyadicScale_pos k), integral_smul_measure,
        integral_map hdc.aemeasurable hg.aestronglyMeasurable,
        ENNReal.toReal_ofReal (inv_nonneg.2 (affineFactor_pos γ α a (hcirc ω)).le), smul_eq_mul]
    have h3 : Tendsto (fun k : ℕ => ∫ z, g (z / a) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω))
          (‖a‖ * dyadicScale k))) atTop (𝓝 (∫ z, g (z / a) ∂(μ ω))) := by
      have hlim : Tendsto (fun k : ℕ => ‖a‖ * dyadicScale k) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hR (dyadicScale_pos k)⟩
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul ‖a‖
        simpa [dyadicScale] using this
      exact (hPω _ hdiv hdivc hdivs).comp hlim
    exact tendsto_nhds_unique (h1.congr h2) (h3.const_mul (affineFactor γ α a (hcirc ω))⁻¹)
  -- Step 2: finiteness of both sides and vanishing of the atoms at `0`
  have := hμω.isLocallyFiniteMeasure
  have := hμaω.isLocallyFiniteMeasure
  have hmap_fin : IsFiniteMeasureOnCompacts (Measure.map (fun x : ℂ => x / a) (μ ω)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hdc.measurable hK.measurableSet]
    have hpre : (fun x : ℂ => x / a) ⁻¹' K = (fun y : ℂ => a * y) '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨x / a, hx, by field_simp⟩
      · rintro ⟨y, hy, rfl⟩
        rw [mem_preimage, mul_div_cancel_left₀ y ha]
        exact hy
    rw [hpre]
    exact (hK.image (continuous_const.mul continuous_id)).measure_lt_top
  have hsmul_fin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω) :=
    ⟨fun K hK => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  have hatom1 : (ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω) {0} = 0 := by
    rw [Measure.smul_apply, hNoaω, smul_zero]
  have hatom2 : Measure.map (fun x : ℂ => x / a) (μ ω) {0} = 0 := by
    rw [Measure.map_apply hdc.measurable (measurableSet_singleton 0)]
    have hpre0 : (fun x : ℂ => x / a) ⁻¹' {0} = {0} := by
      ext x
      simp [ha]
    rw [hpre0, hNoω]
  -- Step 3: agreement on test functions, then the atom-free uniqueness
  refine measure_eq_of_avoid_zero hatom1 hatom2 ?_
  intro g hg hgc hgs
  rw [integral_smul_measure, ENNReal.toReal_ofReal (affineFactor_pos γ α a (hcirc ω)).le, smul_eq_mul,
    integral_map hdc.aemeasurable hg.aestronglyMeasurable, htest g hg hgc hgs,
    ← mul_assoc, mul_inv_cancel₀ hC0, one_mul]

/-- **Translated fixed-affine limit (steps3:673-675).** If `μa` is the insertion limit of the normalized field and
`C_a μa = (x ↦ x/a)_* μ`, then the affine circle array `(r, z) ↦ H(|a| r, a z + b) + Q log |a|` has the vague limit
`(x ↦ (x - b)/a)_* μ`, with `p = b/a`. The approximating measures are `C_a (z ↦ z - p)_*` of the normalized ones
(`lqgApprox_affineArray_eq`). -/
theorem isLQGLimit_affineCircleArray_of_dilation {γ α : ℝ} {a b : ℂ} (ha : a ≠ 0) {h : ℝ → ℂ → ℝ}
    {μ μa : Measure ℂ} (hμ : IsLQGLimit γ (fieldCircleAverage α h) μ)
    (hμa : IsLQGLimit γ (fieldCircleAverage α (normalizedCircleProc a h)) μa)
    (hdil : ENNReal.ofReal (affineFactor γ α a h) • μa = Measure.map (fun x : ℂ => x / a) μ) :
    IsLQGLimit γ (affineCircleArray α (lqgQ γ) a b h) (Measure.map (fun x : ℂ => (x - b) / a) μ) := by
  have hcont : Continuous (fun x : ℂ => (x - b) / a) := (continuous_id.sub continuous_const).div_const a
  have hcont2 : Continuous (fun x : ℂ => x / a) := continuous_id.div_const a
  have hφ : Continuous (fun z : ℂ => z - b / a) := continuous_id.sub continuous_const
  have := hμ.isLocallyFiniteMeasure
  have : IsFiniteMeasureOnCompacts (Measure.map (fun x : ℂ => (x - b) / a) μ) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hcont.measurable hK.measurableSet]
    have hpre : (fun x : ℂ => (x - b) / a) ⁻¹' K = (fun y : ℂ => a * y + b) '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨(x - b) / a, hx, by field_simp; ring⟩
      · rintro ⟨y, hy, rfl⟩
        show (a * y + b - b) / a ∈ K
        rw [add_sub_cancel_right, mul_div_cancel_left₀ y ha]
        exact hy
    rw [hpre]
    exact (hK.image ((continuous_const.mul continuous_id).add continuous_const)).measure_lt_top
  refine ⟨inferInstance, fun f hf hcs => ?_⟩
  -- the translated test function
  have hg : Continuous (fun z : ℂ => f (z - b / a)) := hf.comp hφ
  have hgc : HasCompactSupport (fun z : ℂ => f (z - b / a)) := by
    refine HasCompactSupport.intro (K := (fun y : ℂ => y + b / a) '' tsupport f)
      (hcs.isCompact.image (continuous_id.add continuous_const)) ?_
    intro z hz
    show f (z - b / a) = 0
    by_contra hne
    exact hz ⟨z - b / a, subset_tsupport f hne, by simp⟩
  -- the approximations of the affine array are `C_a (z ↦ z - p)_*` of the normalized approximations
  have hA : ∀ k : ℕ, ∫ z, f z ∂(lqgApprox γ (affineCircleArray α (lqgQ γ) a b h) (dyadicScale k))
      = (ENNReal.ofReal (affineFactor γ α a h)).toReal *
          ∫ z, f (z - b / a) ∂(lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a h)) (dyadicScale k)) := by
    intro k
    rw [lqgApprox_affineArray_eq ha h (dyadicScale_pos k), integral_smul_measure,
      integral_map hφ.aemeasurable hf.aestronglyMeasurable, smul_eq_mul]
  have hB := hμa.tendsto_integral (fun z : ℂ => f (z - b / a)) hg hgc
  -- the limit integral, through the identity `C_a μa = (x ↦ x/a)_* μ`
  have hkey : ∫ z, f z ∂(Measure.map (fun x : ℂ => (x - b) / a) μ)
      = (ENNReal.ofReal (affineFactor γ α a h)).toReal * ∫ z, f (z - b / a) ∂μa := by
    calc ∫ z, f z ∂(Measure.map (fun x : ℂ => (x - b) / a) μ)
        = ∫ x, f ((x - b) / a) ∂μ := integral_map hcont.aemeasurable hf.aestronglyMeasurable
      _ = ∫ x, f (x / a - b / a) ∂μ := by simp only [sub_div]
      _ = ∫ y, f (y - b / a) ∂(Measure.map (fun x : ℂ => x / a) μ) :=
          (integral_map hcont2.aemeasurable (hf.comp hφ).aestronglyMeasurable).symm
      _ = ∫ y, f (y - b / a) ∂(ENNReal.ofReal (affineFactor γ α a h) • μa) := by rw [hdil]
      _ = (ENNReal.ofReal (affineFactor γ α a h)).toReal * ∫ y, f (y - b / a) ∂μa := by
          rw [integral_smul_measure, smul_eq_mul]
  rw [hkey]
  exact Tendsto.congr (fun k => (hA k).symm) (hB.const_mul (ENNReal.ofReal (affineFactor γ α a h)).toReal)

/-- **The exact Step `InsertionCoordinateExtensionStep`, assembled.** It is proved from the two displayed residuals
`hSWI` (Sheffield-Wang compact-interior all-scale input, Proposed literature input) and `hDec` (the local Dirichlet/harmonic
decomposition, steps3:609-621, producer residual). The translation parameter is `b`, with `p = b/a` as in steps3:673-675.
No other hypothesis is assumed. -/
theorem insertionCoordinateExtensionStep_of_components
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep) : InsertionCoordinateExtensionStep := by
  unfold InsertionCoordinateExtensionStep
  intro γ α hγ hγ2 hαQ Ω _ P hC hcirc μ _ hGFF hμ a ha b
  obtain ⟨μa, hμaL, hNoa⟩ := normalized_insertion_limit_ae hγ hαQ hGFF hμ ha
  have hP := punctured_allScales_of_steps_interior hγ hγ2 hGFF hμ hSWI hDec
  have hNo := insertion_no_atom_zero_ae_unconditional hγ hαQ hGFF hμ
  have hμL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hdil := affine_dilation_ae_of_atoms hγ ha hP hNo hNoa hμaL hμL
  filter_upwards [hdil, hμaL, hμL] with ω h1 h2 h3
  exact isLQGLimit_affineCircleArray_of_dilation ha h3 h2 h1

end MatedCRT
