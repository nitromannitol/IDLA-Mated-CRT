import MatedCRT.Proofs.Sec4.Prop42Closure.ScaledRegularizedFamily
import HarmonicBalls.Proofs.Potential.BoundedSubharmonicRepresentatives
import HarmonicBalls.Proofs.Potential.BoundedJensenPotentialIntegrability
import HarmonicBalls.Proofs.Potential.BoundedJensenSmoothTests
import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-! # Bounded representatives of the dilated subharmonic balls (Proposition 4.2, z5)

Task `z5-m5q-steps3-bounded-representatives-repair`. Written argument: `notes/wpn-steps3/steps3.tex`, lines 211-368:
the representative lemma `lem:bounded-jensen-representatives` (steps3:230-317) and the bounded repair
`prop:bounded-scaled-representatives` (steps3:319-368).

Proved here:
* `hasSubMeanValueProperty_scaled_boundedTestClass`: for a bounded-domain test function `f` of the dilated set
  `a⁻¹ Λ`, the sub-mean inequality for `scaledMeasure μ a c` on `a⁻¹ Λ` (steps3:340-368: the change of variables
  `F(y) = f(y/a)` into `T_b(Λ, 0)`, and the scaled mean-value transfer of `ScaledRegularizedFamily.lean`).
* `scaledBoundedRepresentativesStep_of_jensen`: the repaired `ScaledBoundedRepresentativesStep` (bounded `Λ`,
  steps3:319), from the representative lemma `BoundedJensenRepresentativesStep`. The mass identity
  `μ_a(a⁻¹ Λ) = c⁻¹ μ(Λ) ∈ (0, ∞)` and the boundedness and openness of `a⁻¹ Λ` are proved here.

* `bounded_jensen_representatives_of_localization_and_fatou`: the representative lemma `BoundedJensenRepresentativesStep`
  (steps3:230-233) from `JensenGreenLocalizationStmt` (steps3:180-225, Riesz localization of the real Green potentials;
  Saff Theorem 2.4 staged in `Proposed/Saff2010.lean`) and `JensenFatouFinitenessStmt`. The latter is the theorem
  `jensenFatouFinitenessStmt_of_smoothing`, from the named smoothing input `JensenSmoothingStmt` (steps3:247-262) and
  Harmonic-Balls lemmas (smooth tests, Fatou, finiteness). The witness transport and the bounded-domain localization `V`
  are Harmonic-Balls lemmas too; `greenKernelExtended` is established for bounded domains only. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls InnerProductSpace
open scoped Pointwise ENNReal

/-- **Named Step: the bounded representative lemma (steps3:230-233).** Let `S` be bounded and open, `z ∈ S`, and
`0 < m S < ∞`. If the sub-mean inequality (eq:submean) holds for `m` on `S` for every bounded-domain test function of
`S` at `z`, then every subharmonic test function of `S` at `z` has a bounded-domain representative for `m`
(`HasBoundedSubharmonicRepresentatives`, HB `Audit/GreenSubharmonicTestClass.lean:48`).
Written proof: steps3:234-317 (potential localization, bounded approximation and the Green identification).
Consumer: `scaledBoundedRepresentativesStep_of_jensen`, which gives the repaired `ScaledBoundedRepresentativesStep`. -/
def BoundedJensenRepresentativesStep : Prop :=
  ∀ (m : Measure ℂ) (S : Set ℂ) (z : ℂ), IsOpen S → Bornology.IsBounded S → z ∈ S → 0 < m S → m S < ⊤ →
    (∀ f ∈ boundedSubharmonicBallTestClass S z, HasSubMeanValueProperty m S z f) →
    HasBoundedSubharmonicRepresentatives m S z

/-- **Named internal Step: Riesz localization of the real Green potentials (steps3:180-225, eq:potential-localization).**
For bounded open `V ⊆ O` and a finite measure `ν` carried by a compact `K ⊆ V`, there is a harmonic `a` on `V` such that
at every `x ∈ V` with `ν {x} = 0`: `G_O(x, ·)` is `ν`-integrable iff `G_V(x, ·)` is, and then
`P_O ν x = a x + P_V ν x` (Armitage-Gardiner terminology: the real Green potentials of the Harmonic-Balls kernel).
Written proof: steps3:180-225 (regular parts bounded on compact sets) and Saff Theorem 2.4 (`Proposed/Saff2010.lean`). -/
def JensenGreenLocalizationStmt : Prop :=
  ∀ (O V : Set ℂ) (ν : Measure ℂ) (K : Set ℂ), IsOpen O → IsOpen V → Bornology.IsBounded V → V ⊆ O →
    IsCompact K → K ⊆ V → IsFiniteMeasure ν → ν Kᶜ = 0 →
    ∃ a : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd a V ∧
      ∀ x ∈ V, ν {x} = 0 →
        (Integrable (greenFunction O x) ν ↔ Integrable (greenFunction V x) ν) ∧
        (Integrable (greenFunction V x) ν → greenPotential O ν x = a x + greenPotential V ν x)

/-- **Named internal Step: Jensen-Fatou finiteness (steps3:247-262, eq:potential-jensen).** Let `V` be bounded open,
`S ∋ z` bounded open with `closure S ⊆ V`, and `ν` a finite measure carried by a compact `K ⊆ V`, with `ν {z} = 0` and
`G_V(z, ·) ∈ L¹(ν)`. If `m S < ∞` and `m` satisfies the sub-mean inequality on `T_b(S, z)`, then `m`-almost every
`x ∈ S` has `ν {x} = 0` and `G_V(x, ·) ∈ L¹(ν)`. Written proof: smooth superharmonic approximants `F_n = -χ u_{2,n}` in
`T_b(S, z)` (`mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport`), then Fatou
(`jensen_fatou_of_common_lower_bound`). -/
def JensenFatouFinitenessStmt : Prop :=
  ∀ (V S : Set ℂ) (z : ℂ) (m ν : Measure ℂ) (K : Set ℂ),
    IsOpen V → Bornology.IsBounded V → IsOpen S → Bornology.IsBounded S → z ∈ S → closure S ⊆ V →
    IsCompact K → K ⊆ V → IsFiniteMeasure ν → ν Kᶜ = 0 → ν {z} = 0 → Integrable (greenFunction V z) ν →
    m S < ⊤ → (∀ F ∈ boundedSubharmonicBallTestClass S z, HasSubMeanValueProperty m S z F) →
    ∀ᵐ x ∂(m.restrict S), ν {x} = 0 ∧ Integrable (greenFunction V x) ν

/-- **The representative lemma `BoundedJensenRepresentativesStep`, from its two named analytic inputs.** The witness
`(O, K, ν₁, ν₂, q)` of `f ∈ T(S, z)` is localized to a bounded `V` with `closure S ⊆ V ⊆ O`
(`exists_bounded_open_containing_closure_and_compact`). `JensenGreenLocalizationStmt` gives the harmonic corrections
`a₁, a₂` on `V`, with identities at `z` and at every `x ∈ S` for `ν₁` (where `ν₁ S = 0`). `JensenFatouFinitenessStmt`
gives the identity for `ν₂` `m`-a.e. on `S`. The bounded-witness transport `bounded_representative_of_source_corrections`
then gives the representative. -/
theorem bounded_jensen_representatives_of_localization_and_fatou (hLoc : JensenGreenLocalizationStmt)
    (hFat : JensenFatouFinitenessStmt) : BoundedJensenRepresentativesStep := by
  intro m S z hS hSb hz _hm0 hmtop hJ
  unfold HasBoundedSubharmonicRepresentatives
  intro f hf
  obtain ⟨O, K, ν₁, ν₂, q, hO, hSO, hK, hKO, hν₁, hν₂, h₁K, h₂K, hν₁S, hq, hz₂, hi₂, rfl⟩ := hf
  obtain ⟨V, hV, hVb, hVO, hSV, hKV⟩ :=
    HarmonicBalls.exists_bounded_open_containing_closure_and_compact hSb hO hSO hK hKO
  have hzV : z ∈ V := hSV (subset_closure hz)
  have hSmeas : MeasurableSet S := hS.measurableSet
  have hS' : S ⊆ V := fun x hx => hSV (subset_closure hx)
  have hint₁ : ∀ x ∈ S, Integrable (greenFunction V x) ν₁ := fun x hx =>
    HarmonicBalls.integrable_greenFunction_of_source_null_on_open hV hS hS' hx hK hKV hν₁ h₁K hν₁S
  have hatom₁ : ∀ x ∈ S, ν₁ {x} = 0 := fun x hx => measure_mono_null (singleton_subset_iff.2 hx) hν₁S
  obtain ⟨a₁, ha₁, hid₁⟩ := hLoc O V ν₁ K hO hV hVb hVO hK hKV hν₁ h₁K
  obtain ⟨a₂, ha₂, hid₂⟩ := hLoc O V ν₂ K hO hV hVb hVO hK hKV hν₂ h₂K
  have hiV : Integrable (greenFunction V z) ν₂ := ((hid₂ z hzV hz₂).1).mp hi₂
  have hfin := hFat V S z m ν₂ K hV hVb hS hSb hz hSV hK hKV hν₂ h₂K hz₂ hiV hmtop hJ
  refine HarmonicBalls.bounded_representative_of_source_corrections (μ := m) (ν₁ := ν₁) (ν₂ := ν₂)
    (Λ := S) (O := O) (V := V) (K := K) (z := z) (q := q) (a := a₁) (b := a₂)
    hV hVb hVO hSV hK hKV hν₁ hν₂ h₁K h₂K hν₁S hq ha₁ ha₂ hz₂ hiV ?_ ?_ ?_ ?_
  · exact (hid₁ z hzV (hatom₁ z hz)).2 (hint₁ z hz)
  · exact (hid₂ z hzV hz₂).2 hiV
  · filter_upwards [ae_restrict_mem hSmeas] with x hxS
    exact (hid₁ x (hS' hxS) (hatom₁ x hxS)).2 (hint₁ x hxS)
  · filter_upwards [ae_restrict_mem hSmeas, hfin] with x hxS hx
    exact (hid₂ x (hS' hxS) hx.1).2 hx.2

/-- **The sub-mean inequality on the bounded test class of the dilated set (steps3:340-368).** For a subharmonic ball
`Λ` of `μ` at `0` and `a, c > 0`, every `f ∈ T_b(a⁻¹ Λ, 0)` satisfies the sub-mean inequality for `μ_a = scaledMeasure μ a c`
on `a⁻¹ Λ`. Here `F(y) = f(y / a)` lies in `T_b(Λ, 0)` (`boundedSubharmonicBallTestClass_rescaled`), and the scaled
mean-value transfer is `hasSubMeanValueProperty_rescaledMeasure`. -/
theorem hasSubMeanValueProperty_scaled_boundedTestClass {μ : Measure ℂ} {Λ : Set ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : IsSubharmonicBall μ Λ 0) {f : ℂ → ℝ}
    (hf : f ∈ boundedSubharmonicBallTestClass ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0) :
    HasSubMeanValueProperty (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0 f := by
  obtain ⟨-, -, -, -, hmv⟩ := h
  rw [scaledMeasure_eq_rescaledMeasure μ hc]
  have hg := boundedSubharmonicBallTestClass_rescaled ha hf
  have hH := hmv _ (boundedSubharmonicBallTestClass_subset Λ 0 hg)
  have hT := hasSubMeanValueProperty_rescaledMeasure ha.ne' hc hH
  simpa only [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.2 ha.ne')] using hT

/-- **The repaired `ScaledBoundedRepresentativesStep`, from the bounded representative lemma.** For a bounded subharmonic
ball `Λ` of `μ` at `0`, the set `S = a⁻¹ Λ` is open, bounded and contains `0`, and `μ_a(S) = c⁻¹ μ(Λ)` lies in `(0, ∞)`
(`rescaledMeasure_preimage`). The sub-mean inequality on `T_b(S, 0)` is
`hasSubMeanValueProperty_scaled_boundedTestClass`. The named representative lemma `hJ` then gives the representatives.
The input is the representative lemma itself, not the repaired Step. -/
theorem scaledBoundedRepresentativesStep_of_jensen (hJ : BoundedJensenRepresentativesStep) :
    ScaledBoundedRepresentativesStep := by
  intro μ Λ a c ha hc hΛ hbd
  have hR0 : a ≠ 0 := ha.ne'
  have hRc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  refine hJ (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0
    (hΛ.1.preimage (continuous_const.mul continuous_id)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨R, hR⟩ := hbd.subset_closedBall (0 : ℂ)
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R / a)).subset ?_
    intro x hx
    have hΛx : (a : ℂ) * x ∈ Λ := hx
    have hx' : (a : ℂ) * x ∈ closedBall (0 : ℂ) R := hR hΛx
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le] at hx'
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ ha]
    linarith [mul_comm ‖x‖ a]
  · show (a : ℂ) * 0 ∈ Λ
    rw [mul_zero]
    exact hΛ.2.1
  · rw [scaledMeasure_eq_rescaledMeasure μ hc, rescaledMeasure_preimage μ hR0 c Λ]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne' hΛ.2.2.1.ne'
  · rw [scaledMeasure_eq_rescaledMeasure μ hc, rescaledMeasure_preimage μ hR0 c Λ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ.2.2.2.1
  · intro f hf
    exact hasSubMeanValueProperty_scaled_boundedTestClass ha hc hΛ hf

/-- **The repaired `ScaledBoundedRepresentativesStep`, from the two named analytic inputs of the representative lemma.** -/
theorem scaledBoundedRepresentativesStep_of_localization_and_fatou (hLoc : JensenGreenLocalizationStmt)
    (hFat : JensenFatouFinitenessStmt) : ScaledBoundedRepresentativesStep :=
  scaledBoundedRepresentativesStep_of_jensen (bounded_jensen_representatives_of_localization_and_fatou hLoc hFat)

/-- **Named internal Step: superharmonic smoothing of the classical Green potential (steps3:247-262).** Let `V` be bounded
open, `S ∋ z` bounded open with `closure S ⊆ V`, and `ν` a finite measure carried by a compact `K ⊆ V`, with `ν {z} = 0`
and `G_V(z, ·) ∈ L¹(ν)`. There are smooth compactly supported `F n` with `0 ≤ Δ (F n)` on `S` (so that `-F n` is
superharmonic there), `F n ≤ c` on `S`, `F n z` convergent, and the classical potential `x ↦ ∫⁻ G_V(x, ·) dν` is bounded by
`liminf (-F n x + c)` on `S`. Written proof: steps3:247-262, the radial convolution of the superharmonic potential (pointwise
convergence from the circle-mean inequality and lower semicontinuity) with a cut-off `χ`. -/
def JensenSmoothingStmt : Prop :=
  ∀ (V S : Set ℂ) (z : ℂ) (ν : Measure ℂ) (K : Set ℂ),
    IsOpen V → Bornology.IsBounded V → IsOpen S → Bornology.IsBounded S → z ∈ S → closure S ⊆ V →
    IsCompact K → K ⊆ V → IsFiniteMeasure ν → ν Kᶜ = 0 → ν {z} = 0 → Integrable (greenFunction V z) ν →
    ∃ (F : ℕ → ℂ → ℝ) (c L : ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n)) ∧ (∀ n, HasCompactSupport (F n)) ∧
      (∀ n, ∀ x ∈ S, 0 ≤ Laplacian.laplacian (F n) x) ∧
      (∀ n, ∀ x ∈ S, F n x ≤ c) ∧
      Tendsto (fun n => F n z) atTop (nhds L) ∧
      (∀ x ∈ S, (∫⁻ y, greenKernelExtended V x y ∂ν) ≤
        liminf (fun n => ENNReal.ofReal (-F n x + c)) atTop)

/-- **The Jensen-Fatou finiteness, from the smoothing input.** The smooth functions `F n` lie in `T_b(S, z)`
(`mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport`). The sub-mean inequality gives
`∫_S (-F n) dm ≤ m(S) (-F n z)`. Fatou's lemma (`jensen_fatou_of_common_lower_bound`) gives finiteness `m`-a.e. on `S`, and
finiteness of the classical potential gives `ν {x} = 0` and integrability (`greenPotential_eq_toReal_of_classical_lt_top`). -/
theorem jensenFatouFinitenessStmt_of_smoothing (hSm : JensenSmoothingStmt) : JensenFatouFinitenessStmt := by
  intro V S z m ν K hV hVb hS hSb hz hSV hK hKV hνfin hνK hνz hi hmS hJ
  have : IsFiniteMeasure ν := hνfin
  obtain ⟨F, c, L, hFs, hFc, hFlap, hFle, hFlim, hliminf⟩ :=
    hSm V S z ν K hV hVb hS hSb hz hSV hK hKV hνfin hνK hνz hi
  have hSmeas : MeasurableSet S := hS.measurableSet
  have hcont : ∀ n, Continuous (F n) := fun n => (hFs n).continuous
  have hmem : ∀ n, F n ∈ boundedSubharmonicBallTestClass S z := fun n =>
    HarmonicBalls.mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport S z hS hSb hz (F n)
      (hFs n) (hFc n) (hFlap n)
  have hsub : ∀ n, ∫ x in S, -F n x ∂m ≤ m.real S * -F n z := by
    intro n
    have h := (hJ (F n) (hmem n)).2
    calc ∫ x in S, -F n x ∂m = -∫ x in S, F n x ∂m := by rw [integral_neg]
      _ ≤ -(F n z * m.real S) := neg_le_neg h
      _ = m.real S * -F n z := by ring
  have hint : ∀ n, IntegrableOn (fun x => -F n x) S m := by
    intro n
    obtain ⟨C, hC⟩ := hSb.isCompact_closure.exists_bound_of_continuousOn (hcont n).continuousOn
    refine Measure.integrableOn_of_bounded (M := C) (ne_top_of_lt hmS) (hcont n).neg.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSmeas] with x hx
    rw [norm_neg]
    exact hC x (subset_closure hx)
  have hlb : ∀ n, ∀ x ∈ S, -c ≤ -F n x := fun n x hx => by
    have := hFle n x hx
    linarith
  have hmeasK : Measurable (fun x => ∫⁻ y, greenKernelExtended V x y ∂ν) := by
    have hk : Measurable (fun p : ℂ × ℂ => greenKernelExtended V p.1 p.2) := by
      unfold greenKernelExtended
      exact Measurable.ite (isClosed_eq continuous_snd continuous_fst).measurableSet measurable_const
        (ENNReal.measurable_ofReal.comp (measurable_greenFunction_uncurry hV))
    exact hk.lintegral_prod_right'
  have hfat := HarmonicBalls.BoundedJensenFatou.jensen_fatou_of_common_lower_bound (μ := m)
    (u := fun n x => -F n x) hSmeas (ne_top_of_lt hmS) hz hmeasK.aemeasurable
    (fun n => (hcont n).neg.measurable) hint hlb hsub hFlim.neg hliminf
  filter_upwards [hfat.2.1] with x hx
  obtain ⟨hatom, hintV, -⟩ := HarmonicBalls.BoundedJensenFatou.greenPotential_eq_toReal_of_classical_lt_top hV hVb hx
  exact ⟨hatom, hintV⟩

/-- **The representative lemma `BoundedJensenRepresentativesStep`, from the localization and smoothing inputs.** -/
theorem bounded_jensen_representatives_of_localization_and_smoothing (hLoc : JensenGreenLocalizationStmt)
    (hSm : JensenSmoothingStmt) : BoundedJensenRepresentativesStep :=
  bounded_jensen_representatives_of_localization_and_fatou hLoc (jensenFatouFinitenessStmt_of_smoothing hSm)

/-- **The repaired `ScaledBoundedRepresentativesStep`, from the localization and smoothing inputs.** -/
theorem scaledBoundedRepresentativesStep_of_localization_and_smoothing (hLoc : JensenGreenLocalizationStmt)
    (hSm : JensenSmoothingStmt) : ScaledBoundedRepresentativesStep :=
  scaledBoundedRepresentativesStep_of_jensen (bounded_jensen_representatives_of_localization_and_smoothing hLoc hSm)

end MatedCRT
