import MatedCRT.FirstPass.Derived.ZeroConeConfigCovarianceProof
import LatticeProb.LQG.MassReparamBorel
import LatticeProb.Prob.FiniteOnCompactsPart
import LatticeProb.Prob.KernelCurveImage
import LatticeProb.Analysis.VagueLimitCompactMass

/-!
# The quantum-time curve of the zero-cone field with the LQG coordinate change

The step `ZeroConeQuantumCurveCovariance` of the proof of Lemma 3.5 of Gwynne–Miller–Sheffield (arXiv:1705.11161)
asks for one Borel map `qc` from (field, Lebesgue-parametrized curve) to curves which returns the curve `η₀`
parametrized by the quantum area of the `0`-quantum cone, and which is covariant under every positive similarity
`ψ(w) = C w + z` at once: `qc(h(C · + z) + Q log C, ψ⁻¹ ∘ e re-rooted at z) = ψ⁻¹ ∘ qc(h, e)(· + τ)`.

Following the written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(d) One area clock for every similarity"
(lines 46-51), `qc(h, e)` is the curve `e` run with the inverse of its signed area clock `t ↦ ±μ_h(e[0, t])`
(`areaClockCurve`), where `h ↦ μ_h` is a Borel field-to-area map with the simultaneous coordinate change
(`ZeroConeAreaCoordinateChange`, a named input from Sheffield–Wang, arXiv:1605.06171). The clock is tested at
rational times (`IsGoodMassClock`): when it is strictly increasing, unbounded both ways, has dense values and vanishes
at `0`, its inverse is an increasing homeomorphism of `ℝ` (`exists_orderIso_massClockInv`), and the reparametrized
curve is continuous; otherwise `qc(h, e) = e`. The new clock of the transformed pair is the old clock from the first
visit `t_z` of `z`, rescaled, so the covariance holds with `τ = A(t_z)` (`massReparamCurve_similarity`). These
identities hold together on a measurable good set of pairs (`AreaClockGood`) which contains `(h₀, ηL)` almost surely
by the area parametrization of the coupling, and the independence of `h₀` and `ηL` gives the two nested
almost-everywhere quantifiers.

## Main declarations

* `IsGoodMassClock`, `exists_orderIso_massClockInv`, `massReparamCurve`, `measurable_massReparamCurve`.
* `massReparamCurve_similarity`: the deterministic covariance of the area clock under a positive similarity.
* `ZeroConeAreaCoordinateChange`: the named input (Sheffield–Wang, Theorems 1.1, 1.2 and 1.4).
* `zeroConeQuantumCurveCovariance`: `ZeroConeQuantumCurveCovariance D hγ` from `ZeroConeAreaCoordinateChange`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open LatticeProb.LQG (massClock massClockInv massReparam massReparam_eq_of_massParam
  massClock_eq_symm_of_massParam measurable_massClock measurable_massReparam)
open scoped NNReal ENNReal

/-! ### Good mass clocks and their inverses -/

section Clock

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- **A good mass clock.** The signed mass clock `u ↦ ±μ(L[0, u])` of the curve `L`, read at rational times, is
strictly increasing, unbounded above and below, has dense values and vanishes at `0`. -/
def IsGoodMassClock (μ : Measure E) (L : ℝ → E) : Prop :=
  (∀ q q' : ℚ, q < q' → massClock μ L q < massClock μ L q') ∧
    (∀ r : ℚ, ∃ q : ℚ, (r : ℝ) < massClock μ L q) ∧
    (∀ r : ℚ, ∃ q : ℚ, massClock μ L q < r) ∧
    (∀ r r' : ℚ, r < r' → ∃ q : ℚ, (r : ℝ) < massClock μ L q ∧ massClock μ L q < r') ∧
    massClock μ L 0 = 0

omit [TopologicalSpace E] in
/-- **The inverse of a good mass clock is an increasing homeomorphism of `ℝ` fixing `0`.** -/
theorem exists_orderIso_massClockInv {μ : Measure E} {L : ℝ → E} (hG : IsGoodMassClock μ L) :
    ∃ v : ℝ ≃o ℝ, v 0 = 0 ∧ ∀ t, massClockInv μ L t = v t := by
  obtain ⟨hmono, habove, hbelow, hdense, hzero⟩ := hG
  -- the clock reflects the order of rational times
  have hrefl : ∀ q q' : ℚ, massClock μ L q < massClock μ L q' → q < q' := by
    intro q q' h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h1 | h1
    · exact lt_asymm h (hmono _ _ h1)
    · rw [h1] at h
      exact lt_irrefl _ h
  have habove' : ∀ t : ℝ, ∃ q : ℚ, t < massClock μ L q := by
    intro t
    obtain ⟨r, hr⟩ := exists_rat_gt t
    obtain ⟨q, hq⟩ := habove r
    exact ⟨q, hr.trans hq⟩
  have hbelow' : ∀ t : ℝ, ∃ q : ℚ, massClock μ L q < t := by
    intro t
    obtain ⟨r, hr⟩ := exists_rat_lt t
    obtain ⟨q, hq⟩ := hbelow r
    exact ⟨q, hq.trans hr⟩
  have hdense' : ∀ x y : ℝ, x < y → ∃ q : ℚ, x < massClock μ L q ∧ massClock μ L q < y := by
    intro x y hxy
    obtain ⟨r, hxr, hry⟩ := exists_rat_btwn hxy
    obtain ⟨r', hrr', hr'y⟩ := exists_rat_btwn hry
    obtain ⟨q, hq1, hq2⟩ := hdense r r' (by exact_mod_cast hrr')
    exact ⟨q, hxr.trans hq1, hq2.trans hr'y⟩
  -- the infimum defining the inverse clock
  have hup : ∀ (t : ℝ) (q : ℚ), t < massClock μ L q →
      (⨅ q' : ℚ, if t < massClock μ L q' then ((q' : ℝ) : EReal) else ⊤) ≤ ((q : ℝ) : EReal) := by
    intro t q h
    exact (iInf_le _ q).trans (by simp [h])
  have hlow : ∀ (t : ℝ) (q : ℚ), massClock μ L q ≤ t →
      ((q : ℝ) : EReal) ≤ ⨅ q' : ℚ, if t < massClock μ L q' then ((q' : ℝ) : EReal) else ⊤ := by
    intro t q h
    refine le_iInf fun q' => ?_
    by_cases h' : t < massClock μ L q'
    · have hqq' : q < q' := hrefl q q' (h.trans_lt h')
      simp only [h', ↓reduceIte]
      exact EReal.coe_le_coe_iff.2 (by exact_mod_cast hqq'.le)
    · simp only [h', ↓reduceIte, le_top]
  have hcoe : ∀ t, ((massClockInv μ L t : ℝ) : EReal) =
      ⨅ q : ℚ, if t < massClock μ L q then ((q : ℝ) : EReal) else ⊤ := by
    intro t
    obtain ⟨q, hq⟩ := habove' t
    obtain ⟨q₀, hq₀⟩ := hbelow' t
    unfold massClockInv
    exact EReal.coe_toReal ((hup t q hq).trans_lt (EReal.coe_lt_top _)).ne
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow t q₀ hq₀.le))
  have hP1 : ∀ (t : ℝ) (q : ℚ), t < massClock μ L q → massClockInv μ L t ≤ q := by
    intro t q h
    have h1 := hup t q h
    rw [← hcoe t] at h1
    exact EReal.coe_le_coe_iff.1 h1
  have hP2 : ∀ (t : ℝ) (q : ℚ), massClock μ L q ≤ t → (q : ℝ) ≤ massClockInv μ L t := by
    intro t q h
    have h1 := hlow t q h
    rw [← hcoe t] at h1
    exact EReal.coe_le_coe_iff.1 h1
  -- strict monotonicity
  have hsm : StrictMono (massClockInv μ L) := by
    intro t t' htt'
    obtain ⟨q₁, hq₁, hq₁'⟩ := hdense' t t' htt'
    obtain ⟨q₂, hq₂, hq₂'⟩ := hdense' _ _ hq₁'
    have h12 : (q₁ : ℝ) < q₂ := by exact_mod_cast hrefl q₁ q₂ hq₂
    exact ((hP1 t q₁ hq₁).trans_lt h12).trans_le (hP2 t' q₂ hq₂'.le)
  -- surjectivity
  have hsurj : Function.Surjective (massClockInv μ L) := by
    intro x
    obtain ⟨q₁, hq₁⟩ := exists_rat_gt x
    obtain ⟨r₀, hr₀⟩ := exists_rat_lt x
    have hne : ((fun q : ℚ => massClock μ L q) '' {q : ℚ | (q : ℝ) < x}).Nonempty := ⟨_, r₀, hr₀, rfl⟩
    have hbdd : BddAbove ((fun q : ℚ => massClock μ L q) '' {q : ℚ | (q : ℝ) < x}) := by
      refine ⟨massClock μ L q₁, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact (hmono q q₁ (by exact_mod_cast ((show (q : ℝ) < x from hq).trans hq₁))).le
    refine ⟨sSup ((fun q : ℚ => massClock μ L q) '' {q : ℚ | (q : ℝ) < x}), le_antisymm ?_ ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q hq => ?_
      obtain ⟨q₀, hxq₀, hq₀q⟩ := exists_rat_btwn hq
      refine hP1 _ q ((csSup_le hne ?_).trans_lt (hmono q₀ q (by exact_mod_cast hq₀q)))
      rintro _ ⟨r, hr, rfl⟩
      exact (hmono r q₀ (by exact_mod_cast ((show (r : ℝ) < x from hr).trans hxq₀))).le
    · exact le_of_forall_rat_lt_imp_le fun q hq => hP2 _ q (le_csSup hbdd ⟨q, hq, rfl⟩)
  refine ⟨StrictMono.orderIsoOfSurjective (massClockInv μ L) hsm hsurj, ?_, fun t => rfl⟩
  show massClockInv μ L 0 = 0
  apply le_antisymm
  · refine le_of_forall_lt_rat_imp_le fun q hq => hP1 0 q ?_
    have h0q := hmono 0 q (by exact_mod_cast hq)
    rwa [Rat.cast_zero, hzero] at h0q
  · refine le_of_forall_rat_lt_imp_le fun q hq => hP2 0 q ?_
    have hq0 := hmono q 0 (by exact_mod_cast hq)
    rw [Rat.cast_zero, hzero] at hq0
    exact hq0.le

omit [TopologicalSpace E] in
/-- The clock of a curve parametrized by mass through an increasing homeomorphism fixing `0` is good. -/
theorem isGoodMassClock_of_massParam {μ : Measure E} {L η : ℝ → E} (v : ℝ ≃o ℝ) (hv : v 0 = 0)
    (hη : ∀ t, η t = L (v t)) (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    IsGoodMassClock μ L := by
  have hc : ∀ u, massClock μ L u = v.symm u := massClock_eq_symm_of_massParam μ L η v hv hη harea
  have hs0 : v.symm 0 = 0 := by
    rw [OrderIso.symm_apply_eq]
    exact hv.symm
  refine ⟨fun q q' h => ?_, fun r => ?_, fun r => ?_, fun r r' h => ?_, ?_⟩
  · rw [hc, hc]
    exact v.symm.strictMono (by exact_mod_cast h)
  · obtain ⟨q, hq⟩ := exists_rat_gt (v r)
    refine ⟨q, ?_⟩
    rw [hc]
    exact (v.symm_apply_apply (r : ℝ)).symm.trans_lt (v.symm.strictMono hq)
  · obtain ⟨q, hq⟩ := exists_rat_lt (v r)
    refine ⟨q, ?_⟩
    rw [hc]
    exact (v.symm.strictMono hq).trans_eq (v.symm_apply_apply (r : ℝ))
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (v.strictMono (show (r : ℝ) < r' by exact_mod_cast h))
    refine ⟨q, ?_, ?_⟩
    · rw [hc]
      exact (v.symm_apply_apply (r : ℝ)).symm.trans_lt (v.symm.strictMono hq1)
    · rw [hc]
      exact (v.symm.strictMono hq2).trans_eq (v.symm_apply_apply (r' : ℝ))
  · rw [hc, hs0]

/-- The mass reparametrization of a continuous curve with a good clock is continuous. -/
theorem continuous_massReparam_of_good {μ : Measure E} {L : C(ℝ, E)} (h : IsGoodMassClock μ L) :
    Continuous fun t => massReparam μ L t := by
  obtain ⟨v, -, hv⟩ := exists_orderIso_massClockInv h
  have e : (fun t => massReparam μ L t) = fun t => L (v t) := funext fun t => by
    show L (massClockInv μ L t) = L (v t)
    rw [hv]
  rw [e]
  exact L.continuous.comp v.continuous

open Classical in
/-- **The mass reparametrization as a continuous curve**: `L ∘ massClockInv μ L` when the clock of `L` is good,
and `L` itself otherwise. -/
def massReparamCurve (μ : Measure E) (L : C(ℝ, E)) : C(ℝ, E) :=
  if h : IsGoodMassClock μ L then ⟨fun t => massReparam μ L t, continuous_massReparam_of_good h⟩ else L

theorem massReparamCurve_of_good {μ : Measure E} {L : C(ℝ, E)} (h : IsGoodMassClock μ L) :
    massReparamCurve μ L = ⟨fun t => massReparam μ L t, continuous_massReparam_of_good h⟩ := by
  simp only [massReparamCurve, h, ↓reduceDIte]

theorem massReparamCurve_of_not_good {μ : Measure E} {L : C(ℝ, E)} (h : ¬IsGoodMassClock μ L) :
    massReparamCurve μ L = L := by
  simp only [massReparamCurve, h, ↓reduceDIte]

theorem massReparamCurve_apply_of_good {μ : Measure E} {L : C(ℝ, E)} (h : IsGoodMassClock μ L) (t : ℝ) :
    massReparamCurve μ L t = massReparam μ L t :=
  congrArg (fun F : C(ℝ, E) => F t) (massReparamCurve_of_good h)

end Clock

/-! ### Measurability -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pairs with a good mass clock form a measurable set. -/
theorem measurableSet_isGoodMassClock {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → C(ℝ, ℂ)} (hL : Measurable L) :
    MeasurableSet {ω | IsGoodMassClock (μ ω) (L ω)} := by
  have hLm : ∀ t, Measurable fun ω => L ω t := fun t => (continuous_eval_const t).measurable.comp hL
  have hclock : ∀ u : ℝ, Measurable fun ω => massClock (μ ω) (L ω) u :=
    measurable_massClock hμ hfin (fun ω => (L ω).continuous) hLm
  have e : {ω | IsGoodMassClock (μ ω) (L ω)} =
      (⋂ q : ℚ, ⋂ q' : ℚ, ⋂ (_ : q < q'), {ω | massClock (μ ω) (L ω) q < massClock (μ ω) (L ω) q'}) ∩
      ((⋂ r : ℚ, ⋃ q : ℚ, {ω | (r : ℝ) < massClock (μ ω) (L ω) q}) ∩
      ((⋂ r : ℚ, ⋃ q : ℚ, {ω | massClock (μ ω) (L ω) q < r}) ∩
      ((⋂ r : ℚ, ⋂ r' : ℚ, ⋂ (_ : r < r'), ⋃ q : ℚ,
        {ω | (r : ℝ) < massClock (μ ω) (L ω) q ∧ massClock (μ ω) (L ω) q < r'}) ∩
      {ω | massClock (μ ω) (L ω) 0 = 0}))) := by
    ext ω
    simp only [IsGoodMassClock, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [e]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hclock q) (hclock q')
  · exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun q =>
      measurableSet_lt measurable_const (hclock q)
  · exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun q =>
      measurableSet_lt (hclock q) measurable_const
  · exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun q => (measurableSet_lt measurable_const (hclock q)).inter
        (measurableSet_lt (hclock q) measurable_const)
  · exact hclock 0 (measurableSet_singleton 0)

/-- **The mass reparametrization is a measurable map into curves**, for a measurable family of measures finite on
compact sets and a measurable family of continuous curves. -/
theorem measurable_massReparamCurve {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → C(ℝ, ℂ)} (hL : Measurable L) :
    Measurable fun ω => massReparamCurve (μ ω) (L ω) := by
  classical
  have hLm : ∀ t, Measurable fun ω => L ω t := fun t => (continuous_eval_const t).measurable.comp hL
  have hG := measurableSet_isGoodMassClock hμ hfin hL
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have e : (fun ω => massReparamCurve (μ ω) (L ω) t) =
      fun ω => if IsGoodMassClock (μ ω) (L ω) then massReparam (μ ω) (L ω) t else L ω t := by
    funext ω
    by_cases h : IsGoodMassClock (μ ω) (L ω)
    · rw [massReparamCurve_apply_of_good h]
      simp only [h, ↓reduceIte]
    · rw [massReparamCurve_of_not_good h]
      simp only [h, ↓reduceIte]
  rw [e]
  exact Measurable.ite hG (measurable_massReparam hμ hfin (fun ω => (L ω).continuous) hLm t) (hLm t)

end Measurability

/-! ### The covariance of the area clock under a positive similarity -/

section Similarity

/-- The inverse `w ↦ C⁻¹ (w − z)` of the positive similarity `ψ(w) = C w + z`, as a homeomorphism of `ℂ`. -/
def similarityInvHomeomorph (C : ℝ) (z : ℂ) (hC : C ≠ 0) : ℂ ≃ₜ ℂ where
  toFun w := ((C⁻¹ : ℝ) : ℂ) * (w - z)
  invFun w := (C : ℂ) * w + z
  left_inv w := by
    have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hC
    show (C : ℂ) * (((C⁻¹ : ℝ) : ℂ) * (w - z)) + z = w
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hC', one_mul, sub_add_cancel]
  right_inv w := by
    have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hC
    show ((C⁻¹ : ℝ) : ℂ) * ((C : ℂ) * w + z - z) = w
    rw [Complex.ofReal_inv, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hC', one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The image of a measure finite on compact sets by a homeomorphism of `ℂ` is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_map_homeomorph {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (f : ℂ ≃ₜ ℂ) :
    IsFiniteMeasureOnCompacts (μ.map f) :=
  ⟨fun K hK => by
    rw [Measure.map_apply f.measurable hK.measurableSet]
    exact (f.isCompact_preimage.2 hK).measure_lt_top⟩

/-- A measure on `ℂ` finite on the closed balls `B̄(0, n)` is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_of_forall_closedBall {μ : Measure ℂ}
    (h : ∀ n : ℕ, μ (Metric.closedBall 0 n) < ⊤) : IsFiniteMeasureOnCompacts μ :=
  ⟨fun K hK => by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact (measure_mono (hr.trans (Metric.closedBall_subset_closedBall hn))).trans_lt (h n)⟩

/-- **The area clock under a positive similarity** (written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, line 50).
Let the mass clock of the continuous curve `e` under `μ` be good, and let `μ` parametrize the reparametrized curve
`w = massReparamCurve μ e` by mass at rational times. For `ψ(w) = C w + z`, `C > 0`, the curve `ψ⁻¹ ∘ e` re-rooted at
the first visit `t_z` of `z` and run at speed `C²`, reparametrized by the image measure `μ ∘ ψ`, is
`ψ⁻¹ ∘ w(· + τ)` with `τ = A(t_z)`: its clock is the clock of `e` from time `t_z`, rescaled. -/
theorem massReparamCurve_similarity {μ : Measure ℂ} {e : C(ℝ, ℂ)} (hG : IsGoodMassClock μ e)
    (harea : ∀ s t : ℚ, s ≤ t →
      μ (massReparamCurve μ e '' Icc (s : ℝ) t) = ENNReal.ofReal ((t : ℝ) - s))
    {C : ℝ} (hC : 0 < C) (z : ℂ) :
    ∃ τ : ℝ, massReparamCurve (μ.map (similarityInvHomeomorph C z hC.ne')) (affineReroot z C 0 e) =
      curveSimilarityPullback C z (curveTimeTranslate τ (massReparamCurve μ e)) := by
  obtain ⟨v, hv0, hv⟩ := exists_orderIso_massClockInv hG
  have hwv : ∀ t, massReparamCurve μ e t = e (v t) := by
    intro t
    rw [massReparamCurve_apply_of_good hG]
    show e (massClockInv μ e t) = e (v t)
    rw [hv]
  have hreal : ∀ s t : ℝ, s ≤ t → μ (massReparamCurve μ e '' Icc s t) = ENNReal.ofReal (t - s) :=
    fun s t hst => LatticeProb.VagueLimit.measure_image_Icc_eq_ofReal_of_rat harea hst
  obtain ⟨tz, htz⟩ : ∃ tz : ℝ, tz = firstHit e z := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = v.symm tz := ⟨_, rfl⟩
  refine ⟨τ, ?_⟩
  have hvτ : v τ = tz := by rw [hτ, OrderIso.apply_symm_apply]
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  -- the time change of the transformed pair
  let v' : ℝ ≃o ℝ := ((OrderIso.addRight τ).trans v).trans
    ((OrderIso.addRight (-tz)).trans (OrderIso.mulLeft₀ (C ^ 2)⁻¹ (inv_pos.2 hC2)))
  have hv'_apply : ∀ s, v' s = (C ^ 2)⁻¹ * (v (s + τ) + -tz) := fun s => rfl
  have hv'0 : v' 0 = 0 := by rw [hv'_apply, zero_add, hvτ, add_neg_cancel, mul_zero]
  have hrr : ∀ s, tz + C ^ 2 * v' s = v (s + τ) := by
    intro s
    rw [hv'_apply, ← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul]
    ring
  have hη : ∀ s, curveSimilarityPullback C z (curveTimeTranslate τ (massReparamCurve μ e)) s =
      affineReroot z C 0 e (v' s) := by
    intro s
    show ((C⁻¹ : ℝ) : ℂ) * (massReparamCurve μ e (s + τ) - z) =
      (((C : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))⁻¹) * (e (firstHit e z + C ^ 2 * v' s) - z)
    rw [← htz, hrr, hwv, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_inv]
  have harea' : ∀ s t : ℝ, s ≤ t → (μ.map (similarityInvHomeomorph C z hC.ne'))
      (curveSimilarityPullback C z (curveTimeTranslate τ (massReparamCurve μ e)) '' Icc s t) =
        ENNReal.ofReal (t - s) := by
    intro s t hst
    have himg : ⇑(curveSimilarityPullback C z (curveTimeTranslate τ (massReparamCurve μ e))) '' Icc s t =
        similarityInvHomeomorph C z hC.ne' '' (massReparamCurve μ e '' Icc (s + τ) (t + τ)) := by
      rw [← Set.image_add_const_Icc, Set.image_image, Set.image_image]
      rfl
    have hK : IsCompact (massReparamCurve μ e '' Icc (s + τ) (t + τ)) :=
      isCompact_Icc.image (massReparamCurve μ e).continuous
    rw [himg, Measure.map_apply (similarityInvHomeomorph C z hC.ne').measurable
      (hK.image (similarityInvHomeomorph C z hC.ne').continuous).isClosed.measurableSet,
      Homeomorph.preimage_image, hreal _ _ (by linarith)]
    congr 1
    ring
  have hmp := massReparam_eq_of_massParam (μ.map (similarityInvHomeomorph C z hC.ne'))
    (affineReroot z C 0 e) (curveSimilarityPullback C z (curveTimeTranslate τ (massReparamCurve μ e)))
    v' hv'0 hη harea'
  have hG' := isGoodMassClock_of_massParam v' hv'0 hη harea'
  ext s
  rw [massReparamCurve_apply_of_good hG', hmp]

end Similarity

/-! ### The area clock of the zero-cone field -/

section ZeroCone

/-- The curve `e` run with the inverse of its area clock for the area measure `M h` of the field `h` (made finite on
compact sets). -/
def areaClockCurve (M : Field → Measure ℂ) (p : Field × C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  massReparamCurve (LatticeProb.finiteOnCompactsPart (M p.1)) p.2

theorem measurable_areaClockCurve {M : Field → Measure ℂ} (hM : Measurable M) :
    Measurable (areaClockCurve M) := by
  show Measurable fun p : Field × C(ℝ, ℂ) =>
    massReparamCurve (LatticeProb.finiteOnCompactsPart (M p.1)) p.2
  exact measurable_massReparamCurve (μ := fun p : Field × C(ℝ, ℂ) => LatticeProb.finiteOnCompactsPart (M p.1))
    ((LatticeProb.measurable_finiteOnCompactsPart_comp hM).comp measurable_fst) (fun _ => inferInstance)
    measurable_snd

/-- **The good pairs** `(h, e)`: the area measure `M h` is finite on compact sets, the area clock of `e` is good,
and the reparametrized curve is parametrized by area at rational times. -/
def AreaClockGood (M : Field → Measure ℂ) (p : Field × C(ℝ, ℂ)) : Prop :=
  (∀ n : ℕ, M p.1 (Metric.closedBall 0 n) < ⊤) ∧
    IsGoodMassClock (LatticeProb.finiteOnCompactsPart (M p.1)) p.2 ∧
    ∀ s t : ℚ, s ≤ t → LatticeProb.finiteOnCompactsPart (M p.1) (areaClockCurve M p '' Icc (s : ℝ) t) =
      ENNReal.ofReal ((t : ℝ) - s)

theorem measurableSet_areaClockGood {M : Field → Measure ℂ} (hM : Measurable M) :
    MeasurableSet {p : Field × C(ℝ, ℂ) | AreaClockGood M p} := by
  have hμ : Measurable fun p : Field × C(ℝ, ℂ) => LatticeProb.finiteOnCompactsPart (M p.1) :=
    (LatticeProb.measurable_finiteOnCompactsPart_comp hM).comp measurable_fst
  have hfin : ∀ p : Field × C(ℝ, ℂ), IsFiniteMeasureOnCompacts (LatticeProb.finiteOnCompactsPart (M p.1)) :=
    fun _ => inferInstance
  have hq := measurable_areaClockCurve hM
  have hev : ∀ t : ℝ, Measurable fun p : Field × C(ℝ, ℂ) => areaClockCurve M p t :=
    fun t => (continuous_eval_const t).measurable.comp hq
  have e : {p : Field × C(ℝ, ℂ) | AreaClockGood M p} =
      (⋂ n : ℕ, {p : Field × C(ℝ, ℂ) | M p.1 (Metric.closedBall 0 n) < ⊤}) ∩
      ({p : Field × C(ℝ, ℂ) | IsGoodMassClock (LatticeProb.finiteOnCompactsPart (M p.1)) p.2} ∩
      ⋂ s : ℚ, ⋂ t : ℚ, ⋂ (_ : s ≤ t), {p : Field × C(ℝ, ℂ) | LatticeProb.finiteOnCompactsPart (M p.1)
        (areaClockCurve M p '' Icc (s : ℝ) t) = ENNReal.ofReal ((t : ℝ) - s)}) := by
    ext p
    simp only [AreaClockGood, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => ?_) (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_lt ((Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp
      (hM.comp measurable_fst)) measurable_const
  · exact measurableSet_isGoodMassClock hμ hfin measurable_snd
  · refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun t => MeasurableSet.iInter fun hst => ?_
    exact (LatticeProb.measurable_measure_image_Icc hμ hfin (fun p => (areaClockCurve M p).continuous) hev
      (by exact_mod_cast hst)) (measurableSet_singleton _)

/-- **Pathwise recovery.** If the measure `M h` is finite on compact sets and parametrizes `η = L ∘ φ` by area, for an
increasing homeomorphism `φ` of `ℝ` fixing `0`, then `(h, L)` is a good pair and the area clock curve is `η`. -/
theorem areaClockGood_of_areaParam {M : Field → Measure ℂ} {h : Field} {L η : C(ℝ, ℂ)}
    (hfin : ∀ K : Set ℂ, IsCompact K → M h K < ⊤) (φ : ℝ ≃o ℝ) (hφ0 : φ 0 = 0) (hφ : ∀ t, η t = L (φ t))
    (harea : ∀ s t : ℝ, s ≤ t → M h (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    AreaClockGood M (h, L) ∧ areaClockCurve M (h, L) = η := by
  have hfoc : IsFiniteMeasureOnCompacts (M h) := ⟨fun K hK => hfin K hK⟩
  have hF : LatticeProb.finiteOnCompactsPart (M h) = M h := LatticeProb.finiteOnCompactsPart_eq_self (M h)
  have hG : IsGoodMassClock (M h) L := isGoodMassClock_of_massParam φ hφ0 hφ harea
  have hcurve : areaClockCurve M (h, L) = η := by
    ext t
    show massReparamCurve (LatticeProb.finiteOnCompactsPart (M h)) L t = η t
    rw [hF, massReparamCurve_apply_of_good hG]
    exact massReparam_eq_of_massParam (M h) L η φ hφ0 hφ harea t
  refine ⟨⟨fun n => hfin _ (isCompact_closedBall 0 n), ?_, ?_⟩, hcurve⟩
  · show IsGoodMassClock (LatticeProb.finiteOnCompactsPart (M h)) L
    rw [hF]
    exact hG
  · intro s t hst
    show LatticeProb.finiteOnCompactsPart (M h) (areaClockCurve M (h, L) '' Icc (s : ℝ) t) = _
    rw [hF, hcurve]
    exact harea s t (by exact_mod_cast hst)

/-- **The covariance of the area clock curve** on a good pair whose area measure changes coordinates under the
similarity `ψ(w) = C w + z`. -/
theorem areaClockCurve_similarity {M : Field → Measure ℂ} {h : Field} {e : C(ℝ, ℂ)} {γ C : ℝ} {z : ℂ}
    (hgood : AreaClockGood M (h, e))
    (hcov : M (lqgSimilarityField γ C z h) = (M h).map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)) (hC : 0 < C) :
    ∃ τ : ℝ, areaClockCurve M (lqgSimilarityField γ C z h, affineReroot z C 0 e) =
      curveSimilarityPullback C z (curveTimeTranslate τ (areaClockCurve M (h, e))) := by
  obtain ⟨hfin, hG, harea⟩ := hgood
  replace hfin : ∀ n : ℕ, M h (Metric.closedBall 0 n) < ⊤ := hfin
  replace hG : IsGoodMassClock (LatticeProb.finiteOnCompactsPart (M h)) e := hG
  replace harea : ∀ s t : ℚ, s ≤ t → LatticeProb.finiteOnCompactsPart (M h)
      (massReparamCurve (LatticeProb.finiteOnCompactsPart (M h)) e '' Icc (s : ℝ) t) =
        ENNReal.ofReal ((t : ℝ) - s) := harea
  have hfoc : IsFiniteMeasureOnCompacts (M h) := isFiniteMeasureOnCompacts_of_forall_closedBall hfin
  have hF : LatticeProb.finiteOnCompactsPart (M h) = M h := LatticeProb.finiteOnCompactsPart_eq_self (M h)
  have hmap : ((M h).map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)) =
      (M h).map (similarityInvHomeomorph C z hC.ne') := rfl
  have hfoc' : IsFiniteMeasureOnCompacts ((M h).map (similarityInvHomeomorph C z hC.ne')) :=
    isFiniteMeasureOnCompacts_map_homeomorph _
  have hF' : LatticeProb.finiteOnCompactsPart (M (lqgSimilarityField γ C z h)) =
      (M h).map (similarityInvHomeomorph C z hC.ne') := by
    rw [hcov, hmap]
    exact LatticeProb.finiteOnCompactsPart_eq_self _
  rw [hF] at hG harea
  obtain ⟨τ, hτ⟩ := massReparamCurve_similarity hG harea hC z
  refine ⟨τ, ?_⟩
  show massReparamCurve (LatticeProb.finiteOnCompactsPart (M (lqgSimilarityField γ C z h)))
      (affineReroot z C 0 e) =
    curveSimilarityPullback C z (curveTimeTranslate τ
      (massReparamCurve (LatticeProb.finiteOnCompactsPart (M h)) e))
  rw [hF', hF]
  exact hτ

/-- **The simultaneous LQG coordinate change of the area measure of the `0`-quantum cone** (Sheffield–Wang,
arXiv:1605.06171, Theorems 1.1, 1.2 and 1.4; written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(d) One area clock
for every similarity", line 48: "Use the Borel field-to-area map `h ↦ μ_h` from the simultaneous coordinate-change
theorem ... On the original field its limit agrees a.s. with the circle-average measure in the coupling. The
simultaneous version gives `μ_{h^T}(A) = μ_h(TA)` for all similarities on one event. For the zero cone, couple to a
whole-plane GFF with the same lateral part and inward Brownian motion ... Localize the GFF on a countable disk cover").

There is a Borel map `M` from fields to measures on `ℂ` such that, for the circle-average embedding
`h = coneField X₀' (coneRadial γ 0 b b')` of the `0`-quantum cone built from a whole-plane GFF `X₀'` and two
independent standard Brownian motions independent of it (`zeroConeFieldOf`), for almost every `h`, `M h` is the vague
limit of the dyadic area approximations of `h`, and for all `C > 0` and `z ∈ ℂ` simultaneously
`M(h(C · + z) + Q log C) = M h ∘ ψ`, `ψ(w) = C w + z` (the image of `M h` by `ψ⁻¹`). -/
def ZeroConeAreaCoordinateChange (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ M : Field → Measure ℂ, Measurable M ∧
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
      IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
      IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
      ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'),
        IsVagueLimitC (lqgAreaApprox γ h) (M h) ∧
          ∀ C : ℝ, 0 < C → ∀ z : ℂ,
            M (lqgSimilarityField γ C z h) = (M h).map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The quantum-time curve as a Borel function of the field and the curve, with the LQG coordinate change**
(`ZeroConeQuantumCurveCovariance`; written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, lines 46-51). The map is the
area clock curve of the Borel area map of `ZeroConeAreaCoordinateChange`: almost surely it returns `η₀` by the area
parametrization of the coupling, the pair `(h₀, ηL)` is almost surely good, and the independence of `h₀` and `ηL`
puts almost every pair in the good set, where the covariance is `areaClockCurve_similarity`. -/
theorem zeroConeQuantumCurveCovariance (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hSW : ZeroConeAreaCoordinateChange γ hγ) :
    ZeroConeQuantumCurveCovariance D hγ := by
  obtain ⟨M, hM, hMlaw⟩ := hSW
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hcov := hMlaw P X₀ B₀ B₀' D.isProbabilityMeasure D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.1
    D.indep_cone₀.2
  obtain ⟨H', hH'm, hH'ind, hH'eq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hh₀ : AEMeasurable (zeroConeFieldOf γ X₀ B₀ B₀') P := hH'm.aemeasurable.congr hH'eq
  have hηm : Measurable ηL := D.measurable_curves.1
  have hgoodω : ∀ᵐ ω ∂P, AreaClockGood M (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) ∧
      areaClockCurve M (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) = η₀ ω := by
    filter_upwards [ae_of_ae_map hh₀ hcov, D.areaParam₀] with ω hω hap
    obtain ⟨⟨φ, hφ0, hφ⟩, harea⟩ := hap
    exact areaClockGood_of_areaParam hω.1.1 φ hφ0 hφ (harea (M (zeroConeFieldOf γ X₀ B₀ B₀' ω)) hω.1)
  have hA : ∀ᵐ a ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, AreaClockGood M (a, e) :=
    ae_ae_mem_of_indepFun_version hH'm hηm hH'ind hH'eq (measurableSet_areaClockGood hM)
      (hgoodω.mono fun _ h => h.1)
  unfold ZeroConeQuantumCurveCovariance
  refine ⟨areaClockCurve M, measurable_areaClockCurve hM, hgoodω.mono fun _ h => h.2, ?_⟩
  filter_upwards [hA, hcov] with a ha hca
  filter_upwards [ha] with e he C hC z
  exact areaClockCurve_similarity he (hca.2 C hC z) hC

end ZeroCone

end MatedCRT
