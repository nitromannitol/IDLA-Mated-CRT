import MatedCRT.FirstPass.Derived.RevuzWindowFormula
import MatedCRT.FirstPass.Derived.RevuzSigmaFinite

/-!
# The time-dependent Revuz formula

For a positive continuous additive functional `A` of planar Brownian motion with σ-finite Revuz measure `μ_A`, every
horizon `N` and every measurable `g : ℝ × ℂ → [0, ∞]`,
`∫ dz E_z ∫_{(0,N]} g(s, B_s) dA_s = ∫_{(0,N]} ∫ g(s, y) μ_A(dy) ds`
(Revuz–Yor (1999), Chapter X, Proposition 2.4, space-time form).

Both sides are integrals against measures on `ℝ × ℂ`: the left side against the Lebesgue-started mixture
`spaceTimeRevuzMeasure A N` of the occupation measures of the space-time path `s ↦ (s, B_s)` against the clock on
`(0, N]`, the right side against `Leb|_{(0,N]} ⊗ μ_A`. On a rectangle `(l, u] × S` both sides are
`Leb((l, u] ∩ (0, N]) · μ_A(S)` by the window formula `lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz`, and
the rectangles with `μ_A(S) < ∞` form a π-system with a spanning sequence of finite measure, so the two measures
agree (`Measure.prod_eq_generateFrom`).

The kernel uses the rational-time regularization `regularize A` of the clock, which is measurable in the path; on
the unshifted path it agrees almost surely with the raw clock.

## Main results

* `spaceTimeClockMeasure A N ω`: the occupation measure of `s ↦ (s, ω_s)` against `dĀ_s(ω)` on `(0, N]`;
* `spaceTimeRevuzMeasure A N`: its mixture over the Lebesgue-started Brownian motion;
* `volume_restrict_prod_revuz_eq`: `Leb|_{(0,N]} ⊗ μ_A = spaceTimeRevuzMeasure A N`;
* `lintegral_setLIntegral_Ioc_spaceTime_eq`: the time-dependent Revuz formula.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- On the unshifted path, the Stieltjes function of the regularized clock is almost surely that of the clock. -/
theorem ae_stieltjesOfNNReal_regularize_eq {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) :
    ∀ᵐ ω ∂W z, stieltjesOfNNReal (fun u => regularize A u ω) = stieltjesOfNNReal fun u => A u ω := by
  filter_upwards [hA.path z] with ω hp
  simp only [regularize_eq_of_continuous_monotone hp.2.1 hp.2.2]

/-- **The window formula for the regularized clock**, for every window `(a, b]` with `0 ≤ a`:
`∫ dz E_z ∫_{(a, b]} g(B_s) dĀ_s = (b - a)⁺ · ∫ g dμ_A`. -/
theorem lintegral_setLIntegral_Ioc_regularize_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc a b, g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => regularize A u ω).measure ∂planarLaw z =
      ENNReal.ofReal (b - a) * ∫⁻ y, g y ∂revuz planarLaw A := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioc_eq_empty (not_lt.2 hba), ENNReal.ofReal_of_nonpos (sub_nonpos.2 hba)]
  · lift a to ℝ≥0 using ha
    have h := lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz hA a hg (sub_nonneg.2 hab.le)
    have hb : (a : ℝ) + (b - a) = b := by ring
    rw [hb] at h
    rw [← h]
    refine lintegral_congr fun z => lintegral_congr_ae ?_
    filter_upwards [ae_stieltjesOfNNReal_regularize_eq hA z] with ω hω
    rw [hω]

/-- The occupation measure of the space-time path `s ↦ (s, ω_s)` against the regularized clock `dĀ_s(ω)` on the
time window `(0, N]`. -/
noncomputable def spaceTimeClockMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (N : ℝ) (ω : ContinuousPath ℂ) :
    Measure (ℝ × ℂ) :=
  ((stieltjesOfNNReal fun u => regularize A u ω).measure.restrict (Ioc 0 N)).map fun s => (s, ω s.toNNReal)

/-- The space-time occupation measure of the regularized clock is measurable in the path. -/
theorem measurable_spaceTimeClockMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (N : ℝ) : Measurable (spaceTimeClockMeasure A N) :=
  LatticeProb.measurable_map_stieltjes_restrict_Ioc_window
    (fun ω : ContinuousPath ℂ => stieltjesOfNNReal (fun t => regularize A t ω))
    (measurable_stieltjesOfNNReal_regularize hA) (fun ω s => (s, ω s.toNNReal))
    (fun ω => continuous_id.prodMk (ω.continuous.comp continuous_real_toNNReal))
    (fun _ => measurable_const.prodMk (ContinuousMap.measurable_eval _)) 0 N

/-- The space-time occupation measure of a rectangle `(l, u] × S` is the clock integral of `1_S(ω_s)` over the
window `(l, u] ∩ (0, N]`. -/
theorem spaceTimeClockMeasure_Ioc_prod (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (N l u : ℝ) (ω : ContinuousPath ℂ)
    {S : Set ℂ} (hS : MeasurableSet S) :
    spaceTimeClockMeasure A N ω (Ioc l u ×ˢ S) = ∫⁻ s in Ioc (max l 0) (min u N), S.indicator 1 (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun t => regularize A t ω).measure := by
  have hω : Measurable fun s : ℝ => ω s.toNNReal := (ω.continuous.comp continuous_real_toNNReal).measurable
  have hγ : Measurable fun s : ℝ => (s, ω s.toNNReal) :=
    (continuous_id.prodMk (ω.continuous.comp continuous_real_toNNReal)).measurable
  have hind : (fun s : ℝ => S.indicator (1 : ℂ → ℝ≥0∞) (ω s.toNNReal)) =
      ((fun s : ℝ => ω s.toNNReal) ⁻¹' S).indicator 1 := rfl
  rw [spaceTimeClockMeasure, Measure.map_apply hγ (measurableSet_Ioc.prod hS),
    Measure.restrict_apply (hγ (measurableSet_Ioc.prod hS)), hind, lintegral_indicator_one (hω hS),
    Measure.restrict_apply (hω hS)]
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
  tauto

/-- The Lebesgue-started mixture of the space-time occupation measures of the regularized clock on `(0, N]`. -/
noncomputable def spaceTimeRevuzMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (N : ℝ) : Measure (ℝ × ℂ) :=
  ((volume : Measure ℂ).bind planarLaw).bind (spaceTimeClockMeasure A N)

/-- The mixture evaluated on a measurable set is the Lebesgue-started expectation of the occupation measure. -/
theorem spaceTimeRevuzMeasure_apply {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t)) (N : ℝ)
    {E : Set (ℝ × ℂ)} (hE : MeasurableSet E) :
    spaceTimeRevuzMeasure A N E = ∫⁻ z, ∫⁻ ω, spaceTimeClockMeasure A N ω E ∂planarLaw z := by
  have hm : Measurable fun ω => spaceTimeClockMeasure A N ω E :=
    (Measure.measurable_coe hE).comp (measurable_spaceTimeClockMeasure hA N)
  rw [spaceTimeRevuzMeasure, Measure.bind_apply hE (measurable_spaceTimeClockMeasure hA N).aemeasurable,
    Measure.lintegral_bind measurable_planarLaw.aemeasurable hm.aemeasurable]

/-- Integrals against the mixture are Lebesgue-started expectations of space-time clock integrals. -/
theorem lintegral_spaceTimeRevuzMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (N : ℝ) {f : ℝ × ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂spaceTimeRevuzMeasure A N = ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc 0 N, f (s, ω s.toNNReal)
      ∂(stieltjesOfNNReal fun u => regularize A u ω).measure ∂planarLaw z := by
  have hm : Measurable fun ω => ∫⁻ p, f p ∂spaceTimeClockMeasure A N ω :=
    (Measure.measurable_lintegral hf).comp (measurable_spaceTimeClockMeasure hA N)
  rw [spaceTimeRevuzMeasure, Measure.lintegral_bind (measurable_spaceTimeClockMeasure hA N).aemeasurable
      hf.aemeasurable, Measure.lintegral_bind measurable_planarLaw.aemeasurable hm.aemeasurable]
  refine lintegral_congr fun z => lintegral_congr fun ω => ?_
  have hγ : Measurable fun s : ℝ => (s, ω s.toNNReal) :=
    (continuous_id.prodMk (ω.continuous.comp continuous_real_toNNReal)).measurable
  rw [spaceTimeClockMeasure, lintegral_map hf hγ]

/-- **The space-time mixture on rectangles**: `spaceTimeRevuzMeasure A N ((l, u] × S) = Leb((l, u] ∩ (0, N]) · μ_A(S)`. -/
theorem spaceTimeRevuzMeasure_Ioc_prod {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A) (N l u : ℝ)
    {S : Set ℂ} (hS : MeasurableSet S) :
    spaceTimeRevuzMeasure A N (Ioc l u ×ˢ S) =
      (volume.restrict (Ioc (0 : ℝ) N)) (Ioc l u) * revuz planarLaw A S := by
  rw [spaceTimeRevuzMeasure_apply hA.meas N (measurableSet_Ioc.prod hS)]
  simp only [spaceTimeClockMeasure_Ioc_prod A N l u _ hS]
  rw [lintegral_setLIntegral_Ioc_regularize_eq hA (le_max_right l 0) (min u N) (measurable_one.indicator hS),
    lintegral_indicator_one hS, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, Real.volume_Ioc]

/-- **The space-time Revuz measure is a product**: for a positive continuous additive functional `A` of planar
Brownian motion with a good clock, `Leb|_{(0,N]} ⊗ μ_A = spaceTimeRevuzMeasure A N`. -/
theorem volume_restrict_prod_revuz_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (hG : GoodClock planarLaw A) (N : ℝ) :
    (volume.restrict (Ioc (0 : ℝ) N)).prod (revuz planarLaw A) = spaceTimeRevuzMeasure A N := by
  have := sigmaFinite_revuz hA hG
  set μ := revuz planarLaw A with hμ
  have hD : MeasurableSpace.generateFrom {S : Set ℂ | MeasurableSet S ∧ μ S < ∞} =
      (inferInstance : MeasurableSpace ℂ) := by
    refine le_antisymm (MeasurableSpace.generateFrom_le fun S hS => hS.1) fun S hS => ?_
    have hS' : S = ⋃ n, S ∩ spanningSets μ n := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
    rw [hS']
    exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
      ⟨hS.inter (measurableSet_spanningSets μ n),
        (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)⟩
  have h3C : (volume.restrict (Ioc (0 : ℝ) N)).FiniteSpanningSetsIn
      {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S} :=
    { set := fun n : ℕ => Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
      set_mem := fun n => ⟨_, _, by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith, rfl⟩
      finite := fun _ => (Measure.restrict_apply_le _ _).trans_lt measure_Ioc_lt_top
      spanning := eq_univ_of_forall fun x => by
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        exact mem_iUnion.2 ⟨n, mem_Ioc.2 ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩⟩ }
  have h3D : μ.FiniteSpanningSetsIn {S : Set ℂ | MeasurableSet S ∧ μ S < ∞} :=
    { set := spanningSets μ
      set_mem := fun n => ⟨measurableSet_spanningSets μ n, measure_spanningSets_lt_top μ n⟩
      finite := measure_spanningSets_lt_top μ
      spanning := iUnion_spanningSets μ }
  refine Measure.prod_eq_generateFrom ((borel_eq_generateFrom_Ioc ℝ).symm.trans BorelSpace.measurable_eq.symm)
    hD (isPiSystem_Ioc (id : ℝ → ℝ) id)
    (fun S hS T hT _ => ⟨hS.1.inter hT.1, (measure_mono inter_subset_left).trans_lt hS.2⟩) h3C h3D ?_
  rintro s ⟨l, u, -, rfl⟩ t ht
  exact spaceTimeRevuzMeasure_Ioc_prod hA N l u ht.1

/-- **The time-dependent Revuz formula** (Revuz–Yor (1999), Chapter X, Proposition 2.4, space-time form). For a
positive continuous additive functional `A` of planar Brownian motion with a good clock, every horizon `N` and every
measurable `g : ℝ × ℂ → [0, ∞]`, `∫ dz E_z ∫_{(0,N]} g(s, B_s) dA_s = ∫_{(0,N]} ∫ g(s, y) μ_A(dy) ds`. -/
theorem lintegral_setLIntegral_Ioc_spaceTime_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (hG : GoodClock planarLaw A) (N : ℝ) {g : ℝ × ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc 0 N, g (s, ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z =
      ∫⁻ s in Ioc 0 N, ∫⁻ y, g (s, y) ∂revuz planarLaw A := by
  have := sigmaFinite_revuz hA hG
  calc ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc 0 N, g (s, ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z
      = ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc 0 N, g (s, ω s.toNNReal)
          ∂(stieltjesOfNNReal fun u => regularize A u ω).measure ∂planarLaw z := by
        refine lintegral_congr fun z => lintegral_congr_ae ?_
        filter_upwards [ae_stieltjesOfNNReal_regularize_eq hA z] with ω hω
        rw [hω]
    _ = ∫⁻ p, g p ∂spaceTimeRevuzMeasure A N := (lintegral_spaceTimeRevuzMeasure hA.meas N hg).symm
    _ = ∫⁻ p, g p ∂(volume.restrict (Ioc (0 : ℝ) N)).prod (revuz planarLaw A) := by
        rw [volume_restrict_prod_revuz_eq hA hG N]
    _ = ∫⁻ s in Ioc 0 N, ∫⁻ y, g (s, y) ∂revuz planarLaw A := lintegral_prod _ hg.aemeasurable

end MatedCRT
