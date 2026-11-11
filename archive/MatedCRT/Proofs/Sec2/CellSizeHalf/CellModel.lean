import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.SLEInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping

/-!
# A valid environment as Bonanno's cell model

Leonardo Bonanno's formalization of GMS19 Lemmas 2.7 and 2.8 (adapted from Leonardo Bonanno's lean-formalizations,
https://github.com/leobon12/lean-formalizations, module `MatedCRTHarmonic.GMSLemma27`, as ported to
Lattice-Probability) is stated for an abstract cell model `MatedCRTHarmonic.GMSLemma27.CellModel γ`: a probability
space with a field, its LQG area measure and a curve parametrized by area with `η(0) = 0`.

* `MatedCRTEnv.toCellModel`: the cell model of a valid environment (area `μ_h`, curve `η`). The field of the cell
  model (a random distribution) is not read by Lemmas 2.7 and 2.8 and is taken to be `0`. Its cells
  `η([ε(x-1), εx])` are our `cell ε η x` (definitionally).
* `segmentsContainBalls_toCellModel`: Bonanno's SLE interface `SegmentsContainBalls` (GHM15 Proposition 3.4 with
  Remark 3.9, `P(E_ε(R, r)ᶜ) = o^∞(ε)`) for this model, from the field `segmentsContainBalls` of the mating-of-trees
  coupling (`MatedCRTEnv.IsValid.matingOfTrees`) for the Lebesgue-parametrized curve `ηL`: `η = ηL ∘ φ` with `φ` an
  order isomorphism (`areaParam`), so the segments of `η` are those of `ηL`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Asymptotics
open scoped ENNReal

/-- `μ(η({a})) = 0` for a curve parametrized by `μ`-area. -/
theorem IsAreaParametrized.measure_image_Icc {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {a b : ℝ} (hab : a ≤ b) : μ (η '' Icc a b) = ENNReal.ofReal (b - a) := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact h.2.2.2 a b hlt
  · rw [sub_self, ENNReal.ofReal_zero, Icc_self, image_singleton]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun t ht _ => ?_) zero_le
    calc μ {η a} ≤ μ (η '' Icc a (a + t)) :=
          measure_mono (singleton_subset_iff.mpr ⟨a, ⟨le_rfl, by simp⟩, rfl⟩)
      _ = ENNReal.ofReal (a + t - a) := h.2.2.2 a (a + t) (by simpa using ht)
      _ = 0 + (t : ℝ≥0∞) := by rw [add_sub_cancel_left, ENNReal.ofReal_coe_nnreal, zero_add]

/-- **The cell model of a valid environment** (Bonanno's `CellModel γ`): sample space `Ω`, law `P`, area `μ_h`,
curve `η`; the field is not used by Lemmas 2.7 and 2.8 and is `0`. -/
noncomputable def MatedCRTEnv.toCellModel {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) : MatedCRTHarmonic.GMSLemma27.CellModel γ where
  Ω := Ω
  measurableSpace := ‹_›
  P := S.P
  isProbabilityMeasure := hS.isProbabilityMeasure
  field := fun _ => 0
  area := S.μ
  curve := S.η
  ae_continuous_curve := hS.isAreaParametrized.mono fun _ h => h.1
  ae_curve_zero := hS.isAreaParametrized.mono fun _ h => h.2.1
  ae_area_curve := hS.isAreaParametrized.mono fun _ h _ _ hab => h.measure_image_Icc hab

/-- The segments of `η` and of the Lebesgue-parametrized `ηL` agree when `η = ηL ∘ φ`, `φ` an order isomorphism. -/
theorem image_Icc_eq_of_orderIso {η : ℝ → ℂ} {ηL : ℝ → ℂ} (φ : ℝ ≃o ℝ) (h : ∀ t, η t = ηL (φ t)) (a b : ℝ) :
    η '' Icc a b = ηL '' Icc (φ a) (φ b) := by
  have h1 : η = ηL ∘ φ := funext h
  rw [h1, image_comp, OrderIso.image_Icc]

/-- **Bonanno's SLE interface `SegmentsContainBalls` for the cell model of a valid environment**, from the field
`segmentsContainBalls` (GHM15 Proposition 3.4 + Remark 3.9) of the mating-of-trees coupling. -/
theorem segmentsContainBalls_toCellModel {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    MatedCRTHarmonic.GMSLemma27.SegmentsContainBalls (S.toCellModel hS) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcoup, hae⟩ := hS.matingOfTrees
  intro r hr R hR s
  have hsub : ∀ ε, S.P (MatedCRTHarmonic.GMSLemma27.segmentBallEvent (S.toCellModel hS) R r ε)ᶜ ≤
      S.P {ω | ¬ MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (ηL ω) R r ε} := by
    intro ε
    refine measure_mono_ae ?_
    filter_upwards [hae, hcoup.areaParam] with ω hω hφ
    intro hbad hgood
    apply hbad
    obtain ⟨φ, -, hφη⟩ := hφ.1
    have himg : ∀ a b, S.η ω '' Icc a b = ηL ω '' Icc (φ a) (φ b) := fun a b =>
      image_Icc_eq_of_orderIso φ (fun t => by rw [← hφη t, hω.1]) a b
    intro δ hδ a b hab hsubR hdiam
    change S.η ω '' Icc a b ⊆ ball 0 R at hsubR
    change δ ^ (1 - r) ≤ diam (S.η ω '' Icc a b) at hdiam
    rw [himg] at hsubR hdiam
    obtain ⟨w, hw⟩ := hgood δ hδ (φ a) (φ b) (φ.lt_iff_lt.mpr hab) hsubR hdiam
    refine ⟨w, δ, le_rfl, ?_⟩
    change ball w δ ⊆ S.η ω '' Icc a b
    rw [himg]
    exact hw
  set N : ℕ := ⌈s⌉₊ + 1 with hN
  have hNs : 0 < (N : ℝ) - s := by
    have := Nat.le_ceil s
    rw [hN]; push_cast; linarith
  obtain ⟨C, hC⟩ := hcoup.segmentsContainBalls R hR r hr N
  set K : ℝ := max C 0 + 1 with hK
  have hK0 : 0 < K := by rw [hK]; linarith [le_max_right C 0]
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [MatedCRTHarmonic.GMSLemma27.eventually_lt_nhdsGT_zero one_pos,
    MatedCRTHarmonic.GMSLemma27.eventually_rpow_lt hNs (div_pos hc hK0), self_mem_nhdsWithin]
    with ε h1 h2 hε0
  have hε : 0 < ε := hε0
  have hpow : 0 ≤ ε ^ N := pow_nonneg hε.le N
  have hbd : S.P (MatedCRTHarmonic.GMSLemma27.segmentBallEvent (S.toCellModel hS) R r ε)ᶜ ≤
      ENNReal.ofReal (max C 0 * ε ^ N) :=
    ((hsub ε).trans (hC ε ⟨hε, h1⟩)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow))
  have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_max_right _ _) hpow) hbd
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (Real.rpow_nonneg hε.le _)]
  have hsplit : ε ^ N = ε ^ ((N : ℝ) - s) * ε ^ s := by
    rw [← Real.rpow_add hε, sub_add_cancel, Real.rpow_natCast]
  have hlt : K * ε ^ ((N : ℝ) - s) ≤ c := by
    have := (lt_div_iff₀' hK0).mp h2
    linarith
  calc (S.P (MatedCRTHarmonic.GMSLemma27.segmentBallEvent (S.toCellModel hS) R r ε)ᶜ).toReal
      ≤ max C 0 * ε ^ N := hreal
    _ ≤ K * ε ^ N := mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hpow
    _ = K * ε ^ ((N : ℝ) - s) * ε ^ s := by rw [hsplit, mul_assoc]
    _ ≤ c * ε ^ s := mul_le_mul_of_nonneg_right hlt (Real.rpow_nonneg hε.le _)

end MatedCRT
