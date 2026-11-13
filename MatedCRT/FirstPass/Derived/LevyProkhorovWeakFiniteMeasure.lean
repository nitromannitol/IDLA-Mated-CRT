import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Lévy–Prokhorov convergence of finite measures implies weak convergence

On a pseudometric space `X` (with a Borel-measurable topology in the sense of
`OpensMeasurableSpace`), convergence of finite measures in the Lévy–Prokhorov distance
`MeasureTheory.levyProkhorovDist` implies convergence in the topology of weak convergence, which
is the topology of `MeasureTheory.FiniteMeasure X`. No separability is needed.

Mathlib proves this for probability measures (the Lévy–Prokhorov topology on
`ProbabilityMeasure X` is finer than the topology of convergence in distribution). The
finite-measure case reduces to it by normalization:
* the Lévy–Prokhorov distance controls the difference of the total masses
  (`abs_measure_univ_toReal_sub_le_levyProkhorovDist`), so the masses converge;
* if the limit has mass zero, the measures converge weakly to zero because their masses do;
* otherwise the normalized measures converge in the Lévy–Prokhorov distance, by the scaling
  bound `levyProkhorovDist_nnreal_smul_le_of_isFiniteMeasure`
  `levyProkhorovDist (a • μ) (b • ν) ≤ (1 + a + b) * levyProkhorovDist μ ν + |a - b| (μ(X) + ν(X))`,
  hence weakly as probability measures; together with the convergence of the masses this is
  weak convergence of the finite measures.

## Main results

* `MatedCRT.tendsto_finiteMeasure_of_tendsto_levyProkhorovDist`: if
  `levyProkhorovDist (μ i) μ₀ → 0`, then `μ i → μ₀` weakly.
* `MatedCRT.continuous_levyProkhorov_toFiniteMeasure`: the identity from finite measures with the
  Lévy–Prokhorov metric to finite measures with the topology of weak convergence is continuous.

## References

* P. Billingsley, *Convergence of Probability Measures*, Section 6.
-/

open MeasureTheory Filter Metric Set Topology
open scoped ENNReal NNReal

namespace MatedCRT

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- If `levyProkhorovEDist μ ν < δ`, the total mass of `μ` is at most that of `ν` plus `δ`. -/
theorem measure_univ_le_add_of_levyProkhorovEDist_lt {μ ν : Measure X} {δ : ℝ}
    (h : levyProkhorovEDist μ ν < ENNReal.ofReal δ) : μ univ ≤ ν univ + ENNReal.ofReal δ :=
  (left_measure_le_of_levyProkhorovEDist_lt h MeasurableSet.univ).trans
    (add_le_add (measure_mono (subset_univ _)) le_rfl)

/-- The total mass of `μ` exceeds that of `ν` by at most the Lévy–Prokhorov distance. -/
theorem measure_univ_toReal_le_add_levyProkhorovDist (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    (μ univ).toReal ≤ (ν univ).toReal + levyProkhorovDist μ ν := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set d := levyProkhorovDist μ ν with hd_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hD : levyProkhorovEDist μ ν = ENNReal.ofReal d :=
    (ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)).symm
  have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal (d + ε) := by
    rw [hD]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top ν univ, ENNReal.ofReal_ne_top⟩)
    (measure_univ_le_add_of_levyProkhorovEDist_lt hlt)
  rw [ENNReal.toReal_add (measure_ne_top ν univ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at h
  linarith

/-- The total masses of two finite measures differ by at most their Lévy–Prokhorov distance. -/
theorem abs_measure_univ_toReal_sub_le_levyProkhorovDist (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    |(μ univ).toReal - (ν univ).toReal| ≤ levyProkhorovDist μ ν := by
  have h1 := measure_univ_toReal_le_add_levyProkhorovDist μ ν
  have h2 := measure_univ_toReal_le_add_levyProkhorovDist ν μ
  rw [levyProkhorovDist_comm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Scalar step: if `x ≤ y + δ` with `y ≤ M`, then `a * x ≤ b * y + (|a - b| * M + a * δ)`. -/
private lemma nnreal_mul_le_mul_add_of_le_add_of_le {x y M : ℝ≥0∞} {δ : ℝ} (a b : ℝ≥0)
    (hy : y ≤ M) (hxy : x ≤ y + ENNReal.ofReal δ) :
    (a : ℝ≥0∞) * x ≤
      (b : ℝ≥0∞) * y + (ENNReal.ofReal |(a : ℝ) - b| * M + ENNReal.ofReal (a * δ)) := by
  have hab : (a : ℝ≥0∞) ≤ b + ENNReal.ofReal |(a : ℝ) - b| := by
    have h1 : (a : ℝ) ≤ (b : ℝ) + |(a : ℝ) - b| := by
      linarith [le_abs_self ((a : ℝ) - b)]
    calc (a : ℝ≥0∞) = ENNReal.ofReal a := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal ((b : ℝ) + |(a : ℝ) - b|) := ENNReal.ofReal_le_ofReal h1
      _ = b + ENNReal.ofReal |(a : ℝ) - b| := by
          rw [ENNReal.ofReal_add b.coe_nonneg (abs_nonneg _), ENNReal.ofReal_coe_nnreal]
  calc (a : ℝ≥0∞) * x ≤ a * (y + ENNReal.ofReal δ) := by gcongr
    _ = a * y + ENNReal.ofReal (a * δ) := by
        rw [mul_add, ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ (b + ENNReal.ofReal |(a : ℝ) - b|) * y + ENNReal.ofReal (a * δ) := by gcongr
    _ = b * y + ENNReal.ofReal |(a : ℝ) - b| * y + ENNReal.ofReal (a * δ) := by
        rw [add_mul]
    _ ≤ b * y + ENNReal.ofReal |(a : ℝ) - b| * M + ENNReal.ofReal (a * δ) := by gcongr
    _ = b * y + (ENNReal.ofReal |(a : ℝ) - b| * M + ENNReal.ofReal (a * δ)) := by
        rw [add_assoc]

/-- **Lévy–Prokhorov distance between multiples of finite measures.** For finite measures `μ`, `ν`
and `a b : ℝ≥0`,
`levyProkhorovDist (a • μ) (b • ν) ≤ (1 + a + b) * levyProkhorovDist μ ν + |a - b| (μ(X) + ν(X))`. -/
theorem levyProkhorovDist_nnreal_smul_le_of_isFiniteMeasure (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : ℝ≥0) :
    levyProkhorovDist (a • μ) (b • ν) ≤
      (1 + a + b) * levyProkhorovDist μ ν +
        |(a : ℝ) - b| * ((μ univ).toReal + (ν univ).toReal) := by
  set d := levyProkhorovDist μ ν with hd_def
  set m : ℝ := (μ univ).toReal + (ν univ).toReal with hm_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  have hb0 : (0 : ℝ) ≤ b := b.coe_nonneg
  have hab : 0 < 1 + (a : ℝ) + b := by positivity
  set e : ℝ := |(a : ℝ) - b| * m with he_def
  have he0 : 0 ≤ e := mul_nonneg (abs_nonneg _) hm0
  have hR0 : 0 ≤ (1 + a + b) * d + e := add_nonneg (mul_nonneg hab.le hd0) he0
  have hD : levyProkhorovEDist μ ν = ENNReal.ofReal d :=
    (ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)).symm
  have hM : μ univ + ν univ = ENNReal.ofReal m := by
    rw [hm_def, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ univ), ENNReal.ofReal_toReal (measure_ne_top ν univ)]
  suffices key : levyProkhorovEDist (a • μ) (b • ν) ≤ ENNReal.ofReal ((1 + a + b) * d + e) from
    ENNReal.toReal_le_of_le_ofReal hR0 key
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hε_top hB
  have hε_ne : ε ≠ ∞ := hε_top.ne
  have hr0 : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
  have hRr : (1 + a + b) * d + e < ε.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hR0 hε_ne).1 hε
  set δ : ℝ := (ε.toReal - e) / (1 + a + b) with hδ_def
  have hdδ : d < δ := by
    rw [hδ_def, lt_div_iff₀ hab]
    linarith
  have hδ0 : 0 ≤ δ := hd0.trans hdδ.le
  have hδmul : (1 + a + b) * δ = ε.toReal - e := by
    rw [hδ_def]
    field_simp
  have hδr : δ ≤ ε.toReal := by
    rw [hδ_def, div_le_iff₀ hab]
    nlinarith [mul_nonneg hr0 ha0, mul_nonneg hr0 hb0]
  have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal δ := by
    rw [hD]
    exact (ENNReal.ofReal_lt_ofReal_iff (hd0.trans_lt hdδ)).2 hdδ
  have hthick (ρ : Measure X) : ρ (thickening δ B) ≤ ρ (thickening ε.toReal B) :=
    measure_mono (thickening_mono hδr B)
  have hμB : μ B ≤ ν (thickening δ B) + ENNReal.ofReal δ := by
    have h := left_measure_le_of_levyProkhorovEDist_lt hlt hB
    rwa [ENNReal.toReal_ofReal hδ0] at h
  have hνB : ν B ≤ μ (thickening δ B) + ENNReal.ofReal δ := by
    have h := right_measure_le_of_levyProkhorovEDist_lt hlt hB
    rwa [ENNReal.toReal_ofReal hδ0] at h
  have hνM : ν (thickening δ B) ≤ μ univ + ν univ :=
    (measure_mono (subset_univ _)).trans le_add_self
  have hμM : μ (thickening δ B) ≤ μ univ + ν univ :=
    (measure_mono (subset_univ _)).trans le_self_add
  have herr (p : ℝ≥0) (hp : (p : ℝ) * δ ≤ (1 + a + b) * δ) (q : ℝ≥0)
      (hpq : |(p : ℝ) - q| = |(a : ℝ) - b|) :
      ENNReal.ofReal |(p : ℝ) - q| * (μ univ + ν univ) + ENNReal.ofReal (p * δ) ≤ ε := by
    rw [hM, ← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hm0) (mul_nonneg p.coe_nonneg hδ0),
      ← ENNReal.ofReal_toReal hε_ne]
    exact ENNReal.ofReal_le_ofReal (by rw [hpq]; linarith)
  have hδa : (a : ℝ) * δ ≤ (1 + a + b) * δ := by nlinarith [mul_nonneg hb0 hδ0]
  have hδb : (b : ℝ) * δ ≤ (1 + a + b) * δ := by nlinarith [mul_nonneg ha0 hδ0]
  refine ⟨?_, ?_⟩
  · rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    exact (nnreal_mul_le_mul_add_of_le_add_of_le a b hνM hμB).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hthick ν) zero_le) (herr a hδa b rfl))
  · rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    exact (nnreal_mul_le_mul_add_of_le_add_of_le b a hμM hνB).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hthick μ) zero_le)
        (herr b hδb a (abs_sub_comm _ _)))

variable [OpensMeasurableSpace X]

/-- **Lévy–Prokhorov convergence of probability measures implies weak convergence** (Mathlib's
comparison of the two topologies, in sequential form). -/
theorem tendsto_probabilityMeasure_of_tendsto_levyProkhorovDist {ι : Type*} {L : Filter ι}
    {P : ι → ProbabilityMeasure X} {P₀ : ProbabilityMeasure X}
    (h : Tendsto (fun i => levyProkhorovDist (P i : Measure X) (P₀ : Measure X)) L (𝓝 0)) :
    Tendsto P L (𝓝 P₀) := by
  have hlp : Tendsto (fun i => LevyProkhorov.ofMeasure (P i)) L
      (𝓝 (LevyProkhorov.ofMeasure P₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (h.congr fun i =>
      (LevyProkhorov.dist_probabilityMeasure_def (LevyProkhorov.ofMeasure (P i))
        (LevyProkhorov.ofMeasure P₀)).symm)
  exact ((LevyProkhorov.continuous_toMeasure_probabilityMeasure (Ω := X)).tendsto _).comp hlp

/-- **Lévy–Prokhorov convergence of finite measures implies weak convergence.** If finite measures
`μ i` satisfy `levyProkhorovDist (μ i) μ₀ → 0`, then `μ i → μ₀` in the topology of weak
convergence of finite measures. -/
theorem tendsto_finiteMeasure_of_tendsto_levyProkhorovDist {ι : Type*} {L : Filter ι}
    {μ : ι → FiniteMeasure X} {μ₀ : FiniteMeasure X}
    (h : Tendsto (fun i => levyProkhorovDist (μ i : Measure X) (μ₀ : Measure X)) L (𝓝 0)) :
    Tendsto μ L (𝓝 μ₀) := by
  have hmassR_eq (ν : FiniteMeasure X) : ((ν : Measure X) univ).toReal = (ν.mass : ℝ) := by
    rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
  have hmassR : Tendsto (fun i => ((μ i).mass : ℝ)) L (𝓝 (μ₀.mass : ℝ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) h
    rw [Real.norm_eq_abs, ← hmassR_eq, ← hmassR_eq]
    exact abs_measure_univ_toReal_sub_le_levyProkhorovDist _ _
  have hmass : Tendsto (fun i => (μ i).mass) L (𝓝 μ₀.mass) := NNReal.tendsto_coe.1 hmassR
  by_cases hμ₀ : μ₀ = 0
  · subst hμ₀
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa using hmass
  · have : Nonempty X := by
      rcases isEmpty_or_nonempty X with hX | hX
      · exact absurd (Subtype.ext (Measure.eq_zero_of_isEmpty _)) hμ₀
      · exact hX
    have hm₀ : μ₀.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff μ₀).2 hμ₀
    have hm₀R : (μ₀.mass : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hm₀
    rw [← FiniteMeasure.tendsto_normalize_iff_tendsto hμ₀]
    refine ⟨tendsto_probabilityMeasure_of_tendsto_levyProkhorovDist ?_, hmass⟩
    have hbound : ∀ᶠ i in L,
        levyProkhorovDist ((μ i).normalize : Measure X) (μ₀.normalize : Measure X) ≤
          (1 + ((μ i).mass : ℝ)⁻¹ + (μ₀.mass : ℝ)⁻¹) *
              levyProkhorovDist (μ i : Measure X) (μ₀ : Measure X) +
            |((μ i).mass : ℝ)⁻¹ - (μ₀.mass : ℝ)⁻¹| * (((μ i).mass : ℝ) + μ₀.mass) := by
      filter_upwards [hmass.eventually_ne hm₀] with i hi
      have hi' : μ i ≠ 0 := (FiniteMeasure.mass_nonzero_iff _).1 hi
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hi',
        FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hμ₀]
      have hle := levyProkhorovDist_nnreal_smul_le_of_isFiniteMeasure (μ i : Measure X)
        (μ₀ : Measure X) (μ i).mass⁻¹ μ₀.mass⁻¹
      rw [hmassR_eq, hmassR_eq, NNReal.coe_inv, NNReal.coe_inv] at hle
      exact hle
    have hinv : Tendsto (fun i => ((μ i).mass : ℝ)⁻¹) L (𝓝 (μ₀.mass : ℝ)⁻¹) :=
      hmassR.inv₀ hm₀R
    have h1 : Tendsto (fun i => (1 + ((μ i).mass : ℝ)⁻¹ + (μ₀.mass : ℝ)⁻¹) *
        levyProkhorovDist (μ i : Measure X) (μ₀ : Measure X)) L
        (𝓝 ((1 + (μ₀.mass : ℝ)⁻¹ + (μ₀.mass : ℝ)⁻¹) * 0)) :=
      ((tendsto_const_nhds.add hinv).add_const _).mul h
    have h2 : Tendsto (fun i => |((μ i).mass : ℝ)⁻¹ - (μ₀.mass : ℝ)⁻¹| *
        (((μ i).mass : ℝ) + μ₀.mass)) L
        (𝓝 (|(μ₀.mass : ℝ)⁻¹ - (μ₀.mass : ℝ)⁻¹| * ((μ₀.mass : ℝ) + μ₀.mass))) :=
      (hinv.sub_const _).abs.mul (hmassR.add_const _)
    rw [mul_zero] at h1
    rw [sub_self, abs_zero, zero_mul] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact squeeze_zero' (Eventually.of_forall fun i => ENNReal.toReal_nonneg) hbound h3

/-- **The Lévy–Prokhorov topology on finite measures is finer than the weak topology.** The
identity from finite measures with the Lévy–Prokhorov metric to finite measures with the topology
of weak convergence is continuous. -/
theorem continuous_levyProkhorov_toFiniteMeasure :
    Continuous (LevyProkhorov.toMeasure : LevyProkhorov (FiniteMeasure X) → FiniteMeasure X) := by
  rw [continuous_iff_continuousAt]
  intro μ
  refine tendsto_finiteMeasure_of_tendsto_levyProkhorovDist ?_
  refine (tendsto_iff_dist_tendsto_zero.1 (tendsto_id (x := 𝓝 μ))).congr fun ν => ?_
  exact LevyProkhorov.dist_finiteMeasure_def ν μ

end MatedCRT
