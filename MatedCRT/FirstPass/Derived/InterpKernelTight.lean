import MatedCRT.FirstPass.Derived.InterpKernelPointwise
import MatedCRT.FirstPass.Derived.InterpKernelUniform
import LatticeProb.Prob.LawKernelTightness

/-!
# Tightness of the interpolated quenched walk laws in `C(ℂ, 𝒫(path space))`

The interpolated walk law `P̃^{ε_n}(ω) : ℂ → 𝒫(ContinuousPath ℂ)` (transported to the
Lévy–Prokhorov space) is a random continuous map.  For a mesh sequence `ε_n → 0`, the family of
its laws is tight in `C(ℂ, 𝒫(ContinuousPath ℂ))`: the uniform modulus of continuity in law
(`exists_delta_forall_interpWalkLaw_modulus`) and the pointwise compact value sets
(`exists_isCompact_interpWalkLaw`, with the thresholds of `UniformScales` and a union bound over the
radii `m` and levels `k`) are the two hypotheses of `LatticeProb.isTightMeasureSet_map_of_kernelModuli`
(Arzelà–Ascoli in probabilistic form).
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] dUnifMetricSpace

section AE

variable {Z Y ι W : Type*} [PseudoMetricSpace Z] [CompactlyCoherentSpace Z] [MetricSpace Y]
  [MeasurableSpace W] [MeasurableSpace C(Z, Y)] [BorelSpace C(Z, Y)]

/-- **Tightness of the laws of random continuous maps that are only almost everywhere
measurable.**  Version of `LatticeProb.isTightMeasureSet_map_of_kernelModuli` with `AEMeasurable`
random elements. -/
theorem isTightMeasureSet_map_of_kernelModuli_aemeasurable (μ : ι → Measure W)
    (X : ι → W → C(Z, Y)) (hX : ∀ i, AEMeasurable (X i) (μ i)) (z₀ : Z)
    (hmod : ∀ L : ℝ, 1 < L → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, μ i {ω | X i ω ∈ kernelModulusFailure z₀ L δ} ≤ ENNReal.ofReal (1 / L))
    (hpt : ∀ ζ : ℝ, 0 < ζ → ∃ K : Z → Set Y, (∀ z, IsCompact (K z)) ∧
      ∀ i, μ i {ω | ∃ z, X i ω z ∉ K z} ≤ ENNReal.ofReal ζ) :
    IsTightMeasureSet {ν : Measure C(Z, Y) | ∃ i, ν = (μ i).map (X i)} := by
  have hset : {ν : Measure C(Z, Y) | ∃ i, ν = (μ i).map (X i)} =
      {ν : Measure C(Z, Y) | ∃ i, ν = (μ i).map ((hX i).mk (X i))} := by
    ext ν
    simp only [mem_ofPred_eq]
    exact exists_congr fun i => by rw [Measure.map_congr (hX i).ae_eq_mk]
  rw [hset]
  refine isTightMeasureSet_map_of_kernelModuli μ (fun i => (hX i).mk (X i))
    (fun i => (hX i).measurable_mk) z₀ ?_ ?_
  · intro L hL
    obtain ⟨δ, hδ, h⟩ := hmod L hL
    refine ⟨δ, hδ, fun i => ?_⟩
    refine (measure_congr (Filter.eventuallyEqSet_iff.2 ((hX i).ae_eq_mk.mono fun ω hω => ?_))).le.trans
      (h i)
    simp only [mem_ofPred_eq, hω]
  · intro ζ hζ
    obtain ⟨K, hK, h⟩ := hpt ζ hζ
    refine ⟨K, hK, fun i => ?_⟩
    refine (measure_congr (Filter.eventuallyEqSet_iff.2 ((hX i).ae_eq_mk.mono fun ω hω => ?_))).le.trans
      (h i)
    simp only [mem_ofPred_eq, hω]

end AE

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Pointwise compact value sets of the interpolated walk law, with high probability uniformly in
the mesh index.**  If the mesh sequence is bounded by `B` and the vertex path failure events are
small for large indices (`hEqPath`), then for every `ζ > 0` there are compact sets `K z` of the
Lévy–Prokhorov space of path laws such that, for **every** `n`, with probability at least
`1 - ζ` the interpolated walk law `P̃^{ε_n}(ω)(z)` lies in `K z` for **all** `z ∈ ℂ`. -/
theorem exists_pointwise_compact_interpWalkLawLP {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0)) {B : ℝ} (hB : ∀ n, eps n ≤ B)
    (hEqPath : ∀ R L a : ℝ, 0 < L → 0 < a → ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ᶠ n in atTop, S.P (vertexPathFailure S η' (eps n) R L a δ) ≤ ENNReal.ofReal a)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℂ → Set (LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))),
      (∀ z, IsCompact (K z)) ∧
      ∀ n, S.P {ω | ∃ z, interpWalkLawLP S η' (eps n) ω z ∉ K z} ≤ ENNReal.ofReal ζ := by
  have hprop := ae_mem_properCurveSet hS hae
  have hD : ∀ m : ℕ, ∃ D : ℝ, 1 ≤ D ∧ ∀ n,
      S.P {ω | ENNReal.ofReal D < maxCellDiam (eps n) (⇑(η' ω)) ((m : ℝ) + B)} ≤
        ENNReal.ofReal (ζ / 4 / 2 / 2 ^ m) := fun m =>
    exists_cellDiam_scale_forall hS hη' hae hε0 hε ((m : ℝ) + B)
      (ENNReal.ofReal_pos.2 (by positivity))
  choose D hD1 hDP using hD
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ → ℝ,
      ∀ m k, a m k = min (1 / ((k : ℝ) + 1)) (ζ / 4 / 2 / 2 ^ m / 2 / 2 ^ k) :=
    ⟨fun m k => min (1 / ((k : ℝ) + 1)) (ζ / 4 / 2 / 2 ^ m / 2 / 2 ^ k), fun _ _ => rfl⟩
  have ha0 : ∀ m k, 0 < a m k := fun m k => by
    rw [ha]
    exact lt_min (by positivity) (by positivity)
  have ha1 : ∀ m k, a m k ≤ 1 / ((k : ℝ) + 1) := fun m k => by
    rw [ha]
    exact min_le_left _ _
  have ha2 : ∀ m k, a m k ≤ ζ / 4 / 2 / 2 ^ m / 2 / 2 ^ k := fun m k => by
    rw [ha]
    exact min_le_right _ _
  have hδ : ∀ m k : ℕ, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ n,
      S.P (vertexPathFailure S η' (eps n) ((m : ℝ) + B + D m) ((k : ℝ) + 1) (a m k) δ) ≤
        ENNReal.ofReal (a m k) := fun m k =>
    exists_vertexPathFailure_scale_forall hS hη' hae hε0 _ (by positivity) (ha0 m k)
      (hEqPath _ _ _ (by positivity) (ha0 m k))
  choose δ hδ0 hδP using hδ
  have hK : ∀ z : ℂ, ∃ K : Set (LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))),
      IsCompact K ∧ ∀ (ω : Ω) (ε : ℝ), ω ∈ properCurveSet η' → 0 < ε → ε ≤ B →
        ‖z‖ ≤ ((⌈‖z‖⌉₊ : ℕ) : ℝ) →
        maxCellDiam ε (⇑(η' ω)) (((⌈‖z‖⌉₊ : ℕ) : ℝ) + B) ≤ ENNReal.ofReal (D ⌈‖z‖⌉₊) →
        (∀ k : ℕ, ω ∉ vertexPathFailure S η' ε (((⌈‖z‖⌉₊ : ℕ) : ℝ) + B + D ⌈‖z‖⌉₊)
          ((k : ℝ) + 1) (a ⌈‖z‖⌉₊ k) (δ ⌈‖z‖⌉₊ k)) →
        LevyProkhorov.probabilityMeasureHomeomorph (interpWalkLaw S η' ε ω z) ∈ K := fun z =>
    exists_isCompact_interpWalkLaw S η' z _ B (D _) (by linarith [hD1 ⌈‖z‖⌉₊]) (δ ⌈‖z‖⌉₊)
      (hδ0 _) (a ⌈‖z‖⌉₊) (ha1 _)
  choose K hKc hKP using hK
  refine ⟨K, hKc, fun n => ?_⟩
  have hgeo : ∑' m : ℕ, ENNReal.ofReal (ζ / 4 / 2 / 2 ^ m) = ENNReal.ofReal (ζ / 4) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (summable_geometric_two' _),
      tsum_geometric_two']
  set Bad : Set Ω := (⋃ m : ℕ, {ω | ENNReal.ofReal (D m) < maxCellDiam (eps n) (⇑(η' ω))
      ((m : ℝ) + B)}) ∪ ⋃ m : ℕ, ⋃ k : ℕ, vertexPathFailure S η' (eps n)
        ((m : ℝ) + B + D m) ((k : ℝ) + 1) (a m k) (δ m k) with hBad
  have hbad : S.P Bad ≤ ENNReal.ofReal ζ := by
    rw [hBad]
    refine (measure_union_le _ _).trans ?_
    have h1 : S.P (⋃ m : ℕ, {ω | ENNReal.ofReal (D m) < maxCellDiam (eps n) (⇑(η' ω))
        ((m : ℝ) + B)}) ≤ ENNReal.ofReal (ζ / 4) := by
      refine (measure_iUnion_le _).trans ?_
      rw [← hgeo]
      exact ENNReal.tsum_le_tsum fun m => hDP m n
    have h2 : S.P (⋃ m : ℕ, ⋃ k : ℕ, vertexPathFailure S η' (eps n)
        ((m : ℝ) + B + D m) ((k : ℝ) + 1) (a m k) (δ m k)) ≤ ENNReal.ofReal (ζ / 4) := by
      refine (measure_iUnion_le _).trans ?_
      rw [← hgeo]
      refine ENNReal.tsum_le_tsum fun m => (measure_iUnion_le _).trans ?_
      calc ∑' k : ℕ, S.P (vertexPathFailure S η' (eps n) ((m : ℝ) + B + D m) ((k : ℝ) + 1)
            (a m k) (δ m k))
          ≤ ∑' k : ℕ, ENNReal.ofReal (ζ / 4 / 2 / 2 ^ m / 2 / 2 ^ k) :=
            ENNReal.tsum_le_tsum fun k =>
              (hδP m k n).trans (ENNReal.ofReal_le_ofReal (ha2 m k))
        _ = ENNReal.ofReal (ζ / 4 / 2 / 2 ^ m) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
              (summable_geometric_two' _), tsum_geometric_two']
    calc _ ≤ ENNReal.ofReal (ζ / 4) + ENNReal.ofReal (ζ / 4) := add_le_add h1 h2
      _ = ENNReal.ofReal (ζ / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal ζ := ENNReal.ofReal_le_ofReal (by linarith)
  have hN : S.P {ω | ω ∉ properCurveSet η'} = 0 := ae_iff.1 hprop
  have hsub : {ω | ∃ z, interpWalkLawLP S η' (eps n) ω z ∉ K z} ⊆
      {ω | ω ∉ properCurveSet η'} ∪ Bad := by
    intro ω hω
    obtain ⟨z, hz⟩ := hω
    by_cases hpω : ω ∈ properCurveSet η'
    · by_cases hbω : ω ∈ Bad
      · exact Or.inr hbω
      · exfalso
        rw [hBad] at hbω
        simp only [mem_union, mem_iUnion, not_or, not_exists, mem_ofPred_eq, not_lt] at hbω
        exact hz (hKP z ω (eps n) hpω (hε0 n) (hB n) (Nat.le_ceil _) (hbω.1 _)
          fun k => hbω.2 _ k)
    · exact Or.inl hpω
  calc _ ≤ S.P ({ω | ω ∉ properCurveSet η'} ∪ Bad) := measure_mono hsub
    _ ≤ S.P {ω | ω ∉ properCurveSet η'} + S.P Bad := measure_union_le _ _
    _ ≤ ENNReal.ofReal ζ := by rw [hN, zero_add]; exact hbad

/-- **Tightness of the laws of the interpolated quenched walk laws in `C(ℂ, 𝒫(ContinuousPath ℂ))`**
(Lévy–Prokhorov topology on `𝒫`): for a mesh sequence `ε_n → 0`, if the vertex-indexed modulus of
the quenched walk laws is small with high probability for large `n` (`hEq`) and the vertex path
failure events are small with high probability for large `n` (`hEqPath`), then the family of laws
of `P̃^{ε_n}` is tight. -/
theorem isTightMeasureSet_interpWalkLawLP {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0))
    (hEq : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a)
    (hEqPath : ∀ R L a : ℝ, 0 < L → 0 < a → ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ᶠ n in atTop, S.P (vertexPathFailure S η' (eps n) R L a δ) ≤ ENNReal.ofReal a) :
    IsTightMeasureSet {ν : Measure C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map (interpWalkLawLP S η' (eps n))} := by
  obtain ⟨B, hB⟩ := hε.bddAbove_range
  have hBn : ∀ n, eps n ≤ B := fun n => hB ⟨n, rfl⟩
  refine isTightMeasureSet_map_of_kernelModuli_aemeasurable (fun _ : ℕ => S.P)
    (fun n => interpWalkLawLP S η' (eps n))
    (fun n => aemeasurable_interpWalkLawLP hS hη' hae (hε0 n)) (0 : ℂ) ?_ ?_
  · intro L hL
    obtain ⟨δ, hδ, h⟩ := exists_delta_forall_interpWalkLaw_modulus hS hη' hae hε0 hε hEq hL
    exact ⟨δ, hδ, fun n => h n⟩
  · intro ζ hζ
    exact exists_pointwise_compact_interpWalkLawLP hS hη' hae hε0 hε hBn hEqPath hζ

end MatedCRT.FirstPass.Derived
