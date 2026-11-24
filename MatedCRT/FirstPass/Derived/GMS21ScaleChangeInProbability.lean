import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Random change of scale: from almost sure convergence to convergence in probability

Gwynne–Miller–Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity* (arXiv 1705.11161), proof of Lemma 3.5. There the cell configuration `H` of unit-mass
cells of a `0`-quantum cone satisfies an invariance principle at every spatial scale `ε → 0`, almost
surely and uniformly over starting points in a compact set; the mated-CRT map `G^b` with cells of
mass `b` is isometric to `R_b H^b`, where `(h^b, η^b) := (h(R_b ·) + Q log R_b − γ⁻¹ log b,
R_b⁻¹ η(b ·))` has the law of `(h, η)` (so `H^b` has the law of `H`) and `R_b → 0` almost surely as
`b → 0`. "Setting `b = 1/n`, we now get the desired convergence in probability."

This file proves that last step for an abstract error functional:

* `X ε s` is the error at spatial scale `ε` of the configuration `s` (in the application: the
  supremum over starting points in a compact set of the Prokhorov distance between the walk on
  `ε s` and Brownian motion);
* `H n` has law `μ` for every `n`, and `μ`-almost every configuration has error tending to `0` as
  `ε → 0`;
* `R n → 0` almost surely, `R n > 0` almost surely.

Then the error `X (R n) (H n)` of the configuration at the random scale tends to `0` in (outer)
probability (`tendsto_measure_lt_scaleChange`). The only regularity premise is the almost
everywhere measurability, under the law `μ`, of the scale supremum `sup_{0 < ε ≤ ε₀} X ε`; no
measurability of the event `{δ < X (R n) (H n)}` is required.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

/-- **Outer-measure transport along a measurable map.** For a measurable `f` and an arbitrary set
`B`, the outer probability of `f ⁻¹' B` is at most the outer measure of `B` under the image law. -/
theorem measure_preimage_le_map_apply {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) {f : Ω → S} (hf : Measurable f) (B : Set S) :
    P (f ⁻¹' B) ≤ P.map f B :=
  calc P (f ⁻¹' B) ≤ P (f ⁻¹' toMeasurable (P.map f) B) :=
        measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ = P.map f (toMeasurable (P.map f) B) :=
        (Measure.map_apply hf (measurableSet_toMeasurable _ _)).symm
    _ = P.map f B := measure_toMeasurable B

/-- The scale supremum `sup_{0 < ε ≤ ε₀} X ε s` of an error functional. -/
def scaleSup {S : Type*} (X : ℝ≥0 → S → ℝ≥0∞) (ε₀ : ℝ≥0) (s : S) : ℝ≥0∞ :=
  ⨆ ε ∈ Ioc (0 : ℝ≥0) ε₀, X ε s

theorem le_scaleSup {S : Type*} (X : ℝ≥0 → S → ℝ≥0∞) {ε ε₀ : ℝ≥0} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (s : S) : X ε s ≤ scaleSup X ε₀ s :=
  le_iSup₂_of_le (f := fun ε (_ : ε ∈ Ioc (0 : ℝ≥0) ε₀) => X ε s) ε ⟨hε, hεε₀⟩ le_rfl

theorem scaleSup_mono {S : Type*} (X : ℝ≥0 → S → ℝ≥0∞) {a b : ℝ≥0} (hab : a ≤ b) (s : S) :
    scaleSup X a s ≤ scaleSup X b s :=
  iSup₂_le fun _ hε => le_scaleSup X hε.1 (hε.2.trans hab) s

/-- If the error of `s` tends to `0` at small scales, the scale supremum is eventually below any
positive level. -/
theorem exists_scaleSup_le_of_tendsto {S : Type*} (X : ℝ≥0 → S → ℝ≥0∞) {s : S}
    (hs : Tendsto (fun ε => X ε s) (𝓝[>] 0) (𝓝 0)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ k : ℕ, scaleSup X (1 / ((k : ℝ≥0) + 1)) s ≤ δ := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), X ε s < δ := hs.eventually (gt_mem_nhds hδ)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ≥0) < u := hu
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hu0
  refine ⟨k, iSup₂_le fun ε hε => ?_⟩
  exact (hsub (show ε ∈ Ioo 0 u from ⟨hε.1, lt_of_le_of_lt hε.2 hk⟩) : X ε s < δ).le

/-- **The scale supremum tends to `0` in measure** when the error tends to `0` almost
everywhere. -/
theorem tendsto_measure_lt_scaleSup {S : Type*} [MeasurableSpace S] {μ : Measure S}
    [IsFiniteMeasure μ] (X : ℝ≥0 → S → ℝ≥0∞)
    (hX : ∀ᵐ s ∂μ, Tendsto (fun ε => X ε s) (𝓝[>] 0) (𝓝 0))
    (hXm : ∀ ε₀ : ℝ≥0, AEMeasurable (scaleSup X ε₀) μ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => μ {s | δ < scaleSup X (1 / ((k : ℝ≥0) + 1)) s}) atTop (𝓝 0) := by
  set A : ℕ → Set S := fun k => {s | δ < scaleSup X (1 / ((k : ℝ≥0) + 1)) s}
  have hAm : ∀ k, NullMeasurableSet (A k) μ := fun k =>
    (hXm (1 / ((k : ℝ≥0) + 1))).nullMeasurableSet_preimage
      (measurableSet_Ioi : MeasurableSet (Ioi δ))
  have hanti : Antitone A := by
    intro k l hkl s hs
    have hs' : δ < scaleSup X (1 / ((l : ℝ≥0) + 1)) s := hs
    show δ < scaleSup X (1 / ((k : ℝ≥0) + 1)) s
    refine lt_of_lt_of_le hs' (scaleSup_mono X ?_ s)
    have hkl' : (k : ℝ≥0) + 1 ≤ (l : ℝ≥0) + 1 := by
      have : (k : ℝ≥0) ≤ (l : ℝ≥0) := by exact_mod_cast hkl
      exact add_le_add this le_rfl
    exact one_div_le_one_div_of_le (by positivity) hkl'
  have hnull : μ (⋂ k, A k) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hX)
    intro s hs hconv
    obtain ⟨k, hk⟩ := exists_scaleSup_le_of_tendsto X hconv hδ
    have hsk : δ < scaleSup X (1 / ((k : ℝ≥0) + 1)) s := mem_iInter.1 hs k
    exact (not_lt.2 hk) hsk
  have h := tendsto_measure_iInter_atTop hAm hanti ⟨0, measure_ne_top μ _⟩
  rw [hnull] at h
  exact h

/-- **A random scale tending to `0` almost surely exceeds any positive level with probability
tending to `0`.** -/
theorem tendsto_measure_lt_of_ae_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (R : ℕ → Ω → ℝ≥0) (hRm : ∀ n, Measurable (R n))
    (hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 0)) {ε₀ : ℝ≥0} (hε₀ : 0 < ε₀) :
    Tendsto (fun n => P {ω | ε₀ < R n ω}) atTop (𝓝 0) := by
  set C : ℕ → Set Ω := fun m => ⋃ n : ℕ, R (n + m) ⁻¹' Ioi ε₀
  have hCm : ∀ m, NullMeasurableSet (C m) P := fun m =>
    (MeasurableSet.iUnion fun n => hRm (n + m) measurableSet_Ioi).nullMeasurableSet
  have hanti : Antitone C := by
    intro m m' hmm' ω hω
    obtain ⟨n, hn⟩ := mem_iUnion.1 hω
    refine mem_iUnion.2 ⟨n + (m' - m), ?_⟩
    have he : n + (m' - m) + m = n + m' := by omega
    rw [he]
    exact hn
  have hnull : P (⋂ m, C m) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hR)
    intro ω hω hconv
    obtain ⟨m, hm⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds hε₀))
    obtain ⟨n, hn⟩ := mem_iUnion.1 (mem_iInter.1 hω m)
    have hn' : ε₀ < R (n + m) ω := hn
    exact lt_asymm (hm (n + m) (Nat.le_add_left m n)) hn'
  have h := tendsto_measure_iInter_atTop hCm hanti ⟨0, measure_ne_top P _⟩
  rw [hnull] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) ?_
  intro m
  show P {ω | ε₀ < R m ω} ≤ P (C m)
  refine measure_mono fun ω hω => mem_iUnion.2 ⟨0, ?_⟩
  rw [Nat.zero_add]
  exact hω

/-- **GMS21, proof of Lemma 3.5: a random change of scale turns almost sure convergence into
convergence in probability.** Let `H n` be random configurations with the common law `μ`, let
`μ`-almost every configuration have error `X ε s → 0` as `ε → 0` (the uniform-start invariance
principle at every spatial scale), and let the random scales `R n` be positive and tend to `0`
almost surely. If the scale supremum `sup_{0 < ε ≤ ε₀} X ε` is `μ`-a.e. measurable for every
`ε₀`, then the error `X (R n) (H n)` of `H n` at the random scale `R n` tends to `0` in outer
probability. -/
theorem tendsto_measure_lt_scaleChange {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S}
    (X : ℝ≥0 → S → ℝ≥0∞) (H : ℕ → Ω → S) (R : ℕ → Ω → ℝ≥0)
    (hH : ∀ n, Measurable (H n)) (hlaw : ∀ n, P.map (H n) = μ)
    (hX : ∀ᵐ s ∂μ, Tendsto (fun ε => X ε s) (𝓝[>] 0) (𝓝 0))
    (hXm : ∀ ε₀ : ℝ≥0, AEMeasurable (scaleSup X ε₀) μ)
    (hRm : ∀ n, Measurable (R n))
    (hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 0))
    (hRpos : ∀ n, ∀ᵐ ω ∂P, 0 < R n ω)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ < X (R n ω) (H n ω)}) atTop (𝓝 0) := by
  have hμfin : IsFiniteMeasure μ := by
    rw [← hlaw 0]
    infer_instance
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  -- choose the scale cut-off `ε₀ = 1/(k+1)` from the almost sure convergence of the errors
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1
    (tendsto_measure_lt_scaleSup X hX hXm hδ)) (η / 2) hη2).exists
  have hε₀pos : (0 : ℝ≥0) < 1 / ((k : ℝ≥0) + 1) := by positivity
  set ε₀ : ℝ≥0 := 1 / ((k : ℝ≥0) + 1)
  -- the random scale is eventually below `ε₀` with probability close to `1`
  have hRev := (ENNReal.tendsto_nhds_zero.1
    (tendsto_measure_lt_of_ae_tendsto_zero R hRm hR hε₀pos)) (η / 2) hη2
  filter_upwards [hRev] with n hn
  have hsub : {ω | δ < X (R n ω) (H n ω)} ⊆
      ({ω | ¬ 0 < R n ω} ∪ {ω | ε₀ < R n ω}) ∪ H n ⁻¹' {s | δ < scaleSup X ε₀ s} := by
    intro ω hω
    by_cases hpos : 0 < R n ω
    · by_cases hle : R n ω ≤ ε₀
      · exact Or.inr (lt_of_lt_of_le hω (le_scaleSup X hpos hle (H n ω)))
      · exact Or.inl (Or.inr (not_le.1 hle))
    · exact Or.inl (Or.inl hpos)
  have hzero : P {ω | ¬ 0 < R n ω} = 0 := ae_iff.1 (hRpos n)
  calc P {ω | δ < X (R n ω) (H n ω)}
      ≤ P (({ω | ¬ 0 < R n ω} ∪ {ω | ε₀ < R n ω}) ∪
          H n ⁻¹' {s | δ < scaleSup X ε₀ s}) := measure_mono hsub
    _ ≤ (P {ω | ¬ 0 < R n ω} + P {ω | ε₀ < R n ω}) +
          P (H n ⁻¹' {s | δ < scaleSup X ε₀ s}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (0 + η / 2) + μ {s | δ < scaleSup X ε₀ s} := by
        rw [hzero]
        refine add_le_add (add_le_add le_rfl hn) ?_
        rw [← hlaw n]
        exact measure_preimage_le_map_apply P (hH n) _
    _ ≤ (0 + η / 2) + η / 2 := add_le_add le_rfl hk
    _ = η := by rw [zero_add, ENNReal.add_halves]

end MatedCRT
