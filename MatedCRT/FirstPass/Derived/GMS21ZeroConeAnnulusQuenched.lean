import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepair

/-!
# The annulus form of Lemma 3.5 of Gwynne–Miller–Sheffield from the quenched unit-scale convergence

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Lemma 3.5, lines 1327-1343) deduce the uniform-start invariance
principle at mesh `1/n` for the `0`-quantum cone from the invariance principle for the unit-mesh cells as the spatial
scale tends to `0`, through the random change of scale `R_b`. The written answer
`notes/fp-gaps/CODEX-MQ-sbl-30.md` ("Weaker annulus input", lines 47-60) isolates the input this deduction needs at
the level of the code of the weighted cell data: for `λ`-almost every unit-mesh weighted datum `w`, the weighted
uniform Lévy–Prokhorov error `E_A(s, w)` on the annulus `A = closedBall 0 ρ \ B_b(0)` tends to `0` as `s ↓ 0`
(line 47). With the scaling law of the weighted cell data and the measurability of the uniform errors for the
completions of their laws, this gives the annulus form (lines 49-60).

## Main declarations

* `ZeroConeQuenchedUnitScaleConvergence`: the quenched convergence of the unit-scale errors of the unit-mesh weighted
  data of the zero-cone curve on every annulus.
* `zeroConeAnnulusLPForm_of_quenchedUnitScaleConvergence`: this convergence, the scaling law of the weighted cell
  data and the measurability of the uniform errors give `ZeroConeAnnulusLPForm`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Quenched convergence of the unit-scale errors of the zero-cone weighted cell data** (the code-level premise of
the written answer `notes/fp-gaps/CODEX-MQ-sbl-30.md`, line 47: "For each needed `A = closedBall 0 ρ \ B_b(0)`, it
suffices that `E_A(s, w) → 0` as `s ↓ 0`, for `λ`-almost every `w`"; the unit-mesh invariance principle in the proof
of Lemma 3.5 of Gwynne–Miller–Sheffield, arXiv:1705.11161, lines 1327-1330). Truth-checked: TRUE for every `0 < γ < 2`
at the canonical model (written answer MQ-sbl-32, final answer `51-zero-cone-annulus-premise.md`).

For every measurable version `G` of the boundary-length pair of the zero-cone curve and all `0 < b < ρ`, for almost
every sample and phase `θ` under `P ⊗ Unif[0, 1]`, the uniform Lévy–Prokhorov error at spatial scale `ε`, over starts
in `closedBall 0 ρ \ B_b(0)`, of the walk on the unit-mesh weighted data of `t ↦ η₀(t + θ)` and the edge counts of
`t ↦ G(t + θ)` tends to `0` as `ε ↓ 0`. -/
def ZeroConeQuenchedUnitScaleConvergence
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G → ∀ b ρ : ℝ, 0 < b → b < ρ →
    ∀ᵐ p ∂P.prod zeroConePhase,
      Tendsto (fun ε => weightedUnitScaleError (closedBall (0 : ℂ) ρ \ ball 0 b) ε (phaseShiftedData η₀ G 1 p))
        (𝓝[>] 0) (𝓝 0)

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from the quenched unit-scale convergence and the scaling of
the weighted cell data** (written answer `notes/fp-gaps/CODEX-MQ-sbl-30.md`, lines 49-60). Let `w_n` be the unit-mesh
weighted data of the rescaled curve, which have the law `λ` of the unit-mesh weighted data, and `R_n → 0` the radii.
The mesh-`1/n` error equals the unit-mesh error of `w_n` at scale `R_n`, and the probability that it exceeds `δ` is
at most `P(R_n > r) + λ{sup_{0 < s ≤ r} E_A(s, w) > δ}`, which tends to `0` by the quenched convergence. On the regular
mesh data, an error below the threshold of `exists_mem_annulusSelectedLPData_of_uniformLPError_lt` gives the
Lévy–Prokhorov comparison at precision `c` on the annulus. -/
theorem zeroConeAnnulusLPForm_of_quenchedUnitScaleConvergence
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hq : ZeroConeQuenchedUnitScaleConvergence D hγ)
    (hscale : ZeroConeWeightedMeshScaling D hγ) (hmeas : ZeroConeWeightedUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  intro G hG α b ρ R c hα hαb hbρ hρR hc θ hθ
  have _hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  set A : Set ℂ := closedBall (0 : ℂ) ρ \ ball 0 b
  obtain ⟨δ, hδ, hgood⟩ := exists_mem_annulusSelectedLPData_of_uniformLPError_lt hα hαb hbρ hρR hc
  obtain ⟨hXm, hUm⟩ := hmeas G hG b ρ
  have hηm : Measurable η₀ := D.measurable_curves.2.2.1
  have hX1 : ∀ᵐ p ∂P.prod zeroConePhase,
      Tendsto (fun ε => weightedUnitScaleError A ε (phaseShiftedData η₀ G 1 p)) (𝓝[>] 0) (𝓝 0) :=
    hq G hG b ρ (hα.trans hαb) hbρ
  -- transfer to the law of the unit-mesh weighted data
  have hd1 : Measurable (phaseShiftedData η₀ G 1) := measurable_phaseShiftedData hηm hG.1 one_pos
  have hXμ : ∀ᵐ w ∂(P.prod zeroConePhase).map (phaseShiftedData η₀ G 1),
      Tendsto (fun ε => weightedUnitScaleError A ε w) (𝓝[>] 0) (𝓝 0) :=
    ae_tendsto_map_of_ae_tendsto hd1.aemeasurable (weightedUnitScaleError A) hXm hX1
  -- the random change of scale (Lemma 3.5), indexed from `n + 1`
  obtain ⟨Rs, E, hRm, hEm, hR0, hrel⟩ := hscale G hG
  set H : ℕ → Ω × ℝ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ) := fun n p =>
    (phaseShiftedCurve 1 p.2 (E (n + 1) p.1),
      phaseShiftedEdgeCount (1 / ((n + 1 : ℕ) : ℝ)) p.2 (G p.1)) with hHdef
  have hHm : ∀ n, Measurable (H n) := fun n =>
    measurable_phaseShiftedPair (hEm (n + 1)) hG.1 1
      (one_div_pos.2 (Nat.cast_pos.2 (Nat.succ_pos n)))
  have hHlaw : ∀ n, (P.prod zeroConePhase).map (H n) =
      (P.prod zeroConePhase).map (phaseShiftedData η₀ G 1) := fun n =>
    (hrel (n + 1) (Nat.succ_pos n)).2.2
  have hR0' : ∀ᵐ p ∂P.prod zeroConePhase, Tendsto (fun n => Rs (n + 1) p.1) atTop (𝓝 0) :=
    Measure.quasiMeasurePreserving_fst.ae
      (hR0.mono fun _ h => h.comp (tendsto_add_atTop_nat 1))
  have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (half_pos hδ)
  have hconvP := tendsto_measure_lt_scaleChange (weightedUnitScaleError A) H
    (fun n (p : Ω × ℝ) => Rs (n + 1) p.1) hHm hHlaw hXμ hXm
    (fun n => (hRm (n + 1)).comp measurable_fst) hR0'
    (fun n => Measure.quasiMeasurePreserving_fst.ae (hrel (n + 1) (Nat.succ_pos n)).1) hδ2
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hconvP) _ (ENNReal.ofReal_pos.2 hθ))
  refine ⟨N₁ + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hbad := hN₁ k (by omega)
  have hn1 : 0 < k + 1 := Nat.succ_pos k
  have hpos : (0 : ℝ) < 1 / ((k + 1 : ℕ) : ℝ) := one_div_pos.2 (Nat.cast_pos.2 hn1)
  set d : Ω × ℝ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ) := phaseShiftedData η₀ G (1 / ((k + 1 : ℕ) : ℝ)) with hddef
  change (P.prod zeroConePhase).map d
    (annulusSelectedLPData (1 / ((k + 1 : ℕ) : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ
  have hdm : AEMeasurable d (P.prod zeroConePhase) :=
    (measurable_phaseShiftedData hηm hG.1 hpos).aemeasurable
  -- the bad set is contained in the irregular data and the large errors
  have hsub : (annulusSelectedLPData (1 / ((k + 1 : ℕ) : ℝ)) α b ρ R c)ᶜ ⊆
      regularDataᶜ ∪ {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x} := by
    intro x hx
    rw [mem_union]
    by_cases hreg : x ∈ regularData
    · refine Or.inr ?_
      show ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x
      by_contra hlt
      exact (mem_compl_iff _ _).1 hx
        (hgood (1 / ((k + 1 : ℕ) : ℝ)) hpos x hreg.1.1 hreg.2.1 hreg.2.2 (not_le.1 hlt))
    · exact Or.inl hreg
  have hZ : (P.prod zeroConePhase).map d regularDataᶜ = 0 := by
    rw [Measure.map_apply₀ hdm measurableSet_regularData.compl.nullMeasurableSet]
    have h0 := ae_iff.1 (ae_mem_regularData_phaseShifted D hγ hf hG hpos)
    exact h0
  have hnull : NullMeasurableSet {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x}
      ((P.prod zeroConePhase).map d) := nullMeasurableSet_le aemeasurable_const (hUm (k + 1) hn1)
  have hUle : (P.prod zeroConePhase).map d
        {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x} ≤
      (P.prod zeroConePhase)
        {p | ENNReal.ofReal (δ / 2) < weightedUnitScaleError A (Rs (k + 1) p.1) (H k p)} := by
    rw [Measure.map_apply₀ hdm hnull]
    refine measure_mono_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hrel (k + 1) hn1).2.1] with p hp hpU
    have heq : meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) (d p) =
        weightedUnitScaleError A (Rs (k + 1) p.1) (H k p) :=
      meshUniformError_phaseShifted_eq_weightedUnitScaleError A hn1 p.2 hp _
    have hpU' : ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) (d p) := hpU
    show ENNReal.ofReal (δ / 2) < weightedUnitScaleError A (Rs (k + 1) p.1) (H k p)
    rw [← heq]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ).2 (half_lt_self hδ)) hpU'
  calc (P.prod zeroConePhase).map d (annulusSelectedLPData (1 / ((k + 1 : ℕ) : ℝ)) α b ρ R c)ᶜ
      ≤ (P.prod zeroConePhase).map d (regularDataᶜ ∪
          {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x}) := measure_mono hsub
    _ ≤ (P.prod zeroConePhase).map d regularDataᶜ + (P.prod zeroConePhase).map d
          {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / ((k + 1 : ℕ) : ℝ)) x} :=
        measure_union_le _ _
    _ ≤ 0 + (P.prod zeroConePhase)
          {p | ENNReal.ofReal (δ / 2) < weightedUnitScaleError A (Rs (k + 1) p.1) (H k p)} :=
      add_le_add hZ.le hUle
    _ ≤ ENNReal.ofReal θ := by
      rw [zero_add]
      exact hbad

end ZeroCone

end MatedCRT.GMS310Transfer
