import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulus

/-!
# The annulus form of Lemma 3.5 of Gwynne–Miller–Sheffield from the scaling of the weighted cell data

Gwynne–Miller–Sheffield (arXiv:1705.11161, Lemma 3.5, lines 1319-1343) compare the mesh-`1/n` cells of the
`0`-quantum cone with the unit-mesh cells of the rescaled pair `(h^b, η^b)`, `b = 1/n`, dilated by `R_b`. The written
answer on this step (`notes/fp-gaps/CODEX-MQ-sbl-22.md`, lines 41-54) states the scaling law in the form used by the
proof: the rescaled curve `η^b(t) = R_b⁻¹ η₀(b t)` together with the integer edge counts of the original `b`-mesh
intervals (the *weighted* unit-mesh data at the phase `θ`) has the law of the unit-mesh weighted data of `η₀`
(line 53: "the rescaled *weighted* unit-mesh data have the original law and their dilation is the original `b`-mesh
data. This suffices for the uniform walk error"). The measurability of the uniform errors (lines 55-60) holds for the
completions of the laws of these data.

## Main declarations

* `phaseShiftedData`: the curve and the edge counts read on the lattice `ε ℤ + ε θ`.
* `weightedUnitScaleError`: the uniform error at spatial scale `ε` of a unit-mesh weighted datum.
* `ZeroConeWeightedMeshScaling`: the scaling law of the weighted cell data (answer, lines 43 and 53).
* `ZeroConeWeightedUniformErrorMeasurability`: the measurability of the uniform errors for the completions of the
  laws of the weighted data (answer, lines 57-59).
* `zeroConeAnnulusLPForm_of_theorem310Form_code`: these two steps, the realization of the configuration, its rotation
  invariance and the conclusion of Theorem 3.10 of arXiv:1807.07515 at the law of every realization give
  `ZeroConeAnnulusLPForm`.
* `zeroConeAnnulusLPForm_of_theorem310_code`: the same from Theorem 3.10 and the hypotheses of
  `zeroConeAnnulusLPForm_of_theorem310`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

/-- The **weighted data at mesh `ε` and phase `θ`**: the curve `t ↦ η(t + ε θ)` and the contour edge counts at mesh
`ε` of `t ↦ G(t + ε θ)`. -/
def phaseShiftedData {Ω : Type*} (η : Ω → C(ℝ, ℂ)) (G : Ω → Path2) (ε : ℝ) (p : Ω × ℝ) :
    C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (phaseShiftedCurve ε p.2 (η p.1), phaseShiftedEdgeCount ε p.2 (G p.1))

/-- The **uniform error at spatial scale `ε` of a unit-mesh weighted datum** `(η, m)`: the uniform Lévy–Prokhorov
error over starts in `A` of the walk on `m` with the cells and vertices at mesh `1` of the curve `ε η`. -/
def weightedUnitScaleError (A : Set ℂ) (ε : ℝ≥0) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : ℝ≥0∞ :=
  unitScaleError A ε w.1 w.2

/-- A curve read on the lattice `ε ℤ + ε θ` together with edge counts read on the lattice `ε' ℤ + ε' θ`, `ε' > 0`, is
jointly measurable in the sample and the phase. -/
theorem measurable_phaseShiftedPair {Ω : Type*} [MeasurableSpace Ω] {η : Ω → C(ℝ, ℂ)} {G : Ω → Path2}
    (hη : Measurable η) (hG : Measurable G) (ε : ℝ) {ε' : ℝ} (hε' : 0 < ε') :
    Measurable fun p : Ω × ℝ => (phaseShiftedCurve ε p.2 (η p.1), phaseShiftedEdgeCount ε' p.2 (G p.1)) := by
  have hcurve : Continuous fun q : C(ℝ, ℂ) × ℝ => phaseShiftedCurve ε q.2 q.1 := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    change Continuous fun q : (C(ℝ, ℂ) × ℝ) × ℝ => q.1.1 (q.2 + ε * q.1.2)
    fun_prop
  have hpm : Measurable fun p : Ω × ℝ => (G p.1, (⟨ε', hε'⟩ : {ε : ℝ // 0 < ε}), p.2) :=
    (hG.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have hcm : Measurable fun p : Ω × ℝ => (η p.1, p.2) :=
    (hη.comp measurable_fst).prodMk measurable_snd
  have h1 := hcurve.measurable.comp hcm
  have h2 := measurable_bmEdgeCount_shiftedMesh_array.comp hpm
  exact h1.prodMk h2

/-- The weighted data at a positive mesh are jointly measurable in the sample and the phase. -/
theorem measurable_phaseShiftedData {Ω : Type*} [MeasurableSpace Ω] {η : Ω → C(ℝ, ℂ)} {G : Ω → Path2}
    (hη : Measurable η) (hG : Measurable G) {ε : ℝ} (hε : 0 < ε) :
    Measurable (phaseShiftedData η G ε) :=
  measurable_phaseShiftedPair hη hG ε hε

/-- **Scaling of the uniform error with retained edge counts** (arXiv:1705.11161, lines 1336-1342; answer
`notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 53: "the rescaled unit cells are exactly `R_b⁻¹ η₀(b[j − 1 + θ, j + θ])`").
If `η₀(t/n) = R e(t)`, the uniform error at mesh `1/n` of the curve `η₀` read on the lattice `n⁻¹ ℤ + n⁻¹ θ` with
edge counts `m` is the uniform error at spatial scale `R` of the unit-mesh datum `(e(· + θ), m)`. -/
theorem meshUniformError_phaseShifted_eq_weightedUnitScaleError (A : Set ℂ) {n : ℕ} (hn : 0 < n) (θ : ℝ)
    {η₀ e₁ : C(ℝ, ℂ)} {R : ℝ≥0} (h₁ : ∀ t, η₀ (t / n) = (R : ℝ) • e₁ t) (m : ℤ → ℤ → ℕ) :
    meshUniformError A (1 / (n : ℝ)) (phaseShiftedCurve (1 / (n : ℝ)) θ η₀, m) =
      weightedUnitScaleError A R (phaseShiftedCurve 1 θ e₁, m) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hb : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.2 hn'
  unfold meshUniformError weightedUnitScaleError unitScaleError
  congr 1
  · funext k
    have hη : ∀ s : ℝ, ((R : ℝ) : ℂ) * e₁ (s + 1 * θ) =
        (1 : ℂ)⁻¹ * η₀ (1 / (n : ℝ) * s + 1 / (n : ℝ) * θ) := by
      intro s
      rw [inv_one, one_mul (η₀ (1 / (n : ℝ) * s + 1 / (n : ℝ) * θ)), ← Complex.real_smul, ← h₁]
      congr 1
      ring
    have key := cell_rescale_image (ε := 1 / (n : ℝ)) hb one_ne_zero
      (fun t => η₀ (t + 1 / (n : ℝ) * θ)) (fun t => ((R : ℝ) : ℂ) * e₁ (t + 1 * θ)) hη k
    rw [div_self hb.ne', inv_one] at key
    have hid : (fun z : ℂ => 1 * z) = id := funext one_mul
    rw [hid, Set.image_id] at key
    exact key.symm
  · funext k
    show η₀ (1 / (n : ℝ) * k + 1 / (n : ℝ) * θ) = ((R : ℝ) : ℂ) * e₁ (1 * k + 1 * θ)
    rw [← Complex.real_smul, ← h₁]
    congr 1
    ring

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Scaling of the weighted cell data of the zero-cone curve** (arXiv:1705.11161, Lemma 3.5, lines 1331-1343;
written answer `notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 43: "Its radius `R_b` is the largest positive solution of
`h_{0,r}(0) + Q log r = γ⁻¹ log b` ... These hitting times are Borel, finite and tend to infinity as `b ↓ 0` ...
`η^b(t) = R_b⁻¹ η₀(b t)`. All these path variables admit raw measurable versions; countably many `b = 1/n` share one
event"; line 53: "Retain the scaled curve and the integer edge counts for its intervals. For the phase `θ` the
rescaled unit cells are exactly `R_b⁻¹ η₀(b[j − 1 + θ, j + θ])`. Nontrivial common boundary arcs and multiplicities
are preserved by this dilation. Thus the rescaled *weighted* unit-mesh data have the original law and their dilation
is the original `b`-mesh data"; DMS, arXiv:1409.7055, Proposition 4.13(i)).

For every measurable version `G` of the boundary-length pair there are measurable radii `R_n` tending to `0` almost
surely and measurable curves `E_n` such that, for `n ≥ 1`, `R_n > 0` and `η₀(t/n) = R_n E_n(t)` almost surely, and
the curve `t ↦ E_n(t + θ)` with the edge counts at mesh `1/n` of `t ↦ G(t + θ/n)` has, under `P ⊗ Unif[0, 1]`, the
law of the curve `t ↦ η₀(t + θ)` with the edge counts at mesh `1` of `t ↦ G(t + θ)`. -/
def ZeroConeWeightedMeshScaling (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∃ (Rsc : ℕ → Ω → ℝ≥0) (E : ℕ → Ω → C(ℝ, ℂ)),
      (∀ n, Measurable (Rsc n)) ∧ (∀ n, Measurable (E n)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Rsc n ω) atTop (𝓝 0)) ∧
      ∀ n : ℕ, 0 < n → (∀ᵐ ω ∂P, 0 < Rsc n ω) ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ, η₀ ω (t / (n : ℝ)) = (Rsc n ω : ℝ) • E n ω t) ∧
        (P.prod zeroConePhase).map (fun p => (phaseShiftedCurve 1 p.2 (E n p.1),
            phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1))) =
          (P.prod zeroConePhase).map (phaseShiftedData η₀ G 1)

/-- **Measurability of the uniform errors for the completions of the laws of the weighted data** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-22.md`, lines 57-59: "In the unit case the strict superlevel event of the scale supremum
is the projection of the Borel event that there exist `0 < s ≤ ε₀`, `z ∈ A`, `j ∈ ℤ` attaining an error strictly
above the threshold with `z ∈ s K_j`. In the mesh case omit `s` and use the fixed `1/n` cells. The parameter and data
spaces are standard Borel, so these projections are analytic, hence measurable in the completion of each indicated
law"; Kechris, Theorem 21.10).

On the annuli `closedBall 0 ρ \ B_b(0)`, the scale suprema of the unit-mesh error of the weighted data are almost
measurable for the law of the unit-mesh weighted data of `(η₀, G)`, and the mesh-`1/n` error is almost measurable for
the law of the weighted data at mesh `1/n`. -/
def ZeroConeWeightedUniformErrorMeasurability
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G → ∀ b ρ : ℝ,
    (∀ ε₀ : ℝ≥0, AEMeasurable (scaleSup (weightedUnitScaleError (closedBall (0 : ℂ) ρ \ ball 0 b)) ε₀)
        ((P.prod zeroConePhase).map (phaseShiftedData η₀ G 1))) ∧
      ∀ n : ℕ, 0 < n →
        AEMeasurable (meshUniformError (closedBall (0 : ℂ) ρ \ ball 0 b) (1 / (n : ℝ)))
          ((P.prod zeroConePhase).map (phaseShiftedData η₀ G (1 / (n : ℝ))))

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from the conclusion of Theorem 3.10 and the scaling of the
weighted cell data.** If the conclusion of Theorem 3.10 of arXiv:1807.07515 holds at the law of every realization of
the shifted zero-cone configuration, then, given the realization, its rotation invariance, the scaling law of the
weighted cell data and the measurability of the uniform errors for the completions of their laws, the shifted
zero-cone data at mesh `1/n` satisfy the annulus form of the uniform-start invariance principle. -/
theorem zeroConeAnnulusLPForm_of_theorem310Form_code
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (h310 : ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
      GMSTheorem310Form ((P.prod zeroConePhase).map F))
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (hscale : ZeroConeWeightedMeshScaling D hγ) (hmeas : ZeroConeWeightedUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  intro G hG α b ρ R c hα hαb hbρ hρR hc θ hθ
  have hPprob : IsProbabilityMeasure P := D.isProbabilityMeasure
  set A : Set ℂ := closedBall (0 : ℂ) ρ \ ball 0 b
  have hA : IsCompact A := (isCompact_closedBall (0 : ℂ) ρ).diff isOpen_ball
  obtain ⟨δ, hδ, hgood⟩ := exists_mem_annulusSelectedLPData_of_uniformLPError_lt hα hαb hbρ hρR hc
  obtain ⟨hXm, hUm⟩ := hmeas G hG b ρ
  have hηm : Measurable η₀ := D.measurable_curves.2.2.1
  -- the unit-mesh configuration: almost sure uniform convergence with an isotropic limit
  obtain ⟨F, hF⟩ := hreal G hG
  have hFm : AEMeasurable F (P.prod zeroConePhase) := hF.2.2.1
  have hμF : IsProbabilityMeasure ((P.prod zeroConePhase).map F) :=
    (Measure.isProbabilityMeasure_map_iff hFm).2 inferInstance
  obtain ⟨target, hconv, hunif⟩ := h310 G F hF
  obtain ⟨c₀, hc₀, hcov₀⟩ := covariance_eq_smul_one_of_map_quarterTurn (hrot G F hF)
    (connectedAlongLines_map_of_zeroConeConfigRealization D hγ hf hF) hconv
  have hunifP := ae_of_ae_map hFm hunif
  have hX1 : ∀ᵐ p ∂P.prod zeroConePhase,
      Tendsto (fun ε => weightedUnitScaleError A ε (phaseShiftedData η₀ G 1 p)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hunifP, ae_mem_regularData_phaseShifted D hγ hf hG one_pos, hF.2.2.2]
      with p hu hreg hFp
    obtain ⟨h, hFeq⟩ := hFp
    exact tendsto_unitScaleError_of_theorem310 h p.2
      (bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1) (fun t => (G p.1 (t + 1 * p.2)).2))
      hreg.2.1 hreg.2.2 (F p) hFeq target hc₀ hcov₀ hu hA
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

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from Theorem 3.10 of arXiv:1807.07515 and the scaling of
the weighted cell data.** Under the hypotheses of `exists_zeroCone_config_gmsHypotheses_of_lemmaA1`, the law of every
realization of the shifted zero-cone configuration satisfies the four hypotheses of Theorem 1.16 of
arXiv:1807.07515, so Theorem 3.10 applies to it; with the realization, its rotation invariance, the scaling law of the
weighted cell data and the measurability of the uniform errors this gives the annulus form of the uniform-start
invariance principle for the shifted zero-cone data at mesh `1/n`. -/
theorem zeroConeAnnulusLPForm_of_theorem310_code
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1 D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) (h310 : GMSTheorem310)
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (hscale : ZeroConeWeightedMeshScaling D hγ)
    (hmeas : ZeroConeWeightedUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  have hT := zeroConeTailTriviality_of_lemmaA1 D hγ hA1 hcov hlaw hcurve hphase
  refine zeroConeAnnulusLPForm_of_theorem310Form_code D hγ hf (fun G F hF => ?_) hreal hrot hscale hmeas
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have : IsProbabilityMeasure ((P.prod zeroConePhase).map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.2.2.1).2 inferInstance
  exact h310 _ (massTransport_map_of_zeroConeSpatialAverageInvariance D hγ hI h25 hF)
    (ergodicModuloScaling_map_of_zeroConeTailTriviality D hγ hT hF)
    (finiteExpectation_map_of_zeroConeConfigRealization D hγ hF)
    (connectedAlongLines_map_of_zeroConeConfigRealization D hγ hf hF)

end ZeroCone

end MatedCRT.GMS310Transfer
