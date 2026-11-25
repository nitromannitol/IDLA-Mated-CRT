import MatedCRT.FirstPass.Derived.GMS21ZeroConeScalingData
import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1
import MatedCRT.FirstPass.Derived.ZeroConeFiniteExpectation
import MatedCRT.FirstPass.Derived.GMSConditionTwoImpliesFive
import MatedCRT.FirstPass.Derived.ZeroConeConnectedAlongLines
import MatedCRT.FirstPass.Derived.GMS21CellConfigRotationContinuous
import MatedCRT.FirstPass.Derived.GMS21Theorem310Form
import MatedCRT.FirstPass.Derived.GMS21ZeroConeUniformError
import MatedCRT.FirstPass.Derived.GMS21ScaleChangeInProbability
import MatedCRT.FirstPass.Derived.JointShiftedMeshMultiplicity

/-!
# The annulus form of the uniform-start invariance principle for the shifted zero-cone configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161), Lemma 3.5 (lines 1319-1343): Theorem 3.4 holds in case 1 for the
configuration of the cells `η₀([x - 1 + θ, x + θ])` read on the lattice `n⁻¹ ℤ + n⁻¹ θ`, `θ` an independent uniform
phase. The proof combines

* Proposition 3.1 with Theorem 1.7 of arXiv:1807.07515 (here the second conclusion of Theorem 3.10 of
  arXiv:1807.07515, `GMSTheorem310Form`, lines 1328-1331): almost surely the walk on the unit-mesh configuration,
  dilated by `ε`, converges to Brownian motion uniformly in the start in a compact set, with an isotropic limit
  since the law of `(h, η)` is invariant under rotations about the origin (lines 1212-1213);
* the scale invariance of the circle-average embedding (lines 1336-1343): for `b = 1/n`, the pair
  `(R_b⁻¹ η₀(b ·), b^{-1/2} G(b ·))` has the law of `(η₀, G)`, and `R_b → 0` almost surely, so the mesh-`1/n`
  configuration is the unit-mesh configuration of an equally distributed pair dilated by `R_b`.

Main declarations:

* `ZeroConeConfigRealizable`, `ZeroConeConfigRotationInvariance`, `ZeroConeAreaScaling`,
  `ZeroConeUniformErrorMeasurability`: the named steps of the printed proof (the realization of the configuration as
  a random element of the GMS space, line 1127; the rotation invariance, lines 1212-1213; the scale invariance,
  lines 1336-1343; the measurability of the uniform Lévy–Prokhorov errors, used without comment in "convergence in
  probability", line 1343).
* `zeroConeAnnulusLPForm_of_theorem310Form`: these steps and the conclusion of Theorem 3.10 at the law of every
  realization give `ZeroConeAnnulusLPForm`.
* `zeroConeAnnulusLPForm_of_theorem310`: the same from Theorem 3.10 (`GMSTheorem310`) and the hypotheses of
  `exists_zeroCone_config_gmsHypotheses_of_lemmaA1`, which give the four GMS hypotheses at every realization.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

/-- The **unit-mesh uniform error at spatial scale `ε`** of a datum `((η, G), θ)`: the uniform Lévy–Prokhorov error
over starts in `A` of the walk on the contour edge counts at mesh `1` of `t ↦ G(t + θ)`, with the vertices
`ε η(x + θ)`, against planar Brownian motion. -/
def unitScaleConfigError (A : Set ℂ) (ε : ℝ≥0)
    (s : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ) : ℝ≥0∞ :=
  unitScaleError A ε (fun t => s.1.1 (t + 1 * s.2))
    (bmEdgeCount 1 (fun t => (s.1.2 (t + 1 * s.2)).1) (fun t => (s.1.2 (t + 1 * s.2)).2))

/-- The **uniform error at mesh `ε`** of a datum (curve, multigraph): the uniform Lévy–Prokhorov error over starts in
`A` of the walk on the multigraph with the cells and vertices of the curve at mesh `ε`. -/
def meshUniformError (A : Set ℂ) (ε : ℝ) (d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : ℝ≥0∞ :=
  uniformLPError A (cell ε d.1) (vertexPoint ε d.1) d.2

section ZeroCone

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The shifted zero-cone configuration is a random element of the GMS space** (arXiv:1705.11161, lines 1126-1127:
"By definition, H is a measurable function of h, η̂, and θ"): every measurable version `G` of the boundary-length
pair has a realization `F` of the configuration, almost measurable for the Borel σ-algebra of `d^CC`. -/
def ZeroConeConfigRealizable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∃ F : Ω × ℝ → GMSSpace, IsZeroConeConfigRealization D hγ G F

/-- **Rotation invariance of the shifted zero-cone configuration** (arXiv:1705.11161, lines 1212-1213: "the law of
`(h, η)` is invariant under rotations about the origin"): the law of every realization is invariant under the
quarter turn of the plane. -/
def ZeroConeConfigRotationInvariance (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
    ((P.prod zeroConePhase).map F).map (isometryGMS quarterTurn) = (P.prod zeroConePhase).map F

/-- **Scale invariance of the circle-average embedding** (arXiv:1705.11161, lines 1336-1343, from
Duplantier–Miller–Sheffield, arXiv:1409.7055, Proposition 4.13(i), and the LQG coordinate change formula): for
`b = 1/n` the pair `E n = (η^b, G^b)`, `η^b = R_b⁻¹ η₀(b ·)` and `G^b = b^{-1/2} G(b ·)`, has the law of `(η₀, G)`,
with random radii `R_b > 0` tending to `0` almost surely as `b → 0`. -/
def ZeroConeAreaScaling (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∃ (Rsc : ℕ → Ω → ℝ≥0) (E : ℕ → Ω → C(ℝ, ℂ) × Path2),
      (∀ n, Measurable (Rsc n)) ∧ (∀ n, Measurable (E n)) ∧
      (∀ n, P.map (E n) = P.map fun ω => (η₀ ω, G ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Rsc n ω) atTop (𝓝 0)) ∧
      (∀ n, ∀ᵐ ω ∂P, 0 < Rsc n ω) ∧
      ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P,
        (∀ t : ℝ, η₀ ω (t / (n : ℝ)) = (Rsc n ω : ℝ) • (E n ω).1 t) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, (E n ω).2 t = c • G ω (t / (n : ℝ))

/-- **Measurability of the uniform Lévy–Prokhorov errors** on the annuli `closedBall 0 ρ \ B_b(0)` (used without
comment in the convergence in probability of arXiv:1705.11161, line 1343): the scale suprema of the unit-mesh error
are almost measurable for the law of `((η₀, G), θ)`, and the mesh-`1/n` error is almost measurable for the law of the
shifted mesh-`1/n` data. -/
def ZeroConeUniformErrorMeasurability
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G → ∀ b ρ : ℝ,
    (∀ ε₀ : ℝ≥0, AEMeasurable (scaleSup (unitScaleConfigError (closedBall (0 : ℂ) ρ \ ball 0 b)) ε₀)
        ((P.map fun ω => (η₀ ω, G ω)).prod zeroConePhase)) ∧
      ∀ n : ℕ, 0 < n →
        AEMeasurable (meshUniformError (closedBall (0 : ℂ) ρ \ ball 0 b) (1 / (n : ℝ)))
          ((P.prod zeroConePhase).map fun p => (phaseShiftedCurve (1 / (n : ℝ)) p.2 (η₀ p.1),
            phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1)))

/-- **Connectedness along lines at every realization** (hypothesis 3 of arXiv:1807.07515, Theorem 1.16, as verified
in arXiv:1705.11161, Proposition 3.1): the law of every realization of the shifted zero-cone configuration is
connected along lines. -/
theorem connectedAlongLines_map_of_zeroConeConfigRealization
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    {G : Ω → Path2} {F : Ω × ℝ → GMSSpace} (hF : IsZeroConeConfigRealization D hγ G F) :
    ConnectedAlongLines ((P.prod zeroConePhase).map F) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hQ : zeroConePhase ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hph : ∀ᵐ θ ∂zeroConePhase, θ ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  obtain ⟨G₁, -, hclock, H₁, hH₁, -, hconn⟩ :=
    exists_zeroCone_clocked_shiftedCellConfig_connectedAlongLines D hγ hf one_pos zeroConePhase hQ hph
  refine hconn F hF.2.2.1 ?_
  have hGG : ∀ᵐ ω ∂P, G₁ ω = G ω := by
    filter_upwards [hclock, hF.2.1] with ω hω hGω
    obtain ⟨ψ, -, -, hGψ, hψ, -⟩ := hω
    ext1 t
    rw [hGψ t, hGω t, hψ t]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hGG, hH₁, hF.2.2.2] with p hGp hHp hFp
  obtain ⟨_, hH₁eq, -⟩ := hHp
  obtain ⟨_, hFeq⟩ := hFp
  rw [hFeq, hH₁eq, hGp]

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from the conclusion of Theorem 3.10.** If the conclusion of
Theorem 3.10 of arXiv:1807.07515 holds at the law of every realization of the shifted zero-cone configuration, then,
given the realization, the rotation invariance, the scale invariance of the circle-average embedding and the
measurability of the uniform errors, the shifted zero-cone data at mesh `1/n` satisfy the annulus form of the
uniform-start invariance principle. -/
theorem zeroConeAnnulusLPForm_of_theorem310Form
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (h310 : ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
      GMSTheorem310Form ((P.prod zeroConePhase).map F))
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (hscale : ZeroConeAreaScaling D hγ) (hmeas : ZeroConeUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  intro G hG α b ρ R c hα hαb hbρ hρR hc θ hθ
  have hPprob : IsProbabilityMeasure P := D.isProbabilityMeasure
  set A : Set ℂ := closedBall (0 : ℂ) ρ \ ball 0 b
  have hA : IsCompact A := (isCompact_closedBall (0 : ℂ) ρ).diff isOpen_ball
  obtain ⟨δ, hδ, hgood⟩ := exists_mem_annulusSelectedLPData_of_uniformLPError_lt hα hαb hbρ hρR hc
  obtain ⟨hXm, hUm⟩ := hmeas G hG b ρ
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
      Tendsto (fun ε => unitScaleConfigError A ε ((η₀ p.1, G p.1), p.2)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hunifP, ae_mem_regularData_phaseShifted D hγ hf hG one_pos, hF.2.2.2]
      with p hu hreg hFp
    obtain ⟨h, hFeq⟩ := hFp
    exact tendsto_unitScaleError_of_theorem310 h p.2
      (bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1) (fun t => (G p.1 (t + 1 * p.2)).2))
      hreg.2.1 hreg.2.2 (F p) hFeq target hc₀ hcov₀ hu hA
  -- transfer to the law of `((η₀, G), θ)`
  have hgm : Measurable fun ω => (η₀ ω, G ω) := D.measurable_curves.2.2.1.prodMk hG.1
  have hmapf : (P.prod zeroConePhase).map (fun p : Ω × ℝ => ((η₀ p.1, G p.1), p.2)) =
      (P.map fun ω => (η₀ ω, G ω)).prod zeroConePhase := by
    have h := Measure.map_prod_map P zeroConePhase hgm measurable_id
    rw [Measure.map_id] at h
    exact h.symm
  have hfm : Measurable fun p : Ω × ℝ => ((η₀ p.1, G p.1), p.2) :=
    (hgm.comp measurable_fst).prodMk measurable_snd
  have hXμ : ∀ᵐ s ∂(P.map fun ω => (η₀ ω, G ω)).prod zeroConePhase,
      Tendsto (fun ε => unitScaleConfigError A ε s) (𝓝[>] 0) (𝓝 0) := by
    rw [← hmapf]
    refine ae_tendsto_map_of_ae_tendsto hfm.aemeasurable (unitScaleConfigError A) (fun ε₀ => ?_) hX1
    rw [hmapf]
    exact hXm ε₀
  -- the random change of scale (Lemma 3.5)
  obtain ⟨Rs, E, hRm, hEm, hElaw, hR0, hRpos, hrel⟩ := hscale G hG
  have hHlaw : ∀ n, (P.prod zeroConePhase).map (fun p : Ω × ℝ => (E n p.1, p.2)) =
      (P.map fun ω => (η₀ ω, G ω)).prod zeroConePhase := by
    intro n
    have h := Measure.map_prod_map P zeroConePhase (hEm n) measurable_id
    rw [Measure.map_id, hElaw n] at h
    exact h.symm
  have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (half_pos hδ)
  have hconvP := tendsto_measure_lt_scaleChange (unitScaleConfigError A)
    (fun n (p : Ω × ℝ) => (E n p.1, p.2)) (fun n (p : Ω × ℝ) => Rs n p.1)
    (fun n => ((hEm n).comp measurable_fst).prodMk measurable_snd) hHlaw hXμ hXm
    (fun n => (hRm n).comp measurable_fst) (Measure.quasiMeasurePreserving_fst.ae hR0)
    (fun n => Measure.quasiMeasurePreserving_fst.ae (hRpos n)) hδ2
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hconvP) _ (ENNReal.ofReal_pos.2 hθ))
  refine ⟨max N₁ 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₁ 1) hn)
  have hbad := hN₁ n (le_trans (le_max_left N₁ 1) hn)
  have hpos : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.2 (Nat.cast_pos.2 hn1)
  set d : Ω × ℝ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ) := fun p =>
    (phaseShiftedCurve (1 / (n : ℝ)) p.2 (η₀ p.1), phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1))
  -- the mesh-`1/n` data are measurable: the shift of the curve is continuous in (curve, phase), and the edge
  -- counts are jointly measurable in (path, mesh, phase)
  have hdm : AEMeasurable d (P.prod zeroConePhase) := by
    have hcurve : Continuous fun q : C(ℝ, ℂ) × ℝ => phaseShiftedCurve (1 / (n : ℝ)) q.2 q.1 := by
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      change Continuous fun q : (C(ℝ, ℂ) × ℝ) × ℝ => q.1.1 (q.2 + 1 / (n : ℝ) * q.1.2)
      fun_prop
    have hpm : Measurable fun p : Ω × ℝ =>
        (G p.1, (⟨1 / (n : ℝ), hpos⟩ : {ε : ℝ // 0 < ε}), p.2) :=
      (hG.1.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
    have hcm : Measurable fun p : Ω × ℝ => (η₀ p.1, p.2) :=
      (D.measurable_curves.2.2.1.comp measurable_fst).prodMk measurable_snd
    exact ((hcurve.measurable.comp hcm).prodMk
      (measurable_bmEdgeCount_shiftedMesh_array.comp hpm)).aemeasurable
  -- the bad set is contained in the irregular data and the large errors
  have hsub : (annulusSelectedLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ⊆
      regularDataᶜ ∪ {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x} := by
    intro x hx
    rw [mem_union]
    by_cases hreg : x ∈ regularData
    · refine Or.inr ?_
      show ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x
      by_contra hlt
      exact (mem_compl_iff _ _).1 hx
        (hgood (1 / (n : ℝ)) hpos x hreg.1.1 hreg.2.1 hreg.2.2 (not_le.1 hlt))
    · exact Or.inl hreg
  have hZ : (P.prod zeroConePhase).map d regularDataᶜ = 0 := by
    rw [Measure.map_apply₀ hdm measurableSet_regularData.compl.nullMeasurableSet]
    have h0 := ae_iff.1 (ae_mem_regularData_phaseShifted D hγ hf hG hpos)
    exact h0
  have hnull : NullMeasurableSet {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x}
      ((P.prod zeroConePhase).map d) := nullMeasurableSet_le aemeasurable_const (hUm n hn1)
  have hUle : (P.prod zeroConePhase).map d
        {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x} ≤
      (P.prod zeroConePhase)
        {p | ENNReal.ofReal (δ / 2) < unitScaleConfigError A (Rs n p.1) (E n p.1, p.2)} := by
    rw [Measure.map_apply₀ hdm hnull]
    refine measure_mono_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hrel n hn1)] with p hp hpU
    obtain ⟨hη, c', hc', hG'⟩ := hp
    have heq : meshUniformError A (1 / (n : ℝ)) (d p) =
        unitScaleConfigError A (Rs n p.1) (E n p.1, p.2) :=
      uniformLPError_phaseShifted_eq_unitScaleError A hn1 p.2 hη hc' hG'
    have hpU' : ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) (d p) := hpU
    show ENNReal.ofReal (δ / 2) < unitScaleConfigError A (Rs n p.1) (E n p.1, p.2)
    rw [← heq]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ).2 (half_lt_self hδ)) hpU'
  calc (P.prod zeroConePhase).map d (annulusSelectedLPData (1 / (n : ℝ)) α b ρ R c)ᶜ
      ≤ (P.prod zeroConePhase).map d (regularDataᶜ ∪
          {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x}) := measure_mono hsub
    _ ≤ (P.prod zeroConePhase).map d regularDataᶜ + (P.prod zeroConePhase).map d
          {x | ENNReal.ofReal δ ≤ meshUniformError A (1 / (n : ℝ)) x} := measure_union_le _ _
    _ ≤ 0 + (P.prod zeroConePhase)
          {p | ENNReal.ofReal (δ / 2) < unitScaleConfigError A (Rs n p.1) (E n p.1, p.2)} :=
      add_le_add hZ.le hUle
    _ ≤ ENNReal.ofReal θ := by
      rw [zero_add]
      exact hbad

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from Theorem 3.10 of arXiv:1807.07515.** Under the
hypotheses of `exists_zeroCone_config_gmsHypotheses_of_lemmaA1`, the law of every realization of the shifted
zero-cone configuration satisfies the four hypotheses of Theorem 1.16 of arXiv:1807.07515, so Theorem 3.10 applies
to it; with the named steps of the proof of Lemma 3.5 this gives the annulus form of the uniform-start invariance
principle for the shifted zero-cone data at mesh `1/n`. -/
theorem zeroConeAnnulusLPForm_of_theorem310
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1 D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) (h310 : GMSTheorem310)
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (hscale : ZeroConeAreaScaling D hγ) (hmeas : ZeroConeUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  have hT := zeroConeTailTriviality_of_lemmaA1 D hγ hA1 hcov hlaw hcurve hphase
  refine zeroConeAnnulusLPForm_of_theorem310Form D hγ hf (fun G F hF => ?_) hreal hrot hscale hmeas
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have : IsProbabilityMeasure ((P.prod zeroConePhase).map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.2.2.1).2 inferInstance
  exact h310 _ (massTransport_map_of_zeroConeSpatialAverageInvariance D hγ hI h25 hF)
    (ergodicModuloScaling_map_of_zeroConeTailTriviality D hγ hT hF)
    (finiteExpectation_map_of_zeroConeConfigRealization D hγ hF)
    (connectedAlongLines_map_of_zeroConeConfigRealization D hγ hf hF)

end ZeroCone

end MatedCRT.GMS310Transfer
