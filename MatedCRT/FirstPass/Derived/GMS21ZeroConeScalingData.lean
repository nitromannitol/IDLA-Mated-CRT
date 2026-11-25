import MatedCRT.FirstPass.Derived.GMS21ZeroConeWalkIdentification
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusForm
import MatedCRT.FirstPass.Derived.GoodCurveSet
import MatedCRT.FirstPass.Derived.ShiftedPhysicalMultiplicityScaling
import MatedCRT.FirstPass.Derived.CellIntersectionScaling
import MatedCRT.FirstPass.Derived.GMS21ScaleChangeInProbability
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import MatedCRT.Proofs.Infra.MatingOfTrees
import LatticeProb.LQG.CoupledClockedCellEmbedding

/-!
# The shifted zero-cone data at mesh `1/n` and their unit-mesh rescalings

In the proof of Lemma 3.5 of Gwynne–Miller–Sheffield (arXiv:1705.11161, lines 1331-1343) the mesh-`1/n` cells of the
`0`-quantum cone are compared with the unit-mesh cells of the rescaled pair `(h^b, η^b)`, `b = 1/n`, through the
dilation by `R_b`. This file records the deterministic and almost sure ingredients of this comparison.

* `regularData`: the data with a proper onto curve and a locally finite multigraph with the successor edges; a Borel
  set (`measurableSet_regularData`).
* `uniformLPError_phaseShifted_eq_unitScaleError`: if `η(t/n) = R η'(t)` and `G'(t) = c G(t/n)` with `c > 0`, the
  uniform error at mesh `1/n` of the data read on the lattice `n⁻¹ ℤ + n⁻¹ θ` is the uniform error at spatial scale
  `R` of the unit-mesh data of `(η', G')` read on `ℤ + θ`.
* `ae_tendsto_map_of_ae_tendsto`: almost everywhere convergence of an error functional transfers to the image law,
  when its scale suprema are almost everywhere measurable for the image law.
* `ae_mem_regularData_phaseShifted`: almost surely the shifted zero-cone data are regular at every fixed mesh.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

/-- **Regular data**: a proper onto curve and a locally finite multigraph on `ℤ` with the successor edges. -/
def regularData : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | d.1 ∈ properOntoCurves ∧ IsLocallyFiniteMult d.2 ∧ ∀ k : ℤ, d.2 k (k + 1) ≠ 0}

/-- The locally finite multigraphs on `ℤ` form a measurable set. -/
theorem measurableSet_isLocallyFiniteMult :
    MeasurableSet {m : ℤ → ℤ → ℕ | IsLocallyFiniteMult m} := by
  have hset : {m : ℤ → ℤ → ℕ | IsLocallyFiniteMult m} =
      ⋂ a : ℤ, ⋃ N : ℕ, ⋂ c : ℤ, ⋂ (_ : (N : ℤ) < |c|), {m : ℤ → ℤ → ℕ | m a c = 0} := by
    ext m
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    unfold IsLocallyFiniteMult
    refine forall_congr' fun a => ⟨fun h => ?_, fun ⟨N, hN⟩ => ?_⟩
    · obtain ⟨N, hN⟩ := (h.image fun c : ℤ => |c|).bddAbove
      refine ⟨N.toNat, fun c hc => ?_⟩
      by_contra hne
      have hmem : c ∈ {b | m a b ≠ 0} := hne
      have h1 : |c| ≤ N := hN ⟨c, hmem, rfl⟩
      have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
      exact absurd hc (not_lt.2 (h1.trans h2))
    · refine (Set.finite_Icc (-(N : ℤ)) N).subset fun c hc => ?_
      have hc' : m a c ≠ 0 := hc
      by_contra hnot
      have hlt : (N : ℤ) < |c| := by
        by_contra hle
        exact hnot (Set.mem_Icc.2 (abs_le.1 (not_lt.1 hle)))
      exact hc' (hN c hlt)
  rw [hset]
  exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun c =>
    MeasurableSet.iInter fun _ => (measurableSet_singleton 0).preimage
      ((measurable_pi_apply c).comp (measurable_pi_apply a))

/-- The multigraphs on `ℤ` with the successor edges form a measurable set. -/
theorem measurableSet_succEdges :
    MeasurableSet {m : ℤ → ℤ → ℕ | ∀ k : ℤ, m k (k + 1) ≠ 0} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun k => (measurableSet_singleton 0).compl.preimage
    ((measurable_pi_apply (k + 1)).comp (measurable_pi_apply k))

/-- The regular data form a Borel set. -/
theorem measurableSet_regularData : MeasurableSet regularData :=
  (measurableSet_properOntoCurves.preimage measurable_fst).inter
    ((measurableSet_isLocallyFiniteMult.preimage measurable_snd).inter
      (measurableSet_succEdges.preimage measurable_snd))

/-- A time shift of a proper onto curve is proper and onto. -/
theorem phaseShiftedCurve_mem_properOntoCurves {η : C(ℝ, ℂ)} (hη : η ∈ properOntoCurves) (ε θ : ℝ) :
    phaseShiftedCurve ε θ η ∈ properOntoCurves := by
  rw [properOntoCurves, mem_ofPred_eq] at hη ⊢
  exact ⟨hη.1.comp (Homeomorph.addRight (ε * θ)).isClosedEmbedding.tendsto_cocompact,
    hη.2.comp (Homeomorph.addRight (ε * θ)).surjective⟩

/-- **Scaling of the uniform error** (arXiv:1705.11161, lines 1336-1342: `G^b` is isometric to `R_b H^b`). If
`η(t/n) = R η'(t)` and `G'(t) = c G(t/n)` with `c > 0`, the uniform error at mesh `1/n` of the curve `η` and the edge
counts of `G`, read on the lattice `n⁻¹ ℤ + n⁻¹ θ`, is the uniform error at spatial scale `R` of the unit-mesh data of
`(η', G')` read on `ℤ + θ`. -/
theorem uniformLPError_phaseShifted_eq_unitScaleError (A : Set ℂ) {n : ℕ} (hn : 0 < n) (θ : ℝ)
    {η₀ e₁ : C(ℝ, ℂ)} {G e₂ : MatedCRTHarmonic.MatedCRT.Path2} {R : ℝ≥0}
    (h₁ : ∀ t, η₀ (t / n) = (R : ℝ) • e₁ t) {c : ℝ} (hc : 0 < c)
    (h₂ : ∀ t, e₂ t = c • G (t / n)) :
    uniformLPError A (cell (1 / (n : ℝ)) (phaseShiftedCurve (1 / (n : ℝ)) θ η₀))
        (vertexPoint (1 / (n : ℝ)) (phaseShiftedCurve (1 / (n : ℝ)) θ η₀))
        (phaseShiftedEdgeCount (1 / (n : ℝ)) θ G) =
      unitScaleError A R (fun t => e₁ (t + 1 * θ))
        (bmEdgeCount 1 (fun t => (e₂ (t + 1 * θ)).1) (fun t => (e₂ (t + 1 * θ)).2)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hb : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.2 hn'
  unfold unitScaleError
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
  · have hw : ∀ t, G t = (c⁻¹ * (e₂ ((n : ℝ) * t)).1, c⁻¹ * (e₂ ((n : ℝ) * t)).2) := by
      intro t
      rw [h₂, mul_div_cancel_left₀ t hn'.ne']
      refine Prod.ext ?_ ?_ <;> simp [inv_mul_cancel_left₀ hc.ne']
    exact bmEdgeCount_shiftedPhysical_rescale (ε := 1) hn' (inv_pos.2 hc) θ e₂ G hw

/-- **Almost everywhere convergence under the image law.** If the error functional `X` tends to `0` at small scales
along `f` almost everywhere, and its scale suprema are almost everywhere measurable for the image law, then it tends
to `0` at small scales almost everywhere for the image law. -/
theorem ae_tendsto_map_of_ae_tendsto {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {f : Ω → S} (hf : AEMeasurable f P) (X : ℝ≥0 → S → ℝ≥0∞)
    (hXm : ∀ ε₀ : ℝ≥0, AEMeasurable (scaleSup X ε₀) (P.map f))
    (h : ∀ᵐ ω ∂P, Tendsto (fun ε => X ε (f ω)) (𝓝[>] 0) (𝓝 0)) :
    ∀ᵐ s ∂(P.map f), Tendsto (fun ε => X ε s) (𝓝[>] 0) (𝓝 0) := by
  set N : Set S := ⋃ j : ℕ, ⋂ k : ℕ,
    {s | ((j : ℝ≥0∞))⁻¹ < scaleSup X (1 / ((k : ℝ≥0) + 1)) s}
  have hN : NullMeasurableSet N (P.map f) :=
    NullMeasurableSet.iUnion fun _ => NullMeasurableSet.iInter fun _ =>
      nullMeasurableSet_lt aemeasurable_const (hXm _)
  have hsub : ∀ s, s ∉ N → Tendsto (fun ε => X ε s) (𝓝[>] 0) (𝓝 0) := by
    intro s hs
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
    have hs' : ∃ k : ℕ, scaleSup X (1 / ((k : ℝ≥0) + 1)) s ≤ ((j : ℝ≥0∞))⁻¹ := by
      by_contra hne
      exact hs (mem_iUnion.2 ⟨j, mem_iInter.2 fun k => not_le.1 fun hk => hne ⟨k, hk⟩⟩)
    obtain ⟨k, hk⟩ := hs'
    have hpos : (0 : ℝ≥0) < 1 / ((k : ℝ≥0) + 1) := by positivity
    filter_upwards [Ioc_mem_nhdsGT hpos] with ε hε
    exact (le_scaleSup X hε.1 hε.2 s).trans (hk.trans hj.le)
  have hnull : P.map f N = 0 := by
    rw [Measure.map_apply₀ hf hN]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    intro htend
    have hω' : f ω ∈ N := hω
    obtain ⟨j, hj⟩ := mem_iUnion.1 hω'
    obtain ⟨k, hk⟩ := exists_scaleSup_le_of_tendsto X htend
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j))
    exact (not_lt.2 hk) (mem_iInter.1 hj k)
  rw [ae_iff]
  exact measure_mono_null (fun s hs => by_contra fun hsN => hs (hsub s hsN)) hnull

section ZeroCone

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Regularity of the shifted zero-cone data.** For every measurable version `G` of the boundary-length pair of the
zero-cone curve and every mesh `ε > 0`, almost surely under `P ⊗ Unif[0, 1]` the curve `t ↦ η₀(t + ε θ)` is proper
and onto, and the edge counts at mesh `ε` of `t ↦ G(t + ε θ)` are locally finite with the successor edges. -/
theorem ae_mem_regularData_phaseShifted
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγ G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂P.prod zeroConePhase,
      (phaseShiftedCurve ε p.2 (η₀ p.1), phaseShiftedEdgeCount ε p.2 (G p.1)) ∈ regularData := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hQ : zeroConePhase ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨G₂, -, hclock, hemb⟩ :=
    LatticeProb.exists_coupled_clocked_cellularEmbedding D hγ hf ε hε zeroConePhase hQ
  have hGG : ∀ᵐ ω ∂P, G₂ ω = G ω := by
    filter_upwards [hclock, hG.2] with ω hω hGω
    obtain ⟨ψ, -, -, hGψ, hψ, -⟩ := hω
    ext1 t
    rw [hGψ t, hGω t, hψ t]
  have hsf : ∀ᵐ ω ∂P, Function.Surjective (η₀ ω) ∧ Tendsto (η₀ ω) (cocompact ℝ) (cocompact ℂ) :=
    (l46t_zeroCone_spaceFillingGeometry D hγ).mono fun _ h => ⟨h.1, h.2.1⟩
  have hphase : ∀ᵐ p ∂P.prod zeroConePhase, p.2 ∈ Icc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hGG, Measure.quasiMeasurePreserving_fst.ae hsf,
    hphase, hemb] with p hGGp hsfp hph hembp
  obtain ⟨hlf, -, -⟩ := hembp hph.1 hph.2
  rw [regularData, mem_ofPred_eq]
  refine ⟨?_, ?_, fun k => ?_⟩
  · exact phaseShiftedCurve_mem_properOntoCurves ⟨hsfp.2, hsfp.1⟩ ε p.2
  · rw [← hGGp]
    have hlfm := MatedCRT.FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε.le
    simp only [ContinuousMap.coe_mk] at hlfm
    unfold phaseShiftedEdgeCount
    exact hlfm
  · have hL : Continuous fun t => (G p.1 (t + ε * p.2)).1 :=
      ((G p.1).continuous.comp (continuous_id.add continuous_const)).fst
    unfold phaseShiftedEdgeCount
    exact _root_.MatedCRT.bmEdgeCount_succ_ne_zero hε.le hL (fun t => (G p.1 (t + ε * p.2)).2) k

end ZeroCone

end MatedCRT.GMS310Transfer
