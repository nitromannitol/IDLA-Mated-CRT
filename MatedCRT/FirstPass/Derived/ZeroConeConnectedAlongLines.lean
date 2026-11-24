import MatedCRT.FirstPass.Derived.ZeroConeClockedCellCode
import LatticeProb.LQG.PeanosphereTimeTranslation
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedMeasurable

/-!
# Connectedness along lines for the shifted zero-cone cell configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161), Proposition 3.1, verifies the hypotheses of the invariance principle for
random cell configurations (Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16; Lattice-Probability
`ReflectedGMS.GMS.theorem1_16`) for the cells `η₀([x - 1, x])`, `x ∈ ℤ + θ`, of the space-filling SLE curve `η₀`
parametrized by the quantum area of a `0`-quantum cone, with an independent shift `θ` ((3.1) there). One of these
hypotheses is *connectedness along lines*: almost surely, for every nondegenerate horizontal or vertical segment, the
cells meeting it, with the edges joining them, form a connected graph. The printed proof (p. 23): any two points of a
segment are joined by a chain of cells meeting at single points, and two cells meeting at a point `z` are joined by a
chain of cells containing `z`, consecutive ones sharing a boundary arc.

In the mating-of-trees coupling, the shifted zero-cone cells with the edges of the contour criterion of the
transported boundary-length pair `G = bm ∘ ψ` form the cell configuration of `exists_zeroCone_clocked_shiftedCellCode`.
This file adds connectedness along lines:

* `exists_zeroCone_clocked_shiftedCellCode_lineConnected`: the same construction, with `(H p).LineConnected` almost
  surely. The pointwise chain argument is Theorem B for a Peanosphere pair
  (`shiftedAreaCellConfig_lineConnected_of_peanosphere`), applied to the time-translated pair
  (`MatedCRTHarmonic.RouteM.Peanosphere.time_translate`) of the Peanosphere `(G, η₀)` of the coupling.
* `connectedAlongLines_map_of_ae_lineConnected`: a measurable realization in the GMS space of an almost surely
  line-connected configuration has a law connected along lines.
* `exists_zeroCone_clocked_shiftedCellConfig_connectedAlongLines`: **hypothesis 3 of the invariance principle for the
  shifted zero-cone configuration**: every measurable realization `F` of the configuration in the GMS space has
  `ConnectedAlongLines` law. (Measurability of the realization, a map into the Borel space of the metric `d^CC`, is a
  premise, as in `MatedCRTEnv.IsValid.connectedAlongLines_map_areaCellConfig`.)
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal

/-- **The shifted zero-cone cell configuration is connected along lines almost surely.** The construction of
`exists_zeroCone_clocked_shiftedCellCode` (the cells `η₀([ε (x - 1 + θ), ε (x + θ)])` of the zero-cone curve with
the contour edges of the transported boundary-length pair `G = bm ∘ ψ`, and an independent phase `θ` of law `Q`),
with the additional conclusion that the configuration is connected along lines (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Proposition 3.1, "Connectivity along lines"). -/
theorem exists_zeroCone_clocked_shiftedCellCode_lineConnected
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hphase : ∀ᵐ θ ∂Q, θ ∈ Icc (0 : ℝ) 1) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∃ H : Ω × ℝ → CellConfig,
        (∀ᵐ p ∂P.prod Q, ∃ h : IsAreaParametrized
            ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
          H p = shiftedAreaCellConfig h hε p.2
            (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
              (fun t => (G p.1 (t + ε * p.2)).2)) ∧
            (H p).IsCellConfiguration ∧ (H p).LineConnected) ∧
        AEMeasurable (fun p => (H p).code) (P.prod Q) := by
  obtain ⟨G, hG, hclock, hembed⟩ :=
    LatticeProb.exists_coupled_clocked_cellularEmbedding D hγ hf ε hε Q hQ
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have ha := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_zeroCone_isAreaParametrized_of_coupling D hγ)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := Q)).ae hphase
  have hc := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae hclock
  have hgood : ∀ᵐ p ∂P.prod Q,
      ∀ h : IsAreaParametrized ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
        (shiftedAreaCellConfig h hε p.2
          (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
            (fun t => (G p.1 (t + ε * p.2)).2))).IsCellConfiguration ∧
        (shiftedAreaCellConfig h hε p.2
          (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
            (fun t => (G p.1 (t + ε * p.2)).2))).LineConnected := by
    filter_upwards [hp, hembed, hc] with p hp he hc
    intro h
    obtain ⟨hlf, H, hH⟩ := he hp.1 hp.2
    obtain ⟨_, _, _, _, _, hpeano⟩ := hc
    have hT := hpeano.time_translate (ε * p.2)
    have hL := shiftedAreaCellConfig_lineConnected_of_peanosphere h hε p.2 _ hlf H hH hT
    refine ⟨?_, hL⟩
    apply shiftedAreaCellConfig_isCellConfiguration h hε p.2 _ H hH
      (bmEdgeCount_symm ε _ _) (bmEdgeCount_self ε _ _)
    intro a b hab
    have hne : a ≠ b := by
      intro heq
      subst b
      rw [bmEdgeCount_self] at hab
      exact (lt_irrefl 0) hab
    rw [graph_adj_eq_srwGraph hlf hε.le]
    exact ⟨hne, Or.inl (Nat.ne_of_gt hab)⟩
  have hvalid : ∀ᵐ p ∂P.prod Q,
      ∃ h : IsAreaParametrized ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
        (shiftedAreaCellConfig h hε p.2
          (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
            (fun t => (G p.1 (t + ε * p.2)).2))).IsCellConfiguration := by
    filter_upwards [ha, hgood] with p ha hg
    exact ⟨ha, (hg ha).1⟩
  obtain ⟨H, hH, hcode⟩ := exists_shiftedAreaCellConfig_aemeasurable_code
    (P.prod Q) hε (η₀ ∘ Prod.fst) (G ∘ Prod.fst) Prod.snd
    (fun p => (l46tZeroConeCellModel D hγ).area p.1)
    (D.measurable_curves.2.2.1.comp measurable_fst) (hG.comp measurable_fst)
    measurable_snd hvalid
  refine ⟨G, hG, hclock, H, ?_, hcode⟩
  filter_upwards [hH, hgood] with p hHp hg
  obtain ⟨h, hEq, hcell⟩ := hHp
  refine ⟨h, hEq, hcell, ?_⟩
  rw [hEq]
  exact (hg h).2

/-- A realization `F` in the GMS space, measurable for the Borel σ-algebra of the metric `d^CC`, of an almost surely
line-connected random cell configuration `H` has a law connected along lines. -/
theorem connectedAlongLines_map_of_ae_lineConnected {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Ω → CellConfig) (hL : ∀ᵐ p ∂μ, (H p).LineConnected) (F : Ω → GMSSpace)
    (hF : AEMeasurable F μ) (hF_eq : ∀ᵐ p ∂μ, (F p).1 = H p) :
    ConnectedAlongLines (μ.map F) := by
  rw [connectedAlongLines_iff]
  apply (ae_map_iff hF measurableSet_lineConnected).2
  filter_upwards [hL, hF_eq] with p hp heq
  rw [heq]
  exact hp

/-- **Connectedness along lines for the shifted zero-cone cell configuration** (hypothesis 3 of
Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16, as verified in arXiv:1705.11161, Proposition 3.1). For the
cell configuration `H` of the zero-cone cells `η₀([ε (x - 1 + θ), ε (x + θ)])` with the contour edges of the
transported boundary-length pair `G = bm ∘ ψ` and an independent phase `θ` of law `Q`, every realization `F` of `H`
in the GMS space, measurable for the Borel σ-algebra of `d^CC`, has a law connected along lines. -/
theorem exists_zeroCone_clocked_shiftedCellConfig_connectedAlongLines
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hphase : ∀ᵐ θ ∂Q, θ ∈ Icc (0 : ℝ) 1) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∃ H : Ω × ℝ → CellConfig,
        (∀ᵐ p ∂P.prod Q, ∃ h : IsAreaParametrized
            ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
          H p = shiftedAreaCellConfig h hε p.2
            (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
              (fun t => (G p.1 (t + ε * p.2)).2)) ∧ (H p).IsCellConfiguration) ∧
        AEMeasurable (fun p => (H p).code) (P.prod Q) ∧
        ∀ F : Ω × ℝ → GMSSpace, AEMeasurable F (P.prod Q) →
          (∀ᵐ p ∂P.prod Q, (F p).1 = H p) → ConnectedAlongLines ((P.prod Q).map F) := by
  obtain ⟨G, hG, hclock, H, hH, hcode⟩ :=
    exists_zeroCone_clocked_shiftedCellCode_lineConnected D hγ hf hε Q hQ hphase
  refine ⟨G, hG, hclock, H, ?_, hcode, fun F hF hF_eq => ?_⟩
  · filter_upwards [hH] with p hp
    obtain ⟨h, hEq, hcell, -⟩ := hp
    exact ⟨h, hEq, hcell⟩
  · refine connectedAlongLines_map_of_ae_lineConnected (P.prod Q) H ?_ F hF hF_eq
    filter_upwards [hH] with p hp
    obtain ⟨-, -, -, hline⟩ := hp
    exact hline

end MatedCRT
