import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideIdentityProof

/-!
# The cell-side identity from the triple points of valid environments

This file proves `MatingOfTreesCellSideIdentity` (`WindowChartBGDiscreteLawIntrinsic.lean`) from the named
literature input `CorrelatedBMNoCommonLocalMin` (Le Gall, two-sided cone points) and the step
`ValidEnvTriplePointsNoContinuum 𝒮`: in every valid environment, almost surely the points visited at least three
times by the curve `S.η` contain no continuum of positive diameter.

The step is stated on the objects of a valid environment: its curve is, through the mating-of-trees coupling, a
quotient of the boundary-length pair with the time fibres of a whole-plane space-filling SLE (Duplantier–Miller–
Sheffield, arXiv:1409.7055, Lemma 8.15), and the triple points of whole-plane space-filling SLE_κ, `κ > 4`, contain
no continuum (DMS (8.9) and Lemmas 8.12-8.13 for `κ ≥ 8`; Gwynne–Holden–Miller, arXiv:1512.01223, Corollary 6.5,
for `4 < κ < 8`).

The deduction is the one of `MatingOfTreesCellSideIdentityProof.lean`: in a valid environment the boundary-length
pair and the curve form a Peanosphere with finite fibres (`MatedCRTEnv.IsValid.exists_curve_peanosphere`, coupling
field `visitBound`), and almost surely the edge count of each pair of cells is the frontier-side multiplicity
(`bmEdgeCount_eq_cellSideMult`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open MatedCRTHarmonic.MatedCRT (Path2 lrCoord IsCorrelatedBM2)

namespace MatedCRT

/-- **Step: the triple points of the curve of a valid environment contain no
continuum.** For `0 < γ < 2` and every valid environment `S`, almost surely the points visited at least three times by
`S.η ω` (`curveTriplePoints`) contain no continuum of positive diameter. Route: on an extension
of the sample space, a whole-plane space-filling SLE_κ, `κ = 16/γ²`, coupled with the same boundary-length pair
`S.bm` (Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem 1.9; Gwynne–Holden–Miller–Sun, arXiv:1510.04687,
Theorem 1.1) has the same time fibres as `S.η ω` (DMS Lemma 8.15), so the two curves differ by a homeomorphism of the
plane, which carries the triple points of one curve to those of the other; for whole-plane space-filling SLE_κ,
`κ > 4`, the triple points contain no continuum( DMS (8.9) and Lemmas 8.12-8.13; Gwynne–Holden–
Miller, arXiv:1512.01223, Corollary 6.5 and the proof of Example 2.2). -/
def ValidEnvTriplePointsNoContinuum (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ¬ ContainsNondegenerateContinuum (curveTriplePoints (S.η ω))

/-- **The multiplicities of the mated-CRT map are the frontier-side multiplicities of the cells**
(`MatingOfTreesCellSideIdentity`).
Given the named literature input `CorrelatedBMNoCommonLocalMin` (Le Gall) and the step
`ValidEnvTriplePointsNoContinuum 𝒮`, in every valid environment, for every cell size `ε > 0`, almost surely
`S.mult ε = cellSideMult ε (S.η ω)`. The Peanosphere, the finite fibres and the Brownian law of the boundary-length
pair come from the mating-of-trees coupling of the environment. -/
theorem matingOfTreesCellSideIdentity_of_valid {𝒮 : SpaceFillingSLEModel} (hcone : CorrelatedBMNoCommonLocalMin)
    (htripleV : ValidEnvTriplePointsNoContinuum 𝒮) : MatingOfTreesCellSideIdentity 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS ε hε
  obtain ⟨ηc, hηc, hP, -⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  obtain ⟨_, _, _, _, _, _, _, _, ηL, η', _, hC, hae⟩ := hS.matingOfTrees
  have hbm : AEMeasurable S.bm S.P := hC.measurable_curves.2.2.2.aemeasurable
  have hμ := hC.boundaryLawBM
  obtain ⟨kv, hkv⟩ := hC.visitBound
  have hfin : ∀ᵐ ω ∂S.P, ∀ z, (S.η ω ⁻¹' {z}).Finite := by
    filter_upwards [hkv, hC.areaParam, hae] with ω hk harea hω
    obtain ⟨⟨φ, -, hφ⟩, -⟩ := harea
    intro z
    have hset : S.η ω ⁻¹' {z} = φ ⁻¹' (ηL ω ⁻¹' {z}) := by
      ext t
      show S.η ω t = z ↔ ηL ω (φ t) = z
      rw [← hω.1, hφ]
    rw [hset]
    exact (Set.encard_lt_top_iff.1 ((hk z).trans_lt (ENat.natCast_lt_top kv))).preimage φ.injective.injOn
  have htr := htripleV γ hγ0 hγ2 Ω S hS
  have hcn := ae_of_ae_map hbm (hcone γ hγ0 hγ2 _ hμ)
  have hd := ae_of_ae_map hbm (ae_all_iff.2 fun i : Fin 2 => ae_all_iff.2 fun k : ℤ =>
    (ae_forall_exists_lt_right hμ i (ε * k)).and (ae_forall_exists_lt_left hμ i (ε * k)))
  filter_upwards [hηc, hP, hfin, htr, hcn, hd] with ω hηω hPω hfinω htrω hcnω hdω
  rw [hηω] at hPω
  funext j k
  exact bmEdgeCount_eq_cellSideMult hPω hfinω htrω (fun u hu => hcnω u hu) hε
    (fun k => ⟨hdω 0 k, hdω 1 k⟩) j k

end MatedCRT
