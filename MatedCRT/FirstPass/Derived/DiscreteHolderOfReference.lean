import MatedCRT.FirstPass.Derived.CurveMultOuterTransfer
import MatedCRT.FirstPass.Derived.Lemma311RealStandardBorel
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.SLERef.Reference
import LatticeProb.LQG.Theorem15DiscreteBoundaryGood
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# Lemma 3.2 (corrected; GMS19 Theorem 3.9) on every valid environment, from a reference environment

Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Theorem 3.9: the interior
estimate (3.30′) and, for simply connected domains with Hölder discrete boundary data, the global estimate (3.33).
This file proves `FrozenDiscreteHolderContinuityCorrected 𝒮` for a model `𝒮` with normalized space-filling SLE law
`ν` and valid reference environments on `ℝ`, given one-sided rigidity of the mating relation and the cell size
estimate (Lemma 2.8).

The event of the statement at mesh `ε` depends on the environment only through the pair (curve, edge multiplicities)
`(S.η, S.mult ε)` (`IsDiscreteHolderGood`). Its outer probability of failure is therefore at most the one in a
standard Borel reference environment (`measure_eta_mult_preimage_le_of_valid`). In the reference environment the event
contains, up to a null set, the intersection of

* the good event of (3.35) at mesh `ε` and ambient radius `(1 + ρ)/2` (`EpsB.Lemma311GoodReal`; failure probability
  `≤ C ε^α` by `lemma311Real_of_isValid`), and
* the cell size event of Lemma 2.8 (`CellSizeEstimateStmt`),

by the deterministic Theorem 1.5 of [GMS19] with discrete boundary data
(`T15B.theorem15_of_lemma311Holds_discreteBoundary_max`) and the interior estimate (`T15B.interior_estimate`), on the
Peanosphere event (`MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq`). The constants `ξ, A, β, ξ', C` are those of
the reference environment, chosen before the environment `S`.

## Main results

* `IsDiscreteHolderGood`: the event of `DiscreteHolderContinuityCorrectedStep` at mesh `ε`, as a predicate of
  (curve, edge multiplicities);
* `measure_not_isDiscreteHolderGood_le_of_valid`: transfer of its outer failure probability to a standard Borel
  valid environment;
* `isDiscreteHolderGood_of_lemma311GoodReal`: the deterministic inclusion on the good event of (3.35);
* `frozenDiscreteHolderContinuityCorrected_of_reference`: the corrected Lemma 3.2 for every valid environment.
-/

open MeasureTheory Set Metric

namespace MatedCRT.FirstPass.Derived

/-- The exponent `ξ(p) = log₄ (1 - min(p, 1/2))⁻¹` of the interior estimate (3.30′) is less than `1`. -/
theorem holderExponent_lt_one (p : ℝ) : MatedCRTHarmonic.GMSMain.T15B.holderExponent p < 1 := by
  unfold MatedCRTHarmonic.GMSMain.T15B.holderExponent
  have h1 : min p (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have h2 : (0 : ℝ) < 1 - min p (1 / 2) := by linarith
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (inv_pos.mpr h2), Real.rpow_one]
  calc (1 - min p (1 / 2))⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ < 4 := by norm_num

/-- The constant `C₀ = 2 (3^χ + 2·5^χ) C'` of (3.33) coming from the Hölder constant of the boundary data is
positive. -/
theorem theorem15DiscreteBdryConst_pos {χ C' : ℝ} (hC' : 0 < C') :
    0 < MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteBdryConst χ C' := by
  unfold MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteBdryConst
  positivity

/-- The interior constant `A(p) = 2 · 16^{ξ(p)}` of (3.30′) is at most the mass factor `A₀` of (3.33). -/
theorem holderConst_le_theorem15DiscreteMassConst {p C₁ ξ₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    MatedCRTHarmonic.GMSMain.T15B.holderConst p ≤
      MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst p C₁ ξ₁ := by
  have hA := MatedCRTHarmonic.GMSMain.T15B.holderConst_pos p
  have h2 : (0 : ℝ) ≤ 2 ^ ξ₁ := by positivity
  have h3 : 0 ≤ (1 + 2 ^ ξ₁) * C₁ := mul_nonneg (by positivity) hC₁
  unfold MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst
  linarith

/-- If, almost surely, `t` and `u` imply `s`, then `μ sᶜ ≤ μ tᶜ + μ uᶜ` (outer measures). -/
theorem measure_compl_le_add_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t u : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ t → ω ∈ u → ω ∈ s) : μ sᶜ ≤ μ tᶜ + μ uᶜ := by
  have hsub : ∀ᵐ ω ∂μ, ω ∈ sᶜ → ω ∈ tᶜ ∪ uᶜ := by
    filter_upwards [h] with ω hω hs
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
    exact absurd (hω hc.1 hc.2) hs
  exact (measure_mono_ae hsub).trans (measure_union_le _ _)

/-- **The event of the corrected Lemma 3.2 at mesh `ε`** (the body of `DiscreteHolderContinuityCorrectedStep`), as a
predicate of the curve `η` and the edge multiplicities `m`: for every open connected `D ⊆ B_ρ` and every `f`
discrete harmonic on `V^ε(D) \ V^ε(∂D)`, the interior estimate (3.30′) with exponent `ξ`, constant `A` and floor
`ε^β`, and, for `D` simply connected with `(χ, C')`-Hölder data on `V^ε(∂D)`, the estimate (3.33) with exponent `ξ'`
and constant `max C (A sup_{V^ε(D)} |f|)`. -/
def IsDiscreteHolderGood (ρ ξ A β χ C' ξ' C ε : ℝ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) : Prop :=
  ∀ (D : Set ℂ) (f : ℤ → ℝ), D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    (∀ a ∈ interiorCellVertices ε η D, matedLaplacian m f a = 0) →
    (∀ a ∈ interiorCellVertices ε η D, ∀ b ∈ cellVertices ε η D,
      |f a - f b| * infDist (vertexPoint ε η a) (frontier D) ^ ξ ≤
        A * (⨆ a' : cellVertices ε η D, |f a'|) *
          max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ) ∧
    ((SimplyConnectedSpace D ∧ ∀ a ∈ cellVertices ε η (frontier D),
        ∀ b ∈ cellVertices ε η (frontier D),
          |f a - f b| ≤ C' * max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ χ) →
      ∀ a ∈ cellVertices ε η D, ∀ b ∈ cellVertices ε η D,
        |f a - f b| ≤ max C (A * ⨆ a' : cellVertices ε η D, |f a'|) *
          max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ')

/-- **Outer-measure transfer of the event of the corrected Lemma 3.2 to a standard Borel valid environment.** The
event at mesh `ε` is a property of `(S.η, S.mult ε)`, so its outer probability of failure under a valid environment
`S` is at most the one under a valid environment `S'` on a standard Borel space, for models with the same normalized
space-filling SLE law and a one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian
law (`measure_eta_mult_preimage_le_of_valid`). -/
theorem measure_not_isDiscreteHolderGood_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ρ ξ A β χ C' ξ' C ε : ℝ) :
    S.P {ω | IsDiscreteHolderGood ρ ξ A β χ C' ξ' C ε (S.η ω) (S.mult ε ω)}ᶜ ≤
      S'.P {ω | IsDiscreteHolderGood ρ ξ A β χ C' ξ' C ε (S'.η ω) (S'.mult ε ω)}ᶜ :=
  measure_eta_mult_preimage_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG ε
    {x | IsDiscreteHolderGood ρ ξ A β χ C' ξ' C ε x.1 x.2}ᶜ

/-- **The corrected Lemma 3.2 on the good event of (3.35)** (deterministic, one `ω`). Let `0 < ε ≤ 1`,
`0 < ρ < 1`, `β₁, q, p > 0` with `q ≤ 1`. Suppose that `ω` lies in the good event of (3.35) at mesh `ε`, ambient
radius `(1 + ρ)/2`, scale exponent `β₁` and probability `p`, for the boundary-length pair `S.bm` and a continuous
curve `η'` with the same cells as `S.η`, that `(S.bm ω, η' ω)` is a Peanosphere, and that the cells meeting `B_ρ`
have diameter `≤ ε^q`. Then the event of the corrected Lemma 3.2 holds at `ω` with `ξ = ξ(p')`,
`A = A₀(p', C₁, ξ₁)`, `β = min β₁ q`, `ξ' = theorem15DiscreteExponent p' ξ₁ β q χ` and
`C = theorem15DiscreteBdryConst χ C'` (`p' = probParam p`, `ξ₁ = boundaryExponent p`,
`C₁ = boundaryConst p ρ ((1 + ρ)/2)`). -/
theorem isDiscreteHolderGood_of_lemma311GoodReal {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {η' : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β₁ q p χ C' : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hβ₁ : 0 < β₁) (hq0 : 0 < q) (hq1 : q ≤ 1) (hp : 0 < p) (hχ : 0 < χ) (hC' : 0 < C')
    (hgood : ω ∈ MatedCRTHarmonic.GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ((1 + ρ) / 2) β₁ p)
    (hpeano : MatedCRTHarmonic.RouteM.Peanosphere (S.bm ω) (η' ω))
    (hcellEq : ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (hcells : ∀ x : ℤ, (cell ε (S.η ω) x ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) x) ≤ ε ^ q) :
    IsDiscreteHolderGood ρ
      (MatedCRTHarmonic.GMSMain.T15B.holderExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p))
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst (MatedCRTHarmonic.GMSMain.T15B.probParam p)
        (MatedCRTHarmonic.GMSMain.T15B.boundaryConst p ρ ((1 + ρ) / 2))
        (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p))
      (min β₁ q) χ C'
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p)
        (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p) (min β₁ q) q χ)
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteBdryConst χ C') ε (S.η ω) (S.mult ε ω) := by
  obtain ⟨h, H, hcell, h311⟩ := hgood
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  have hβ : 0 < min β₁ q := lt_min hβ₁ hq0
  have hβq : min β₁ q ≤ q := min_le_right _ _
  have hHc : H.cell = cell ε (S.η ω) := funext fun x => (hcell x).trans (hcellEq x).symm
  have hVM : ∀ E : Set ℂ, MatedCRTHarmonic.verticesMeeting H.cell E = cellVertices ε (S.η ω) E := by
    intro E
    rw [hHc]
    rfl
  have hconn := MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl ε (S.bm ω) h
  have hLC : H.PointConnected :=
    MatedCRTHarmonic.RouteM.pointConnected_of_peanosphere_holds hpeano H (funext hcell)
  have h311β : MatedCRTHarmonic.GMSMain.T15A.Lemma311Holds H ε ((1 + ρ) / 2) (min β₁ q) p :=
    MatedCRTHarmonic.GMSMain.T15A.Lemma311Holds.mono h311 hε0 hε1 le_rfl (min_le_left _ _) le_rfl
  have h311p : MatedCRTHarmonic.GMSMain.T15A.Lemma311Holds H ε ((1 + ρ) / 2) (min β₁ q)
      (MatedCRTHarmonic.GMSMain.T15B.probParam p) :=
    MatedCRTHarmonic.GMSMain.T15A.Lemma311Holds.mono h311β hε0 hε1 le_rfl le_rfl (min_le_left _ _)
  have hpt : ∀ v, vertexPoint ε (S.η ω) v ∈ H.cell v := by
    intro v
    rw [hHc]
    exact ⟨ε * v, ⟨mul_le_mul_of_nonneg_left (by linarith) hε0.le, le_rfl⟩, rfl⟩
  have hcells' : ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell x) ≤ ε ^ q := by
    rw [hHc]
    exact hcells
  have hC₁ : 0 ≤ MatedCRTHarmonic.GMSMain.T15B.boundaryConst p ρ ((1 + ρ) / 2) :=
    MatedCRTHarmonic.GMSMain.T15B.boundaryConst_nonneg hρ0 hρρ'
  intro D f hDρ hDo hDc hharmT
  have hDρ' : D ⊆ ball (0 : ℂ) ((1 + ρ) / 2) := hDρ.trans (ball_subset_ball hρρ'.le)
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  have hfin : (cellVertices ε (S.η ω) D).Finite := by
    rw [← hVM]
    exact MatedCRTHarmonic.GMS3.finite_verticesMeeting H hDb
  set M := ⨆ a' : cellVertices ε (S.η ω) D, |f a'| with hMdef
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => abs_nonneg _
  have hMb : ∀ v ∈ cellVertices ε (S.η ω) D, |f v| ≤ M := by
    intro v hv
    have := hfin.to_subtype
    exact le_ciSup (f := fun a' : cellVertices ε (S.η ω) D => |f a'|) (Set.finite_range _).bddAbove ⟨v, hv⟩
  have hharm : ∀ v ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
      v ∉ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) →
        MatedCRTHarmonic.GMS3.lap (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) h) f v = 0 := by
    intro v hv hvb
    rw [hVM] at hv hvb
    exact (S.lap_graph_eq_zero_iff hε0.le h f v).2 (hharmT v ⟨hv, hvb⟩)
  refine ⟨fun a ha b hb => ?_, fun hmore a ha b hb => ?_⟩
  · have hx : a ∈ MatedCRTHarmonic.verticesMeeting H.cell D := by rw [hVM]; exact ha.1
    have hxA : a ∉ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) := by rw [hVM]; exact ha.2
    have hy : b ∈ MatedCRTHarmonic.verticesMeeting H.cell D := by rw [hVM]; exact hb
    have hint := MatedCRTHarmonic.GMSMain.T15B.interior_estimate H hconn f hDo
      (MatedCRTHarmonic.GMSMain.T15B.probParam_pos hp) (Real.rpow_pos_of_pos hε0 (min β₁ q))
      (fun v hv hvb => hharm v hv hvb) (fun v hv => hMb v (by rw [← hVM]; exact hv))
      (MatedCRTHarmonic.GMSMain.T15B.disc_of_lemma311Holds hε0 h311p hDρ') hx hxA hy (hpt a) (hpt b)
    rw [dist_eq_norm] at hint
    refine hint.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (holderConst_le_theorem15DiscreteMassConst hC₁) hM0) (Real.rpow_nonneg ?_ _))
    exact le_max_of_le_left (Real.rpow_pos_of_pos hε0 _).le
  · obtain ⟨hsc, hbd⟩ := hmore
    have hDne : D.Nonempty := hDc.nonempty
    have hDcc : IsPreconnected Dᶜ :=
      (MatedCRTHarmonic.isConnected_compl_of_simplyConnected hDo hDb hDne).isPreconnected
    have hbdry : ∀ a ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
        a ∈ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) →
        ∀ b ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
          b ∈ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) →
            |f a - f b| ≤ C' * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ χ := by
      intro a _ ha b _ hb
      rw [hVM] at ha hb
      rw [dist_eq_norm]
      exact hbd a ha b hb
    have hbdM : ∀ a ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
        a ∈ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) → |f a| ≤ M := by
      intro a ha _
      rw [hVM] at ha
      exact hMb a ha
    have key := MatedCRTHarmonic.GMSMain.T15B.theorem15_of_lemma311Holds_discreteBoundary_max hconn hLC
      (vertexPoint ε (S.η ω)) hpt hε0 hε1 hρ0 hρρ' hβ hβq hq1 hp h311β hcells' hDo hDρ hDcc hC'.le hχ hM0
      hharm hbdry hbdM a (by rw [hVM]; exact ha) b (by rw [hVM]; exact hb)
    rw [dist_eq_norm] at key
    exact key

/-- **Lemma 3.2, corrected (GMS19 Theorem 3.9), on every valid environment.** Let `𝒮` be a space-filling SLE model
with normalized law `ν` (`HasNormalizedSLELaw 𝒮 ν`) and valid reference environments on `ℝ`
(`HasReferenceEnvironments 𝒮`). Assume that for every `γ ∈ (0, 2)` some one-sided mating-rigid set `G` of pairs of
paths (`MatingRigidLEOn G`) is full for every `γ`-correlated two-sided Brownian law, and the cell size estimate
(Lemma 2.8, `CellSizeEstimateStmt 𝒮`). Then `FrozenDiscreteHolderContinuityCorrected 𝒮`: the exponents and constants
`ξ, A, β, ξ', C` are those of the reference environment of `γ` (they do not depend on the environment), and for every
valid environment the event of the statement fails with outer probability `≤ C₀ ε^α` for `ε` small. -/
theorem frozenDiscreteHolderContinuityCorrected_of_reference {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮) :
    FrozenDiscreteHolderContinuityCorrected 𝒮 := by
  unfold FrozenDiscreteHolderContinuityCorrected DiscreteHolderContinuityCorrectedStep
  intro γ hγ0 hγ2 ρ hρ0 hρ1
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  obtain ⟨Sr, hSr⟩ := href γ hγ0 hγ2
  obtain ⟨η', -, -, hη', α₁, hα₁, β₁, hβ₁, p, hp, C₁, hgood⟩ :=
    lemma311Real_of_isValid hSr hγ0 hγ2 hρ'0 hρ'1
  have hpeano := MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq Sr hSr hη'
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have h4 : (4 : ℝ) < (2 + γ) ^ 2 := by nlinarith
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; linarith
  have hqe : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = q := by rw [hqdef]; ring
  obtain ⟨α₂, hα₂, C₂, r₂, hr₂, hcellP⟩ := h28 γ hγ0 hγ2 (1 / (2 + γ) ^ 2) ρ
    (by rw [← hqdef]; exact hq0) (by rw [← hqdef]; exact hq1) hρ0 hρ1 ℝ Sr hSr
  refine ⟨MatedCRTHarmonic.GMSMain.T15B.holderExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p),
    MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst (MatedCRTHarmonic.GMSMain.T15B.probParam p)
      (MatedCRTHarmonic.GMSMain.T15B.boundaryConst p ρ ((1 + ρ) / 2))
      (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p),
    min β₁ q,
    MatedCRTHarmonic.GMSMain.T15B.holderExponent_pos (MatedCRTHarmonic.GMSMain.T15B.probParam_pos hp),
    holderExponent_lt_one _,
    MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst_pos
      (MatedCRTHarmonic.GMSMain.T15B.boundaryConst_nonneg hρ0 hρρ'),
    lt_min hβ₁ hq0, (min_le_right _ _).trans_lt hq1, fun χ C' hχ hχ1 hC' => ?_⟩
  refine ⟨MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p)
      (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p) (min β₁ q) q χ,
    MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteBdryConst χ C',
    MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteExponent_pos
      (MatedCRTHarmonic.GMSMain.T15B.probParam_pos hp) (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent_pos hp)
      (lt_min hβ₁ hq0) hq0 hχ,
    MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteExponent_lt_one ((min_le_right _ _).trans hq1.le) hχ hχ1,
    theorem15DiscreteBdryConst_pos hC', fun Ω _ S hS => ?_⟩
  obtain ⟨G, hGnull, hGr⟩ := hG γ hγ0 hγ2
  refine ⟨min α₁ α₂, lt_min hα₁ hα₂, max C₁ 0 + max C₂ 0, min r₂ 1, lt_min hr₂ one_pos,
    fun ε hε0 hεr => ?_⟩
  have hε1 : ε < 1 := hεr.trans_le (min_le_right _ _)
  have hεr₂ : ε < r₂ := hεr.trans_le (min_le_left _ _)
  change S.P {ω | IsDiscreteHolderGood ρ
      (MatedCRTHarmonic.GMSMain.T15B.holderExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p))
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteMassConst (MatedCRTHarmonic.GMSMain.T15B.probParam p)
        (MatedCRTHarmonic.GMSMain.T15B.boundaryConst p ρ ((1 + ρ) / 2))
        (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p))
      (min β₁ q) χ C'
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteExponent (MatedCRTHarmonic.GMSMain.T15B.probParam p)
        (MatedCRTHarmonic.GMSMain.T15B.boundaryExponent p) (min β₁ q) q χ)
      (MatedCRTHarmonic.GMSMain.T15B.theorem15DiscreteBdryConst χ C') ε (S.η ω) (S.mult ε ω)}ᶜ ≤ _
  refine (measure_not_isDiscreteHolderGood_le_of_valid hν hν hγ0 hγ2 hS hSr hGnull hGr _ _ _ _ _ _ _ _
    ε).trans ?_
  refine (measure_compl_le_add_of_ae (μ := Sr.P)
    (t := MatedCRTHarmonic.GMSMain.EpsB.Lemma311GoodReal Sr.bm η' ε
      ((1 + ρ) / 2) β₁ p)
    (u := {ω | ∀ k : ℤ, (cell ε (Sr.η ω) k ∩ ball 0 ρ).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) ≤ diam (cell ε (Sr.η ω) k) ∧
        diam (cell ε (Sr.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)}) ?_).trans ?_
  · filter_upwards [hpeano.1, hpeano.2] with ω hpω hcω hgω hcellω
    exact isDiscreteHolderGood_of_lemma311GoodReal Sr hε0 hε1.le hρ0 hρ1 hβ₁ hq0 hq1.le hp hχ hC' hgω hpω
      (hcω ε) fun k hk => (hcellω k hk).2.trans_eq (by rw [hqe])
  · have hpow₁ : ε ^ α₁ ≤ ε ^ min α₁ α₂ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)
    have hpow₂ : ε ^ α₂ ≤ ε ^ min α₁ α₂ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right _ _)
    have hε₁ : 0 ≤ ε ^ α₁ := Real.rpow_nonneg hε0.le _
    have hε₂ : 0 ≤ ε ^ α₂ := Real.rpow_nonneg hε0.le _
    have hb₁ : C₁ * ε ^ α₁ ≤ max C₁ 0 * ε ^ min α₁ α₂ :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hε₁).trans
        (mul_le_mul_of_nonneg_left hpow₁ (le_max_right _ _))
    have hb₂ : C₂ * ε ^ α₂ ≤ max C₂ 0 * ε ^ min α₁ α₂ :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hε₂).trans
        (mul_le_mul_of_nonneg_left hpow₂ (le_max_right _ _))
    have hm : 0 ≤ ε ^ min α₁ α₂ := Real.rpow_nonneg hε0.le _
    calc _ ≤ ENNReal.ofReal (C₁ * ε ^ α₁) + ENNReal.ofReal (C₂ * ε ^ α₂) :=
          add_le_add (hgood ε hε0 hε1) (hcellP ε hε0 hεr₂)
      _ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ min α₁ α₂) + ENNReal.ofReal (max C₂ 0 * ε ^ min α₁ α₂) :=
          add_le_add (ENNReal.ofReal_le_ofReal hb₁) (ENNReal.ofReal_le_ofReal hb₂)
      _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * ε ^ min α₁ α₂) := by
          rw [add_mul, ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hm)
            (mul_nonneg (le_max_right _ _) hm)]

end MatedCRT.FirstPass.Derived
