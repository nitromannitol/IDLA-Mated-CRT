import MatedCRT.FirstPass.Derived.CurveMultOuterTransfer
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import MatedCRT.FirstPass.S3i.LensFloored
import MatedCRT.FirstPass.SLERef.Reference
import LatticeProb.LQG.ItineraryRealMesh
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CTheorem39
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# The floored one-sided boundary estimate of Lemma 3.6 on every valid environment, from a reference environment

Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Theorem 3.9, the boundary
estimate (3.31) in the form proved on p. 32 (with the floor `ε ^ β` on the boundary distance), from Lemma 3.11.
This file proves `FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮` (S3i/LensFloored.lean) for a model `𝒮` with
normalized space-filling SLE law `ν` and valid reference environments on `ℝ`, given a one-sided mating-rigid set
that is full for every correlated Brownian law.

* The exponent `β` of Lemma 3.11 is chosen before the radius: for the mating-of-trees coupling of a reference
  environment of `γ`, `pairEventsReal_of_coupling` (Lattice-Probability) gives `α, β > 0` and then, for every
  `ρ' ∈ (0, 1)`, a probability `p₁ > 0` and a constant `C` with `P[(3.35) fails at mesh ε, radius ρ', floor ε^β]
  ≤ C ε^α`. The floor of the statement is `ε ^ min β (1/2)`, which is `< 1`.
* On the event of (3.35) at the ambient radius `(1 + ρ)/2` and on the Peanosphere event, the deterministic (3.31)
  of Lattice-Probability (`t15c_boundaryEstimate_of_lemma311Holds`, for every open `D ⊆ B_ρ(0)` with connected
  complement) gives the one-sided estimate of the statement; simple connectivity of `D` gives the connected
  complement by `isConnected_compl_of_simplyConnected` (Lattice-Probability).
* The event of the statement at mesh `ε` depends on the environment only through (curve, edge multiplicities), so
  its outer probability of failure in a valid environment of `𝒮` is at most the one in the reference environment
  (`measure_eta_mult_preimage_le_of_valid`).

## Main results

* `le_biSup_of_finite`, `biSup_nonneg_of_finite`: the maximum and the sup norm of the statement, as real suprema
  over finite vertex sets;
* `oneSidedBEFlooredAt_of_lemma311GoodReal`: the deterministic inclusion on the good event of (3.35);
* `frozenOneSidedBoundaryContinuityFlooredUniform_of_reference`: the floored uniform estimate on every valid
  environment.
-/

open MeasureTheory Set Metric

namespace MatedCRT.FirstPass.Derived

/-- A value of `g` on a finite set `s ⊆ ℤ` is at most the real supremum `⨆ j ∈ s, g j`. -/
theorem le_biSup_of_finite {s : Set ℤ} (hs : s.Finite) (g : ℤ → ℝ) {k : ℤ} (hk : k ∈ s) :
    g k ≤ ⨆ j ∈ s, g j := by
  have hbdd : BddAbove (range fun j => ⨆ (_ : j ∈ s), g j) := by
    refine ⟨∑ i ∈ hs.toFinset, |g i|, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact Real.iSup_le (fun hj => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |g i|) (fun i _ => abs_nonneg _) (hs.mem_toFinset.2 hj)))
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  calc g k = ⨆ (_ : k ∈ s), g k := (ciSup_pos (f := fun _ => g k) hk).symm
    _ ≤ ⨆ j ∈ s, g j := le_ciSup hbdd k

/-- The real supremum `⨆ j ∈ s, g j` over a finite set `s ⊆ ℤ` is nonnegative: some `j ∉ s` contributes the value
`0` of the empty supremum. -/
theorem biSup_nonneg_of_finite {s : Set ℤ} (hs : s.Finite) (g : ℤ → ℝ) : 0 ≤ ⨆ j ∈ s, g j := by
  have hbdd : BddAbove (range fun j => ⨆ (_ : j ∈ s), g j) := by
    refine ⟨∑ i ∈ hs.toFinset, |g i|, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact Real.iSup_le (fun hj => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |g i|) (fun i _ => abs_nonneg _) (hs.mem_toFinset.2 hj)))
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  obtain ⟨k, hk⟩ := hs.infinite_compl.nonempty
  have : IsEmpty (k ∈ s) := ⟨hk⟩
  calc (0 : ℝ) = ⨆ (_ : k ∈ s), g k := (Real.iSup_of_isEmpty _).symm
    _ ≤ ⨆ j ∈ s, g j := le_ciSup hbdd k

/-- **The floored one-sided boundary estimate on the good event of (3.35)** (deterministic, one `ω`;
GMS19 (3.31) as proved on p. 32). Let `0 < ε`, `0 < ρ < 1` and `0 < p < 1`. Suppose that `ω` lies in the good event
of (3.35) at mesh `ε`, ambient radius `(1 + ρ)/2`, floor `ε ^ β` and probability `p`, for the boundary-length pair
`S.bm` and a continuous curve `η'` with the same cells as `S.η`, and that `(S.bm ω, η' ω)` is a Peanosphere. Then the
one-sided estimate `FP36OneSidedBEFlooredAt` holds at `ω` with `ν = t15cXi p` and `A = 2 κ ^ ν`,
`κ = t15cKappa ρ ((1 + ρ)/2)`. -/
theorem oneSidedBEFlooredAt_of_lemma311GoodReal {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {η' : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β p : ℝ} (hε0 : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hgood : ω ∈ MatedCRTHarmonic.GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ((1 + ρ) / 2) β p)
    (hpeano : MatedCRTHarmonic.RouteM.Peanosphere (S.bm ω) (η' ω))
    (hcellEq : ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) :
    FirstPass36.FP36OneSidedBEFlooredAt (S.mult ε ω) ε (S.η ω) ρ (MatedCRTHarmonic.GMSMain.t15cXi p)
      (2 * MatedCRTHarmonic.GMSMain.t15cKappa ρ ((1 + ρ) / 2) ^ MatedCRTHarmonic.GMSMain.t15cXi p) β := by
  obtain ⟨h, H, hcell, h311⟩ := hgood
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  have hHc : H.cell = cell ε (S.η ω) := funext fun x => (hcell x).trans (hcellEq x).symm
  have hVM : ∀ E : Set ℂ, MatedCRTHarmonic.verticesMeeting H.cell E = cellVertices ε (S.η ω) E := by
    intro E
    rw [hHc]
    rfl
  have hconn := MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl ε (S.bm ω) h
  have hLC : H.PointConnected :=
    MatedCRTHarmonic.RouteM.pointConnected_of_peanosphere_holds hpeano H (funext hcell)
  have hpt : ∀ v, vertexPoint ε (S.η ω) v ∈ H.cell v := by
    intro v
    rw [hHc]
    exact ⟨ε * v, ⟨mul_le_mul_of_nonneg_left (by linarith) hε0.le, le_rfl⟩, rfl⟩
  have hBE := MatedCRTHarmonic.GMSMain.t15c_boundaryEstimate_of_lemma311Holds hconn hLC hε0 hρ0 hρρ' hp0 hp1
    h311
  intro D f hDρ hDo hDc hsc hharmT x hx t ht
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  have hDcc : IsPreconnected Dᶜ :=
    (MatedCRTHarmonic.isConnected_compl_of_simplyConnected hDo hDb hDc.nonempty).isPreconnected
  have hfin : (cellVertices ε (S.η ω) D).Finite := by
    rw [← hVM]
    exact MatedCRTHarmonic.GMS3.finite_verticesMeeting H hDb
  have hfinB : (cellVertices ε (S.η ω) (frontier D ∩ ball (vertexPoint ε (S.η ω) x) t)).Finite := by
    rw [← hVM]
    exact MatedCRTHarmonic.GMS3.finite_verticesMeeting H (isBounded_ball.subset inter_subset_right)
  have hharm : ∀ v ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
      v ∉ MatedCRTHarmonic.verticesMeeting H.cell (frontier D) →
        MatedCRTHarmonic.GMS3.lap (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) h) f v = 0 := by
    intro v hv hvb
    rw [hVM] at hv hvb
    exact (S.lap_graph_eq_zero_iff hε0.le h f v).2 (hharmT v ⟨hv, hvb⟩)
  have hM0 : 0 ≤ FirstPass36.discreteSupNorm ε (S.η ω) D f := biSup_nonneg_of_finite hfin _
  have hm0 : 0 ≤ FirstPass36.boundarySupNear ε (S.η ω) D f x t := biSup_nonneg_of_finite hfinB _
  have hMb : ∀ y ∈ MatedCRTHarmonic.verticesMeeting H.cell D,
      |f y| ≤ FirstPass36.discreteSupNorm ε (S.η ω) D f := by
    intro y hy
    rw [hVM] at hy
    exact le_biSup_of_finite hfin (fun k => |f k|) hy
  have hmb : ∀ y ∈ MatedCRTHarmonic.verticesMeeting H.cell D ∩
      MatedCRTHarmonic.verticesMeeting H.cell (frontier D ∩ ball (vertexPoint ε (S.η ω) x) t),
        f y ≤ FirstPass36.boundarySupNear ε (S.η ω) D f x t := by
    intro y hy
    have hy2 := hy.2
    rw [hVM] at hy2
    exact le_biSup_of_finite hfinB f hy2
  have hxD : x ∈ MatedCRTHarmonic.verticesMeeting H.cell D := by
    rw [hVM]
    exact hx.1
  exact (hBE D hDo hDρ hDcc f hharm _ hMb x hxD (vertexPoint ε (S.η ω) x) (hpt x) t ht _).2 hmb
    (by linarith)

/-- **The floored one-sided boundary estimate of Lemma 3.6, with the floor exponent chosen before the radius, on
every valid environment** (GMS19 Theorem 3.9, (3.31) as proved on p. 32, from Lemma 3.11). Let `𝒮` be a
space-filling SLE model with normalized law `ν` and valid reference environments on `ℝ`, and let `G` be a one-sided
mating-rigid set of pairs of paths that is full for every `γ`-correlated two-sided Brownian law. Then
`FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮`: the floor exponent is `min β (1/2)` for the exponent `β` of
Lemma 3.11 in the reference environment of `γ`, the exponent and constant are `t15cXi p` and `2 κ ^ (t15cXi p)`
for the probability `p` of Lemma 3.11 at the radius `(1 + ρ)/2`, and for every valid environment the estimate fails
with outer probability `≤ C ε^α` for `ε ∈ (0, 1)`. -/
theorem frozenOneSidedBoundaryContinuityFlooredUniform_of_reference {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hG : ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
        MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0) ∧ MatingRigidLEOn G) :
    FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮 := by
  obtain ⟨G, hGnull, hGr⟩ := hG
  intro γ hγ0 hγ2
  obtain ⟨Sr, hSr⟩ := href γ hγ0 hγ2
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hSr.matingOfTrees
  obtain ⟨α, hα, β, hβ, hpair⟩ :=
    LatticeProb.LQG.ExplicitScale.pairEventsReal_of_coupling hC inferInstance ⟨hγ0, hγ2⟩
  have hη' : ∀ᵐ ω ∂Sr.P, ⇑(η' ω) = Sr.η ω := hae.mono fun _ h => h.1
  have hpeano := MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq Sr hSr hη'
  refine ⟨min β (1 / 2), lt_min hβ (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
    fun ρ hρ0 hρ1 Ω _ S hS => ?_⟩
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  obtain ⟨_p₀, _hp₀, p₁, hp₁, C, hCε⟩ := hpair ((1 + ρ) / 2) hρ'0 hρ'1
  have hp0 : 0 < min p₁ (1 / 2) := lt_min hp₁ (by norm_num)
  have hp1 : min p₁ (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨1, MatedCRTHarmonic.GMSMain.t15cXi (min p₁ (1 / 2)),
    2 * MatedCRTHarmonic.GMSMain.t15cKappa ρ ((1 + ρ) / 2) ^ MatedCRTHarmonic.GMSMain.t15cXi (min p₁ (1 / 2)),
    1, one_pos, MatedCRTHarmonic.GMSMain.t15cXi_pos hp0 hp1,
    mul_pos two_pos (Real.rpow_pos_of_pos (MatedCRTHarmonic.GMSMain.t15cKappa_pos hρ0 hρρ') _), one_pos,
    α, hα, C, 1, one_pos, fun ε hε0 hε1 => ?_⟩
  refine (measure_eta_mult_preimage_le_of_valid hν hν hγ0 hγ2 hS hSr (hGnull γ hγ0 hγ2) hGr ε
    {x | ¬ FirstPass36.FP36OneSidedBEFlooredAt x.2 ε x.1 ρ
      (MatedCRTHarmonic.GMSMain.t15cXi (min p₁ (1 / 2)))
      (2 * MatedCRTHarmonic.GMSMain.t15cKappa ρ ((1 + ρ) / 2) ^
        MatedCRTHarmonic.GMSMain.t15cXi (min p₁ (1 / 2))) (min β (1 / 2))}).trans ?_
  refine (measure_mono_ae ?_).trans (hCε ε hε0 hε1).2
  filter_upwards [hpeano.1, hpeano.2] with ω hpω hcω hnot hgood
  exact hnot (oneSidedBEFlooredAt_of_lemma311GoodReal Sr hε0 hρ0 hρ1 hp0 hp1
    (MatedCRTHarmonic.GMSMain.EpsB.lemma311GoodReal_mono hε0 hε1.le (min_le_left _ _) (min_le_left _ _) hgood)
    hpω (hcω ε))

end MatedCRT.FirstPass.Derived

/-! ## Audit -/
#print axioms MatedCRT.FirstPass.Derived.oneSidedBEFlooredAt_of_lemma311GoodReal
#print axioms MatedCRT.FirstPass.Derived.frozenOneSidedBoundaryContinuityFlooredUniform_of_reference
