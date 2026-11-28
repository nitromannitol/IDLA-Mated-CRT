import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideIdentityValid
import LatticeProb.LQG.PeanosphereContourFibers
import LatticeProb.Prob.CorrelatedBMWhitening

/-!
# The Brownian inputs of the cell-side identity

This file proves the two inputs of `matingOfTreesCellSideIdentity_of_valid` (`MatingOfTreesCellSideIdentityValid.lean`)
from statements of the literature on general objects (written answer MQ-sbl-39).

* `correlatedBMNoCommonLocalMin`: a `γ`-correlated two-sided Brownian pair `(L, R)`, `0 < γ < 2`, almost surely has no
  time which is a local minimum of both coordinates (answer section B, lines 41-47). Whitening the pair at the time
  `-n` (`LatticeProb.CorrelatedBM.whitenAt`) gives a standard planar Brownian motion `W`, and the increments of
  `(L, R)` are nonnegative exactly when the increments of `W` lie in the closed wedge `{a x ≥ b |y|}` of angle
  `πγ²/4 < π`. A common local minimum at `u > -n` is thus a two-sided cone point of `W` at the time `u + n`, which
  planar Brownian motion does not have (named hypothesis `PlanarBMNoTwoSidedConePoints`, Le Gall).
* `validEnvTriplePointsNoContinuum`: in a valid environment, almost surely the points visited at least three times by
  the curve contain no continuum of positive diameter (answer lines 28-39). Almost every correlated Brownian pair is
  the boundary-length pair of a whole-plane space-filling SLE whose triple points contain no continuum (named
  hypothesis `CorrelatedBMTraversalTriplePointsNoContinuum`). Two Peanosphere curves of the same pair differ by a
  homeomorphism of the plane (`LatticeProb.Peanosphere.exists_homeomorph`), which carries the triple points of one
  curve onto those of the other; the curve of a valid environment is a Peanosphere curve of its boundary-length pair
  (`MatedCRTEnv.IsValid.exists_curve_peanosphere`).
* `matingOfTreesCellSideIdentity_of_literature`: `MatingOfTreesCellSideIdentity 𝒮` from the two named hypotheses.

Named hypotheses (literature, on general objects):
* `PlanarBMNoTwoSidedConePoints` (Le Gall, *Some properties of planar Brownian motion*, Chapter III, Theorem 3(i)),
  proved as `MatedCRT.planarBMNoTwoSidedConePoints` (`PlanarBMConePoints/Holds.lean`).
* `CorrelatedBMTraversalTriplePointsNoContinuum` (Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem 1.9 and
  Lemmas 8.8, 8.11, 8.14-8.15; Gwynne–Holden–Miller–Sun, arXiv:1510.04687, Theorem 1.1; for the triple points DMS
  (8.9) and Lemmas 8.12-8.13, Gwynne–Holden–Miller, arXiv:1512.01223, Corollary 6.5 and Example 2.2).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open MatedCRTHarmonic.MatedCRT (Path2 lrCoord IsCorrelatedBM2)
open MatedCRTHarmonic.RouteM (Peanosphere directRel)

namespace MatedCRT

/-! ### No common local minimum of the correlated Brownian pair -/

/-- **Named hypothesis: planar Brownian motion has no two-sided cone points of angle less than `π`.** It is proved as
`MatedCRT.planarBMNoTwoSidedConePoints` (`PlanarBMConePoints/Holds.lean`).

Let `μ` be the law of a two-sided standard planar Brownian motion `w` (`IsCorrelatedBM2 (√2) μ`: the coordinates are
independent two-sided standard Brownian motions, `lrCov √2 0 1 = -cos(π/2) = 0`); its restriction to `[0, ∞)` is a
planar Brownian motion started at `0`. A closed wedge with vertex `0` and angle in `(0, π)` is
`{v | 0 ≤ ⟪a, v⟫ ∧ 0 ≤ ⟪b, v⟫}` for its two inward normals `a`, `b`, which are linearly independent
(`a.1 * b.2 - a.2 * b.1 ≠ 0`); conversely every such set is a closed wedge of angle `π - ∠(a, b) ∈ (0, π)`. The
statement: almost surely, no time `t > 0` is a two-sided cone point of `w` for any closed wedge of angle less than
`π`, i.e. there is no `ε ∈ (0, t)` with `w s - w t` in the wedge for all `s ∈ [t - ε, t + ε]`.

Source: J.-F. Le Gall, *Some properties of planar Brownian motion*, École d'Été de Probabilités de Saint-Flour XX
(1990), Lecture Notes in Math. 1527, Chapter III, Theorem 3(i), p. 136: "if `α ∈ (0, π)`, `Γ_α = ∅`" almost surely,
where `Γ_α` is the set of two-sided cone points with angle `α` (closed wedges, all directions); a cone point for a
wedge of angle `α` is one for every larger angle, so one event serves all `α < π` along `α_k ↑ π`. Localized at
rational times by the Markov property and Brownian scaling. -/
def PlanarBMNoTwoSidedConePoints : Prop :=
  ∀ μ : Measure Path2, IsCorrelatedBM2 (Real.sqrt 2) μ → ∀ᵐ w ∂μ, ∀ t : ℝ, 0 < t →
    ∀ a b : ℝ × ℝ, a.1 * b.2 - a.2 * b.1 ≠ 0 →
      ¬ ∃ ε : ℝ, 0 < ε ∧ ε < t ∧ ∀ s ∈ Icc (t - ε) (t + ε),
        0 ≤ a.1 * ((w s).1 - (w t).1) + a.2 * ((w s).2 - (w t).2) ∧
          0 ≤ b.1 * ((w s).1 - (w t).1) + b.2 * ((w s).2 - (w t).2)

/-- **A correlated Brownian pair has no common local minimum of its coordinates** (`CorrelatedBMNoCommonLocalMin`;
written answer MQ-sbl-39, section B, lines 41-47), from Le Gall's theorem on cone points
(`PlanarBMNoTwoSidedConePoints`). With `ρ = lrCov γ 0 1 = -cos(πγ²/4) ∈ (-1, 1)`, `A = √(2(1 + ρ))` and
`B = √(2(1 - ρ))`, the whitened path `W = whitenAt γ (-n)` has `A ΔW₁ = ΔL + ΔR` and `B ΔW₂ = ΔL - ΔR` for the
increments from the time `u = -n + t`; so `ΔL ≥ 0` and `ΔR ≥ 0` say that `ΔW` lies in the wedge with inward normals
`(A, B)` and `(A, -B)`, which are linearly independent. The law of `W` is a two-sided standard planar Brownian motion
(`LatticeProb.CorrelatedBM.isCorrelatedBM2_map_whitenAt`); every `u ∈ ℝ` is covered by some `n` with `u + n > 0`. -/
theorem correlatedBMNoCommonLocalMin (hLG : PlanarBMNoTwoSidedConePoints) : CorrelatedBMNoCommonLocalMin := by
  intro γ hγ0 hγ2 μ hμ
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by
    have := mul_pos Real.pi_pos (pow_pos hγ0 2)
    linarith
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have hcos1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at h
  have hcosm1 : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rwa [Real.cos_pi] at h
  have hρ : MatedCRTHarmonic.MatedCRT.lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  set A := Real.sqrt (2 * (1 + MatedCRTHarmonic.MatedCRT.lrCov γ 0 1)) with hAdef
  set B := Real.sqrt (2 * (1 - MatedCRTHarmonic.MatedCRT.lrCov γ 0 1)) with hBdef
  have hA : 0 < A := Real.sqrt_pos.2 (by rw [hρ]; linarith)
  have hB : 0 < B := Real.sqrt_pos.2 (by rw [hρ]; linarith)
  have hn := fun n : ℕ =>
    ae_of_ae_map (LatticeProb.CorrelatedBM.continuous_whitenAt γ (-(n : ℝ))).measurable.aemeasurable
      (hLG _ (LatticeProb.CorrelatedBM.isCorrelatedBM2_map_whitenAt hγ0 hγ2 (-(n : ℝ)) hμ))
  filter_upwards [ae_all_iff.2 hn] with p hp
  rintro u ⟨hL, hR⟩
  have hL' : ∀ᶠ y in 𝓝 u, lrCoord 0 u p ≤ lrCoord 0 y p := hL
  have hR' : ∀ᶠ y in 𝓝 u, lrCoord 1 u p ≤ lrCoord 1 y p := hR
  obtain ⟨n, hnu⟩ := exists_nat_gt (-u)
  obtain ⟨δ, hδ, hδu⟩ := Metric.eventually_nhds_iff.1 (hL'.and hR')
  have ht : 0 < u + n := by linarith
  refine hp n (u + n) ht (A, B) (A, -B) (fun h => by nlinarith [mul_pos hA hB])
    ⟨min (δ / 2) ((u + n) / 2), lt_min (half_pos hδ) (half_pos ht),
      (min_le_right _ _).trans_lt (half_lt_self ht), fun s hs => ?_⟩
  have hy : dist (-(n : ℝ) + s) u < δ := by
    rw [Real.dist_eq, abs_lt]
    have h1 := hs.1
    have h2 := hs.2
    have h3 : min (δ / 2) ((u + n) / 2) ≤ δ / 2 := min_le_left _ _
    constructor <;> linarith
  obtain ⟨hyL, hyR⟩ := hδu hy
  have hyL' : (p u).1 ≤ (p (-(n : ℝ) + s)).1 := hyL
  have hyR' : (p u).2 ≤ (p (-(n : ℝ) + s)).2 := hyR
  have hqt : -(n : ℝ) + (u + n) = u := by ring
  have hW : ∀ v, LatticeProb.CorrelatedBM.whitenAt γ (-(n : ℝ)) p v =
      (((p (-(n : ℝ) + v)).1 + (p (-(n : ℝ) + v)).2 - ((p (-(n : ℝ))).1 + (p (-(n : ℝ))).2)) / A,
        ((p (-(n : ℝ) + v)).1 - (p (-(n : ℝ) + v)).2 - ((p (-(n : ℝ))).1 - (p (-(n : ℝ))).2)) / B) :=
    fun v => rfl
  rw [hW s, hW (u + n), hqt]
  dsimp only
  rw [div_sub_div_same, div_sub_div_same, neg_mul, mul_div_cancel₀ _ hA.ne', mul_div_cancel₀ _ hB.ne']
  constructor <;> linarith

/-! ### Triple points of the curve of a valid environment -/

/-- **Named hypothesis: the space-filling SLE traversal of a correlated Brownian pair, and its triple points.**
PENDING TRUTH CHECK.

For `0 < γ < 2` and the law `μ` of the `γ`-correlated two-sided Brownian pair (`IsCorrelatedBM2 γ μ`), for
`μ`-almost every pair `p = (L, R)` there is a curve `η : ℝ → ℂ`, the whole-plane space-filling SLE_κ,
`κ = 16/γ² > 4`, parametrized by `γ`-LQG area on the `γ`-quantum cone whose (normalized) boundary-length pair is `p`,
such that
* `η` is continuous, onto `ℂ` and proper (`η t → ∞` as `|t| → ∞`; transience, DMS Lemma 8.11);
* times identified directly by `L` or by `R` are merged by `η`, and `η s = η t` only for times equivalent under the
  equivalence generated by these direct identifications (DMS Lemmas 8.8 and 8.14, with Lemmas 8.9 and 8.15);
* the points visited at least three times by `η` (`curveTriplePoints`) contain no continuum of positive diameter
  (written answer MQ-sbl-39, section A, lines 5-27: for `κ ≥ 8` the set is countable, DMS (8.9) and
  Lemmas 8.12-8.13; for `4 < κ < 8` its Hausdorff dimension is at most `3(8 - κ)/8`, Gwynne–Holden–Miller,
  arXiv:1512.01223, Corollary 6.5, below the dimension `1 + 2/κ` of every frontier subarc, proof of Example 2.2).

That the pair is the boundary-length pair of whole-plane space-filling SLE_κ on the `γ`-quantum cone is
Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem 1.9 (`κ ≤ 8`), and Gwynne–Holden–Miller–Sun,
arXiv:1510.04687, Theorem 1.1 (`κ > 8`), after dividing the length coordinates by their common standard deviation
at time one (which preserves the direct identifications). The curve at the pair is the traversal attached by the
conditional law of the curve given its boundary-length pair (answer line 37). -/
def CorrelatedBMTraversalTriplePointsNoContinuum : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
    ∀ᵐ p ∂μ, ∃ η : ℝ → ℂ, Continuous η ∧ Function.Surjective η ∧
      Tendsto η (cocompact ℝ) (cocompact ℂ) ∧
      (∀ s t, (directRel (fun u => (p u).1) s t ∨ directRel (fun u => (p u).2) s t) → η s = η t) ∧
      (∀ s t, η s = η t → Relation.EqvGen
        (fun a b => directRel (fun u => (p u).1) a b ∨ directRel (fun u => (p u).2) a b) s t) ∧
      ¬ ContainsNondegenerateContinuum (curveTriplePoints η)

/-- **Triple points of two Peanosphere curves of the same pair** (written answer MQ-sbl-39, line 39). Two Peanosphere
curves `η`, `ξ` of the same pair differ by a homeomorphism `e` of the plane, `e ∘ η = ξ`
(`LatticeProb.Peanosphere.exists_homeomorph`). The inverse homeomorphism carries a continuum of positive diameter
inside the triple points of `ξ` to one inside the triple points of `η`. -/
theorem not_containsNondegenerateContinuum_curveTriplePoints_of_peanosphere {p : Path2} {η ξ : ℝ → ℂ}
    (hη : Peanosphere p η) (hξ : Peanosphere p ξ)
    (h : ¬ ContainsNondegenerateContinuum (curveTriplePoints η)) :
    ¬ ContainsNondegenerateContinuum (curveTriplePoints ξ) := by
  obtain ⟨e, he⟩ := LatticeProb.Peanosphere.exists_homeomorph hη hξ
  rintro ⟨K, hKsub, hKc, hKconn, hKd⟩
  refine h ⟨e.symm '' K, ?_, hKc.image e.symm.continuous,
    hKconn.image _ e.symm.continuous.continuousOn, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t₁, t₂, t₃, h12, h23, h1, h2, h3⟩ := hKsub hz
    show ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ η t₁ = e.symm z ∧ η t₂ = e.symm z ∧ η t₃ = e.symm z
    refine ⟨t₁, t₂, t₃, h12, h23, ?_, ?_, ?_⟩
    · rw [← h1, ← he, e.symm_apply_apply]
    · rw [← h2, ← he, e.symm_apply_apply]
    · rw [← h3, ← he, e.symm_apply_apply]
  · have hnt : K.Nontrivial := by
      by_contra hn
      rw [Set.not_nontrivial_iff] at hn
      rw [Metric.diam_subsingleton hn] at hKd
      exact lt_irrefl _ hKd
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact (dist_pos.2 (e.symm.injective.ne hxy)).trans_le
      (Metric.dist_le_diam_of_mem (hKc.image e.symm.continuous).isBounded ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- **The triple points of every Peanosphere curve of the pair contain no continuum** (written answer MQ-sbl-39,
lines 37-39). For almost every correlated Brownian pair, the traversal of `CorrelatedBMTraversalTriplePointsNoContinuum`
together with the conditions on the pair alone carried by any Peanosphere curve `ξ` of the pair is a Peanosphere
curve, so the triple points transfer from it to `ξ`. -/
theorem ae_forall_peanosphere_not_containsNondegenerateContinuum
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ p ∂μ, ∀ ξ : ℝ → ℂ, Peanosphere p ξ → ¬ ContainsNondegenerateContinuum (curveTriplePoints ξ) := by
  filter_upwards [hA γ hγ0 hγ2 μ hμ] with p hp ξ hξ
  obtain ⟨η, hc, hs, ht, hm, ho, hnc⟩ := hp
  exact not_containsNondegenerateContinuum_curveTriplePoints_of_peanosphere
    ⟨hc, hs, ht, hm, ho, hξ.liminf_L, hξ.liminf_R, hξ.locMinDistinct⟩ hξ hnc

/-- **The triple points of the curve of a valid environment contain no continuum** (`ValidEnvTriplePointsNoContinuum`;
written answer MQ-sbl-39, lines 28-39), from `CorrelatedBMTraversalTriplePointsNoContinuum`. In a valid environment
the curve is almost surely a Peanosphere curve of the boundary-length pair `S.bm`
(`MatedCRTEnv.IsValid.exists_curve_peanosphere`), whose law is the correlated Brownian law (coupling field
`boundaryLawBM`). -/
theorem validEnvTriplePointsNoContinuum {𝒮 : SpaceFillingSLEModel}
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) : ValidEnvTriplePointsNoContinuum 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS
  obtain ⟨ηc, hηc, hP, -⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hC, -⟩ := hS.matingOfTrees
  have hbm : AEMeasurable S.bm S.P := hC.measurable_curves.2.2.2.aemeasurable
  have hT := ae_of_ae_map hbm
    (ae_forall_peanosphere_not_containsNondegenerateContinuum hA hγ0 hγ2 hC.boundaryLawBM)
  filter_upwards [hηc, hP, hT] with ω hηω hPω hTω
  rw [← hηω]
  exact hTω _ hPω

/-- **The multiplicities of the mated-CRT map are the frontier-side multiplicities of the cells**
(`MatingOfTreesCellSideIdentity`), from the named literature hypotheses `PlanarBMNoTwoSidedConePoints` (Le Gall) and
`CorrelatedBMTraversalTriplePointsNoContinuum` (Duplantier–Miller–Sheffield; Gwynne–Holden–Miller–Sun;
Gwynne–Holden–Miller). -/
theorem matingOfTreesCellSideIdentity_of_literature {𝒮 : SpaceFillingSLEModel}
    (hLG : PlanarBMNoTwoSidedConePoints) (hA : CorrelatedBMTraversalTriplePointsNoContinuum) :
    MatingOfTreesCellSideIdentity 𝒮 :=
  matingOfTreesCellSideIdentity_of_valid (correlatedBMNoCommonLocalMin hLG) (validEnvTriplePointsNoContinuum hA)

end MatedCRT
