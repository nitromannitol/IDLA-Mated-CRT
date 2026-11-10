import MatedCRT.FirstPass.S2g.HalfBallFamily
import HarmonicBalls.Draft.Section3
import HarmonicBalls.Draft.Section5
import MatedCRT.FirstPass.Frozen.S2g

/-! # Source pathwise inputs from the Draft statements of Harmonic Balls (fp-S2g, q1)

Reduction of the pathwise half-ball inputs `ConePathwiseHalfBallInputs` (HalfBallFamily.lean) of the whole-plane source
to the Draft statements of Harmonic Balls (arXiv:2208.11795): `ClusterOpenLaplacianStmt` (Lemma 3.2),
`LeastSupersolutionMemStmt` (Section 3), `ClusterConservationOfMassStmt` (Lemma 3.4) and `ClusterMonotoneStmt` (Lemma 3.3).
Terminology: Armitage-Gardiner (obstacle problem, least superharmonic majorant), Duplantier-Sheffield (LQG measure).

Proved here, deterministic or Draft-level:
* `hasLaplacian_congr_restrict`: `HasLaplacian` depends only on the restriction to the open set `U`;
* `restrict_regularized_eq`, `hasLaplacian_regularized_of_raw`: the Laplacian clause of `RadiusThreeQuartersData` with the
  regularized cluster `interior (closure Λ)` from the raw cluster `Λ`, under the radius-3/4 boundary-nullness;
* `radiusThreeQuartersData_of_raw`, `leastSupersolution_eq_zero_of_sphere`: the radius-3/4 data at one time;
* `monotoneOn_regularizedCluster_of_monotone_cluster`: monotonicity of the regularized clusters;
* `ae_pathwise_part_of_draft`: the locally finite, monotonicity and radius-3/4 clauses almost surely, from the Draft
  statements, with `RadiusThreeQuartersBoundaryNull` as an explicit hypothesis.

NOT derived here (NEW, see the report): `RadiusThreeQuartersBoundaryNull` (radius 3/4 boundary-nullness of the raw clusters
for every `t > 0`; the Draft `ClusterBoundaryMeasureZeroStmt` is radius 1 with closure in `B_1`), the Hausdorff continuity
on `(0, T + ε)` (clause 4), the identification of the family on `(0, T)` (clauses 7-8), and the mass clause 6. -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- `HasLaplacian` depends only on the restriction of the positive measure to the open set `U`: test functions of
`U` vanish off `U`, so their integrals against `μ₁` and `μ₂` agree once `μ₁` and `μ₂` agree on `U`. -/
theorem hasLaplacian_congr_restrict {w : ℂ → ℝ} {μ₁ μ₂ μneg : Measure ℂ} {U : Set ℂ}
    (h : μ₁.restrict U = μ₂.restrict U) (hw : HasLaplacian w μ₁ μneg U) :
    HasLaplacian w μ₂ μneg U := by
  obtain ⟨hloc, hφ⟩ := hw
  refine ⟨hloc, fun φ hφU => ?_⟩
  obtain ⟨i1, i2, heq⟩ := hφ φ hφU
  have hzero : ∀ x, x ∉ U → φ x = 0 := fun x hx => by
    by_contra hne
    exact hx (hφU.2.2 (subset_tsupport φ (Function.mem_support.mpr hne)))
  have hsupp : Function.support φ ⊆ U := fun x hx => hφU.2.2 (subset_tsupport φ hx)
  have hi : ∀ μ : Measure ℂ, Integrable φ (μ.restrict U) ↔ Integrable φ μ := fun μ =>
    integrableOn_iff_integrable_of_support_subset hsupp
  have hint : ∀ μ : Measure ℂ, ∫ x, φ x ∂(μ.restrict U) = ∫ x, φ x ∂μ := fun μ =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x hx)
  have hmeas : ∫ x, φ x ∂μ₁ = ∫ x, φ x ∂μ₂ :=
    (hint μ₁).symm.trans ((congrArg (fun m : Measure ℂ => ∫ x, φ x ∂m) h).trans (hint μ₂))
  have i1' : Integrable φ (μ₂.restrict U) := by
    rw [← h]
    exact (hi μ₁).mpr i1
  exact ⟨(hi μ₂).mp i1', i2, by rw [hmeas] at heq; exact heq⟩

/-- The regularized cluster `interior (closure Λ)` of an open set `Λ` exceeds `Λ` only inside the frontier of `Λ`. -/
theorem interior_closure_diff_subset_frontier {Λ : Set ℂ} (hΛ : IsOpen Λ) :
    interior (closure Λ) \ Λ ⊆ frontier Λ := by
  intro x hx
  show x ∈ closure Λ \ interior Λ
  refine ⟨interior_subset hx.1, ?_⟩
  rw [hΛ.interior_eq]
  exact hx.2

/-- Restriction to `U` of the regularized cluster: if the raw cluster `Λ` is open and `μ` does not charge the frontier of
`Λ` inside `U`, then `μ` restricted to `interior (closure Λ)` and `μ` restricted to `Λ` agree on `U`; the correction
`ν|∂Λ` of HB Lemma 3.2 (`ν ≤ μ` on `U`) vanishes on `U`. -/
theorem restrict_regularized_eq {μ ν : Measure ℂ} {Λ U : Set ℂ} (hΛ : IsOpen Λ) (hU : MeasurableSet U)
    (hnull : μ.restrict U (frontier Λ) = 0) (hν : ν.restrict U ≤ μ.restrict U) :
    (μ.restrict (interior (closure Λ))).restrict U =
      (μ.restrict Λ + ν.restrict (frontier Λ)).restrict U := by
  have hF : MeasurableSet (frontier Λ) := isClosed_frontier.measurableSet
  have hν0 : (ν.restrict (frontier Λ)).restrict U = 0 := by
    have h1 : ν.restrict U (frontier Λ) = 0 :=
      le_antisymm ((Measure.le_iff'.mp hν (frontier Λ)).trans_eq hnull) zero_le
    rw [Measure.restrict_restrict hU, Measure.restrict_eq_zero, inter_comm, ← Measure.restrict_apply hF]
    exact h1
  have hnull' : μ (frontier Λ ∩ U) = 0 := by
    rw [Measure.restrict_apply hF] at hnull
    exact hnull
  have hΛ' : (μ.restrict (interior (closure Λ))).restrict U = (μ.restrict Λ).restrict U := by
    rw [Measure.restrict_restrict hU, Measure.restrict_restrict hU]
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · refine measure_mono_null ?_ hnull'
      intro x hx
      exact ⟨interior_closure_diff_subset_frontier hΛ ⟨hx.1.2, fun h => hx.2 ⟨hx.1.1, h⟩⟩, hx.1.1⟩
    · refine measure_mono_null ?_ measure_empty
      intro x hx
      exact (hx.2 ⟨hx.1.1, interior_maximal subset_closure hΛ hx.1.2⟩).elim
  rw [hΛ', Measure.restrict_add, hν0, add_zero]

/-- Laplacian clause with the regularized cluster: `Δw = μ|Λ + ν|∂Λ` on `U` becomes `Δw = μ|Λ̂` on `U`, where `Λ̂` is the
regularized cluster, under the boundary-nullness of `Λ` inside `U`. -/
theorem hasLaplacian_regularized_of_raw {μ ν : Measure ℂ} {Λ U : Set ℂ} {w : ℂ → ℝ} (hΛ : IsOpen Λ)
    (hU : MeasurableSet U) (hnull : μ.restrict U (frontier Λ) = 0) (hν : ν.restrict U ≤ μ.restrict U)
    (hw : HasLaplacian w (μ.restrict Λ + ν.restrict (frontier Λ)) 0 U) :
    HasLaplacian w (μ.restrict (interior (closure Λ))) 0 U :=
  hasLaplacian_congr_restrict (restrict_regularized_eq hΛ hU hnull hν).symm hw

/-- The least supersolution vanishes on the sphere `∂B_{3/4}` when the odometer does: the Green function of the ball is
`0` off the ball (`greenFunction`, junk value), so `odometer = leastSupersolution` there. -/
theorem leastSupersolution_eq_zero_of_sphere {μ : Measure ℂ} {t : ℝ}
    (hodo : ∀ x ∈ sphere (0 : ℂ) (3 / 4), odometer μ (3 / 4) 0 t x = 0) :
    ∀ x ∈ sphere (0 : ℂ) (3 / 4), leastSupersolution μ (3 / 4) 0 t x = 0 := by
  intro x hx
  have hG : greenFunction (ball (0 : ℂ) (3 / 4)) 0 x = 0 := by
    unfold greenFunction
    split_ifs with h1
    · exfalso
      have h2 := mem_ball.mp h1.2.1
      rw [mem_sphere.mp hx] at h2
      exact lt_irrefl _ h2
    · rfl
  have h := hodo x hx
  unfold odometer at h
  rw [hG, mul_zero, add_zero] at h
  exact h

/-- Radius-`3/4` obstacle data at one time `t`, from the raw-cluster facts (HB Lemma 3.2 at `r = 3/4`, `z = 0`), the
boundary vanishing (HB Lemma 3.4) and the boundary-nullness `hnull`, which is NOT in the Draft (explicit hypothesis). -/
theorem radiusThreeQuartersData_of_raw {μ ν : Measure ℂ} {t : ℝ}
    (hopen : IsOpen (cluster μ (3 / 4) 0 t))
    (hsup : leastSupersolution μ (3 / 4) 0 t ∈ supersolutions μ (3 / 4) 0 t)
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), leastSupersolution μ (3 / 4) 0 t x = 0)
    (hν : ν.restrict (ball (0 : ℂ) (3 / 4)) ≤ μ.restrict (ball (0 : ℂ) (3 / 4)))
    (hlap : HasLaplacian (leastSupersolution μ (3 / 4) 0 t)
      (μ.restrict (cluster μ (3 / 4) 0 t) + ν.restrict (frontier (cluster μ (3 / 4) 0 t))) 0
      (ball (0 : ℂ) (3 / 4)))
    (hnull : μ.restrict (ball (0 : ℂ) (3 / 4)) (frontier (cluster μ (3 / 4) 0 t)) = 0) :
    RadiusThreeQuartersData μ t :=
  ⟨hopen, hsup, hsph, hasLaplacian_regularized_of_raw hopen measurableSet_ball hnull hν hlap⟩

/-- Monotonicity of the regularized clusters from the monotonicity of the raw clusters (interior and closure are monotone). -/
theorem monotoneOn_regularizedCluster_of_monotone_cluster {μ : Measure ℂ}
    (hmono : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → cluster μ (3 / 4) 0 t₁ ⊆ cluster μ (3 / 4) 0 t₂) :
    MonotoneOn (regularizedCluster μ (3 / 4) 0) (Ioi 0) := by
  intro t₁ ht₁ t₂ _ h12
  exact interior_mono (closure_mono (hmono t₁ t₂ (mem_Ioi.mp ht₁) h12))

/-- NEW hypothesis (q1, fp-S2g; not in the Draft, not frozen): radius-`3/4` boundary-nullness of the raw clusters of the
source, for every `t > 0`: `μ (∂Λ^{3/4}_t ∩ B_{3/4}) = 0`. The Draft gives the radius-1 analogue only, with closure in `B_1`
(`ClusterBoundaryMeasureZeroStmt`, HB Draft/Section5.lean:155). -/
def RadiusThreeQuartersBoundaryNull (μ : Measure ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → μ.restrict (ball (0 : ℂ) (3 / 4)) (frontier (cluster μ (3 / 4) 0 t)) = 0

/-- Almost surely, for the whole-plane source `μ` of `IsLQGMeasureOfField P γ γ`: the radius-3/4 data holds at every `t > 0`
(from `ClusterOpenLaplacianStmt`, `LeastSupersolutionMemStmt`, `ClusterConservationOfMassStmt`), given the explicit
boundary-nullness `hnull`. The monotonicity (`ClusterMonotoneStmt`) and local finiteness (`IsLQGLimit`) clauses are included. -/
theorem ae_pathwise_part_of_draft {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hQ : γ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hW : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ γ hcirc μ)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hnull : ∀ᵐ ω ∂P, RadiusThreeQuartersBoundaryNull (μ ω)) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧ (∀ t : ℝ, 0 < t → RadiusThreeQuartersData (μ ω) t) ∧
      MonotoneOn (regularizedCluster (μ ω) (3 / 4) 0) (Ioi 0) := by
  have hL' := hL
  unfold IsLQGMeasureOfField IsLQGMeasure at hL'
  filter_upwards [hL', hOpen γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL, hSup γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL,
    hCons γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL, hMono γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL, hnull]
    with ω hLω hO hS hC' hM hN
  refine ⟨hLω.isLocallyFiniteMeasure, fun t ht => ?_, ?_⟩
  · obtain ⟨hopenC, _, ν, _, _, hle, hlap, _⟩ := hO t (3 / 4) ht (by norm_num) 0 (mem_ball_self (by norm_num))
    have hsph := leastSupersolution_eq_zero_of_sphere
      (fun x hx => (hC' (3 / 4) t (by norm_num) ht 0 (mem_ball_self (by norm_num))).2.1 x hx)
    exact radiusThreeQuartersData_of_raw hopenC
      ((hS t (3 / 4) ht (by norm_num) 0 (mem_ball_self (by norm_num))).2.2) hsph hle hlap (hN t ht)
  · exact monotoneOn_regularizedCluster_of_monotone_cluster
      (fun t₁ t₂ h1 h12 => hM t₁ t₂ (3 / 4) h1 h12 (by norm_num) 0 (mem_ball_self (by norm_num)))

/-- Almost surely, the mass clause: `μ(Λ_t) = t` whenever `closure Λ_t ⊆ B_{3/4}` (HB Lemma 3.4 at `r = 3/4`), from the
Draft clause and the boundary-nullness `hnull` (the frontier lies in `B_{3/4}`, so the restricted measure is `μ`). -/
theorem ae_mass_of_draft {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hQ : γ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hW : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ γ hcirc μ)
    (hCons : ClusterConservationOfMassStmt.{0}) (hnull : ∀ᵐ ω ∂P, RadiusThreeQuartersBoundaryNull (μ ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → closure (cluster (μ ω) (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) →
      μ ω (cluster (μ ω) (3 / 4) 0 t) = ENNReal.ofReal t := by
  filter_upwards [hCons γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL, hnull] with ω hC' hN
  intro t ht hcl
  have hc := hC' (3 / 4) t (by norm_num) ht 0 (mem_ball_self (by norm_num))
  have hF : frontier (cluster (μ ω) (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) := frontier_subset_closure.trans hcl
  have h0 : μ ω (frontier (cluster (μ ω) (3 / 4) 0 t)) = 0 := by
    have h1 := hN t ht
    rw [Measure.restrict_apply' measurableSet_ball, inter_eq_left.mpr hF] at h1
    exact h1
  exact hc.2.2 hcl h0

/-- Bounded stopping set (clause 6 of `ConePathwiseHalfBallInputs`): if `Λ̂_t ⊆ B_{1/2}` then `closure Λ_t ⊆ B_{3/4}` (the raw
clusters are open, `Λ_t ⊆ Λ̂_t`), so `t = μ(Λ_t) ≤ μ(B_{3/4})` by the mass clause `hmass`. -/
theorem bddAbove_of_mass {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hopen : ∀ t : ℝ, 0 < t → IsOpen (cluster μ (3 / 4) 0 t))
    (hmass : ∀ t : ℝ, 0 < t → closure (cluster μ (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) →
      μ (cluster μ (3 / 4) 0 t) = ENNReal.ofReal t) :
    BddAbove {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} := by
  refine ⟨(μ (ball (0 : ℂ) (3 / 4))).toReal, fun t ht => ?_⟩
  obtain ⟨ht0, hsub⟩ := ht
  have hcl : closure (cluster μ (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) := by
    have h1 : closure (cluster μ (3 / 4) 0 t) ⊆ closure (regularizedCluster μ (3 / 4) 0 t) :=
      closure_mono (interior_maximal subset_closure (hopen t ht0))
    have h2 : closure (regularizedCluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) := by
      rw [← closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      exact closure_mono hsub
    exact h1.trans (h2.trans (closedBall_subset_ball (by norm_num)))
  have hle : μ (cluster μ (3 / 4) 0 t) ≤ μ (ball (0 : ℂ) (3 / 4)) :=
    measure_mono (fun x hx => hx.1)
  rw [hmass t ht0 hcl] at hle
  have hfin : μ (ball (0 : ℂ) (3 / 4)) ≠ ⊤ := measure_ball_lt_top.ne
  have h3 := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_ofReal ht0.le] at h3

/-- **Pathwise inputs of the whole-plane source (q1, fp-S2g; Draft reduction).** Almost surely `ConePathwiseHalfBallInputs`
holds for `μ ω`, given: the Draft statements (clauses 1-3, 6); the frozen initial confinement `FrozenHBInitialConfinement`
(clause 5); the radius-3/4 boundary-nullness `hnull` (NEW, not in the Draft); and three NEW hypotheses not in the Draft,
namely the Hausdorff continuity `hcont` (clause 4, CHATGPT-q1-open-steps.md H5), the harmonic-ball property on `(0,T)`
`hharm` (clause 7) and the conditions `hcond` (clause 8), which need the identification H3 of the regularized clusters. -/
theorem ae_conePathwiseHalfBallInputs_of_draft {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hQ : γ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hW : IsWholePlaneGFF P hC hcirc)
    (hL : IsLQGMeasureOfField P γ γ hcirc μ)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hnull : ∀ᵐ ω ∂P, RadiusThreeQuartersBoundaryNull (μ ω))
    (hcont : ∀ᵐ ω ∂P, ∃ ε : ℝ, 0 < ε ∧ HausdorffContinuousOn (regularizedCluster (μ ω) (3 / 4) 0)
      (Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} + ε)))
    (hharm : ∀ᵐ ω ∂P, ∀ t ∈ Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}),
      IsHarmonicBall (μ ω) (regularizedCluster (μ ω) (3 / 4) 0 t) 0)
    (hcond : ∀ᵐ ω ∂P, SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) (3 / 4) 0) 0
      (sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)})) :
    ∀ᵐ ω ∂P, ConePathwiseHalfBallInputs (μ ω) := by
  have hconf' := hconf γ hγ0 hγ2 Ω P hC hcirc μ inferInstance hW hL
  have hpart := ae_pathwise_part_of_draft hγ0 hγ2 hQ hW hL hOpen hSup hCons hMono hnull
  have hmass := ae_mass_of_draft hγ0 hγ2 hQ hW hL hCons hnull
  filter_upwards [hpart, hmass, hconf', hcont, hharm, hcond,
    hOpen γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL] with ω hp hm hc hcn hh hcd hO
  obtain ⟨hloc, hrad, hmon⟩ := hp
  refine ⟨hloc, hrad, hmon, hcn, hc, ?_, hh, hcd⟩
  have : IsLocallyFiniteMeasure (μ ω) := hloc
  exact bddAbove_of_mass (fun t ht => (hO t (3 / 4) ht (by norm_num) 0 (mem_ball_self (by norm_num))).1) hm

end MatedCRT
