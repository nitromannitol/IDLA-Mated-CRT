import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauRadii
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ClusterDecoder
import HarmonicBalls.Proofs.Sec5.ClusterMeasurability
import HarmonicBalls.Proofs.Sec5.RegularizedGeometry

/-! # Measurability of the global radii from canonical bounded-disk raw-cluster codes (Proposition 4.2)

The route for `R_h(q)` and `(h,r) ↦ 1{r ∈ P(h)}`.
Here `Λ t` is the global regularized family of Theorem 5.5 (`IsRegularizedClusterFamily`, HB Section5.lean:88), the raw
cluster in the disk `B_R` is `cluster μ R 0 t` (HB Defs/Obstacle.lean:69, line 592) and the regularized
cluster is `regularizedCluster μ R 0 t = interior (closure (cluster μ R 0 t))` (HB Section5.lean:56,
line 846).

Route, in the paper's order:
1. Canonical codes. On each disk `B_R` the clusters have a version measurable in the measure
   (`exists_measurable_clusterFamily_of_volumeGrowth`, HB PotentialMeasurableDecoder.lean:215) which equals the cluster on
   every locally finite measure with volume growth in `B_R`. The regularization is measurable on all sets
   (`measurable_denseSequenceRegularization`, HB ClusterMeasurability.lean:178), so the dense positivity code of each dense
   point `d_k` is measurable in the measure.
2. Radius from codes. For an open bounded set, the radius is the supremum of the norms of the dense points it contains
   (`familyRadius_eq_iSup_denseSeq`, PlateauRadii.lean:21).
3. Compatibility and boundedness. `closure (Λ t) ⊆ B_s` gives `Λ t = regularizedCluster μ r 0 t` for every `r ≥ s`
   (third conjunct of `IsRegularizedClusterFamily`). Boundedness of `Λ t` supplies such an `s`, so for all large `n` the
   code radius of `B_{n+1}` is the radius of `Λ t`.
4. Limit. The radius is the `limsup` over the disks of measurable functions, hence measurable (almost everywhere, since the
   family is regularized and the volume growth holds only almost surely).
5. Plateau event. `measurableSet_plateauPairsOf` (PlateauAE.lean:50) makes the canonical plateau pairs measurable; the
   plateau event of the family is almost surely the preimage of the canonical plateau set under the measure.

Probability-space and family assumptions (explicit hypotheses only):
* `μ : Ω → Measure ℂ` is `AEMeasurable` for `P`;
* almost surely, for every `n : ℕ`, `μ ω` is locally finite with volume growth `VolumeGrowth (μ ω) (n+1) β⁻ β⁺` for some
  exponents. This is the family-level volume estimate that the HB measurable decoder needs on every disk. The paper's
  `lemma:volume-growth` (idla_mated_crt-corrected.tex:658, Lemma 2.7 / BG20 Lemma A.1) is stated only with polynomially high
  probability on `B_{1-δ}` for the cone field, and the Borel-Cantelli step at radii `2^{-k}` (line 1054) is not a numbered
  Draft statement for every disk; see the report;
* almost surely, `Λ ω` is a regularized cluster family at `0` for `μ ω` (`ExistenceHarmonicBallsStmt`, HB Theorem 5.5,
  HarmonicBalls/Draft/Section5.lean:192; this is the family hypothesis, not a proof of the existence statement).

The locality input `HarmonicBallLocalSetStmt` (HB Proposition 1.3) is not used by this route. The locality route to
almost-everywhere measurability is `aemeasurable_familyRadius_of_regularized` (PlateauRadii.lean:76). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory

/-- The radius read from the dense positivity codes of a raw-cluster family `G` at time `t`:
`codeRadius G t ν = sup_k ‖d_k‖ · 1[d_k ∈ G ν t]` for the dense sequence `d_k = denseSeq ℂ k`. -/
noncomputable def codeRadius (G : Measure ℂ → ℝ → Set ℂ) (t : ℝ) (ν : Measure ℂ) : ℝ :=
  ⨆ k : ℕ, (G ν t).indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ k)

/-- A canonical bounded-disk raw-cluster family for `B_R` centred at `0`: for every time `t` the map `ν ↦ G ν t` is
measurable, and on every locally finite measure with volume growth in `B_R` it equals the regularized raw cluster
`regularizedCluster ν R 0 t` for every positive time `t` (HB Section5.lean:56). -/
structure CanonicalRawClusterFamily (R : ℝ) (G : Measure ℂ → ℝ → Set ℂ) : Prop where
  measurable : ∀ t : ℝ, Measurable fun ν : Measure ℂ => G ν t
  eq_regularizedCluster : ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
    (∃ βminus βplus : ℝ, VolumeGrowth ν R βminus βplus) →
      ∀ t : ℝ, 0 < t → G ν t = regularizedCluster ν R 0 t

/-- Existence of the canonical family on a disk of positive radius: the measurable version of the clusters
(HB PotentialMeasurableDecoder.lean:215), passed through the measurable regularization `denseSequenceRegularization`. -/
theorem exists_canonicalRawClusterFamily {R : ℝ} (hR : 0 < R) :
    ∃ G : Measure ℂ → ℝ → Set ℂ, CanonicalRawClusterFamily R G := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth hR
  let z : ball (0 : ℂ) R := ⟨0, mem_ball_self hR⟩
  refine ⟨fun ν t => if h : 0 < t then denseSequenceRegularization (F ν (z, ⟨t, h⟩)) else ∅, ?_, ?_⟩
  · intro t
    by_cases h : 0 < t
    · simp only [h, reduceDIte]
      exact measurable_denseSequenceRegularization.comp
        ((measurable_pi_apply (z, (⟨t, h⟩ : Ioi (0 : ℝ)))).comp hF)
    · simp only [h, reduceDIte]
      exact measurable_const
  · intro ν hν hV t ht
    obtain ⟨βm, βp, hV'⟩ := hV
    have hopen : IsOpen (cluster ν R 0 t) :=
      (cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
        shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hν hR hV' (mem_ball_self hR) ht).1
    simp only [ht, reduceDIte]
    rw [hFeq ν hν ⟨βm, βp, hV'⟩]
    exact denseSequenceRegularization_eq hopen

/-- The code radius is measurable in the measure: a countable supremum of measurable dense-code indicators. -/
theorem measurable_codeRadius {G : Measure ℂ → ℝ → Set ℂ} (hG : ∀ t : ℝ, Measurable fun ν : Measure ℂ => G ν t)
    (t : ℝ) : Measurable fun ν : Measure ℂ => codeRadius G t ν := by
  classical
  unfold codeRadius
  refine Measurable.iSup fun k => ?_
  have hset : MeasurableSet {ν : Measure ℂ | denseSeq ℂ k ∈ G ν t} :=
    measurableSet_setOfPred.2 ((measurable_pi_apply (denseSeq ℂ k)).comp (hG t))
  have heq : (fun ν : Measure ℂ => (G ν t).indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ k)) =
      fun ν => if denseSeq ℂ k ∈ G ν t then ‖denseSeq ℂ k‖ else 0 := by
    funext ν
    exact Set.indicator_apply _ _ _
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

/-- On a good measure the code radius of the raw cluster in `B_R` is the radius of its regularization. -/
theorem codeRadius_eq_familyRadius {R : ℝ} {G : Measure ℂ → ℝ → Set ℂ} (hG : CanonicalRawClusterFamily R G)
    {ν : Measure ℂ} (hν : IsLocallyFiniteMeasure ν) (hV : ∃ βminus βplus : ℝ, VolumeGrowth ν R βminus βplus)
    {t : ℝ} (ht : 0 < t) :
    codeRadius G t ν = familyRadius (regularizedCluster ν R 0 t) := by
  have hcl : Bornology.IsBounded (cluster ν R 0 t) := Metric.isBounded_ball.subset fun x hx => hx.1
  unfold codeRadius
  rw [hG.eq_regularizedCluster ν hν hV t ht]
  exact (familyRadius_eq_iSup_denseSeq (isOpen_regularizedCluster ν R 0 t)
    (isBounded_regularizedCluster hcl)).symm

/-- Compatibility and boundedness of the global family (HB Section5.lean:88). Since `Λ t` is bounded and contains `0`,
its closure lies in some ball `B_s`, and then `Λ t = regularizedCluster μ r 0 t` for every radius `r ≥ s`. So the
regularized raw clusters of the disks `B_{n+1}` are equal to `Λ t` for all large `n`. -/
theorem eventually_regularizedCluster_eq {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Λ t = regularizedCluster μ ((n : ℝ) + 1) 0 t := by
  obtain ⟨hS, -, hcompat⟩ := hΛ
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 (hS.isBounded t ht)
  refine ⟨⌈|r|⌉₊, fun n hn => hcompat t ht (|r| + 1) (by positivity) ?_ ((n : ℝ) + 1) ?_⟩
  · exact (closure_minimal hr Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by linarith [le_abs_self r]))
  · have hnr : |r| ≤ (n : ℝ) := (Nat.le_ceil |r|).trans (by exact_mod_cast hn)
    linarith

/-- Along the disks `B_{n+1}`, the code radii of a regularized global family are eventually equal to its radius. -/
theorem codeRadius_eventually_eq {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) {ν : Measure ℂ}
    (hgood : ∀ n : ℕ, IsLocallyFiniteMeasure ν ∧ ∃ βminus βplus : ℝ, VolumeGrowth ν ((n : ℝ) + 1) βminus βplus)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily ν Λ 0) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in atTop, codeRadius (G n) t ν = familyRadius (Λ t) := by
  obtain ⟨N, hN⟩ := eventually_regularizedCluster_eq hΛ ht
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨hloc, hV⟩ := hgood n
  rw [codeRadius_eq_familyRadius (hG n) hloc hV ht, hN n hn]

/-- The canonical radius at time `t`: the limit superior over the disks `B_{n+1}` of the code radii. -/
noncomputable def canonicalRadius (G : ℕ → Measure ℂ → ℝ → Set ℂ) (t : ℝ) (ν : Measure ℂ) : ℝ :=
  Filter.limsup (fun n : ℕ => codeRadius (G n) t ν) atTop

/-- The canonical radius is measurable in the measure, for every time. -/
theorem measurable_canonicalRadius {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) (t : ℝ) :
    Measurable fun ν : Measure ℂ => canonicalRadius G t ν :=
  Measurable.limsup (f := fun (n : ℕ) (ν : Measure ℂ) => codeRadius (G n) t ν)
    fun n => measurable_codeRadius (hG n).measurable t

/-- On a good measure with a regularized global family, the canonical radius is the radius of the family. -/
theorem canonicalRadius_eq_familyRadius {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) {ν : Measure ℂ}
    (hgood : ∀ n : ℕ, IsLocallyFiniteMeasure ν ∧ ∃ βminus βplus : ℝ, VolumeGrowth ν ((n : ℝ) + 1) βminus βplus)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily ν Λ 0) {t : ℝ} (ht : 0 < t) :
    canonicalRadius G t ν = familyRadius (Λ t) := by
  unfold canonicalRadius
  rw [Filter.limsup_congr (codeRadius_eventually_eq hG hgood hΛ ht), Filter.limsup_const]

/-- A choice of canonical families on all the disks `B_{n+1}`. -/
theorem exists_canonicalRawClusterFamilies :
    ∃ G : ℕ → Measure ℂ → ℝ → Set ℂ, ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n) := by
  choose G hG using fun n : ℕ => exists_canonicalRawClusterFamily (R := (n : ℝ) + 1) (by positivity)
  exact ⟨G, hG⟩

/-- **A.e. measurability of the rational-time radii from canonical codes**.
Let `μ` be an almost-everywhere measurable random measure such that, almost surely, every `μ ω` has volume growth on every
disk `B_{n+1}`, and `Λ ω` is almost surely a regularized global family at `0`. Then for every `q > 0` (in particular every
rational `q > 0`) the radius `ω ↦ familyRadius (Λ ω q)` is almost everywhere measurable. -/
theorem aemeasurable_familyRadius_of_canonicalCodes {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hvg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IsLocallyFiniteMeasure (μ ω) ∧ ∃ βminus βplus : ℝ, VolumeGrowth (μ ω) ((n : ℝ) + 1) βminus βplus)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0)
    {q : ℝ} (hq : 0 < q) :
    AEMeasurable (fun ω => familyRadius (Λ ω q)) P := by
  obtain ⟨G, hG⟩ := exists_canonicalRawClusterFamilies
  have hmeas : AEMeasurable (fun ω => canonicalRadius G q (μ ω)) P :=
    (measurable_canonicalRadius hG q).comp_aemeasurable hμ
  refine hmeas.congr ?_
  filter_upwards [hvg, hΛ] with ω h1 h2
  exact canonicalRadius_eq_familyRadius hG h1 h2 hq

/-- The measure-level plateau set of the canonical radii, at the rational times of `plateauValuesOf`
(PlateauAE.lean:21). -/
def canonicalPlateauSet (G : ℕ → Measure ℂ → ℝ → Set ℂ) (r : ℝ) : Set (Measure ℂ) :=
  {ν | r ∈ plateauValuesOf (fun q : ℚ => canonicalRadius G (q : ℝ)) ν}

/-- The joint measurability of `(ν, r) ↦ 1{r ∈ P(ν)}` for the canonical plateau values (the paper's `(h,r) ↦ 1{r∈P(h)}`
at the level of measures). -/
theorem measurableSet_canonicalPlateauPairs {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) :
    MeasurableSet {p : Measure ℂ × ℝ | p.2 ∈ plateauValuesOf (fun q : ℚ => canonicalRadius G (q : ℝ)) p.1} :=
  measurableSet_plateauPairsOf (fun q : ℚ => canonicalRadius G (q : ℝ))
    (fun q _ => measurable_canonicalRadius hG (q : ℝ))

/-- The canonical plateau set is measurable in the measure, for every `r`. -/
theorem measurableSet_canonicalPlateauSet {G : ℕ → Measure ℂ → ℝ → Set ℂ}
    (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) (r : ℝ) :
    MeasurableSet (canonicalPlateauSet G r) :=
  (measurableSet_canonicalPlateauPairs hG).preimage (measurable_id.prodMk measurable_const)

/-- **The measurable plateau-membership event.** Let `μ` be as in `aemeasurable_familyRadius_of_canonicalCodes`, with
`Λ` almost surely a regularized global family for `μ`. Then, for every `r`, almost surely the plateau event
`{ω | r ∈ P(Λ ω)}` equals the preimage `μ⁻¹' canonicalPlateauSet G r` of a measurable set of measures. -/
theorem plateau_event_ae_eq_canonical {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hvg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IsLocallyFiniteMeasure (μ ω) ∧ ∃ βminus βplus : ℝ, VolumeGrowth (μ ω) ((n : ℝ) + 1) βminus βplus)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0)
    {G : ℕ → Measure ℂ → ℝ → Set ℂ} (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) (r : ℝ) :
    {ω | r ∈ plateauValues (Λ ω)} =ᵐ[P] μ ⁻¹' canonicalPlateauSet G r := by
  filter_upwards [hvg, hΛ] with ω h1 h2
  have key : ∀ q : ℚ, 0 < (q : ℝ) → canonicalRadius G (q : ℝ) (μ ω) = familyRadius (Λ ω q) :=
    fun q hq => canonicalRadius_eq_familyRadius hG h1 h2 hq
  refine propext ?_
  change r ∈ plateauValues (Λ ω) ↔ r ∈ plateauValuesOf (fun q : ℚ => canonicalRadius G (q : ℝ)) (μ ω)
  unfold plateauValues plateauValuesOf
  constructor
  · rintro ⟨hr, s, t, hs, hst, h1', h2'⟩
    exact ⟨hr, s, t, hs, hst, (key s hs).trans h1', (key t (hs.trans hst)).trans h2'⟩
  · rintro ⟨hr, s, t, hs, hst, h1', h2'⟩
    exact ⟨hr, s, t, hs, hst, (key s hs).symm.trans h1', (key t (hs.trans hst)).symm.trans h2'⟩

/-- **Plateau-membership probability is law-invariant.** If `μ'` and `μ` have the same law (`IdentDistrib μ' μ P P`) and
both families are almost surely regularized with volume growth on every disk, then
`P[r ∈ P(Λ)] = P[r ∈ P(Λ')]` for every `r`. This is the plateau law transfer on the canonical measurable event. -/
theorem plateau_prob_eq_canonical {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ μ' : Ω → Measure ℂ}
    {Λ Λ' : Ω → ℝ → Set ℂ} (hid : IdentDistrib μ' μ P P)
    (hvg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IsLocallyFiniteMeasure (μ ω) ∧ ∃ βminus βplus : ℝ, VolumeGrowth (μ ω) ((n : ℝ) + 1) βminus βplus)
    (hvg' : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IsLocallyFiniteMeasure (μ' ω) ∧ ∃ βminus βplus : ℝ, VolumeGrowth (μ' ω) ((n : ℝ) + 1) βminus βplus)
    (hΛ : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0)
    (hΛ' : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ' ω) (Λ' ω) 0)
    {G : ℕ → Measure ℂ → ℝ → Set ℂ} (hG : ∀ n : ℕ, CanonicalRawClusterFamily ((n : ℝ) + 1) (G n)) (r : ℝ) :
    P {ω | r ∈ plateauValues (Λ ω)} = P {ω | r ∈ plateauValues (Λ' ω)} := by
  rw [measure_congr (plateau_event_ae_eq_canonical hvg hΛ hG r),
    measure_congr (plateau_event_ae_eq_canonical hvg' hΛ' hG r)]
  exact (hid.measure_mem_eq (measurableSet_canonicalPlateauSet hG r)).symm

end MatedCRT
