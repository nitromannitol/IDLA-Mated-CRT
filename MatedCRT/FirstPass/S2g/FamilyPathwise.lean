import MatedCRT.FirstPass.S2g.HalfBallFamily
import MatedCRT.FirstPass.S2g.SourceFamily

/-! # Pathwise clauses from one Theorem 5.5 family (fp-S2g, q1; operator note 00:50 UTC)

Let `μ` be a whole-plane source, `A_t = regularizedCluster μ (3/4) 0 t`, and let `Λ` be a family of Theorem 5.5
(`IsRegularizedClusterFamily μ Λ 0`) with `Λ_t` a harmonic ball for `t > 0`. Put
`S = {t > 0 : A_t ⊆ B_{1/2}}` and `T = sup S`. The clauses 3, 5, 8, 9 of `ConePathwiseHalfBallInputs` follow
deterministically: `Λ_t = A_t` for `0 < t < T`, and `Λ = A` on a right neighbourhood of `T` (the Hausdorff continuity of
`Λ` at `T` and the global-to-local clause of Theorem 5.5). Terminology: Armitage-Gardiner (regularized clusters),
Armstrong-Kuusi-Mourrat (harmonic balls, Theorem 1.1 and Theorem 5.5), Duplantier-Sheffield (LQG source). -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- Left limits stay in the closed half-ball: if `Λ` is Hausdorff continuous on `(0,∞)` and `Λ_s ⊆ B_{1/2}` for all
`0 < s < T`, then `Λ_T ⊆ closedBall 0 (1/2)` (every point of `Λ_T` is a Hausdorff limit of points of `Λ_s`). -/
theorem subset_closedBall_half_of_hausdorff_left {Λ : ℝ → Set ℂ} {T : ℝ} (hT : 0 < T)
    (hcont : HausdorffContinuousOn Λ (Ioi 0))
    (hL : ∀ s : ℝ, 0 < s → s < T → Λ s ⊆ ball (0 : ℂ) (1 / 2)) :
    Λ T ⊆ closedBall (0 : ℂ) (1 / 2) := by
  intro x hx
  by_contra hxn
  have hxn' : 1 / 2 < dist x 0 := lt_of_not_ge (fun h => hxn (mem_closedBall.2 h))
  have hev := hcont T (show T ∈ Ioi (0 : ℝ) from hT) (ENNReal.ofReal ((dist x 0 - 1 / 2) / 2))
    (ENNReal.ofReal_pos.2 (by linarith))
  rw [isOpen_Ioi.nhdsWithin_eq (show T ∈ Ioi (0 : ℝ) from hT)] at hev
  obtain ⟨s, hE, hs⟩ := ((eventually_nhdsWithin_of_eventually_nhds (s := Iio T) hev).and
    (Ioo_mem_nhdsLT hT)).exists
  have hE' : hausdorffEDist (Λ T) (Λ s) < ENNReal.ofReal ((dist x 0 - 1 / 2) / 2) := by
    rwa [hausdorffEDist_comm]
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hE'
  have hxy' : dist x y < (dist x 0 - 1 / 2) / 2 := edist_lt_ofReal.1 hxy
  have hy' : dist y 0 < 1 / 2 := mem_ball.1 (hL s hs.1 hs.2 hy)
  have htri := dist_triangle x y 0
  linarith

/-- Right neighbourhood of the canonical time: if `Λ` is Hausdorff continuous on `(0,∞)` and `Λ_T ⊆ closedBall 0 (1/2)`,
then for some `δ > 0` every `Λ_s` with `T < s < T + δ` lies in `B_{9/16}`. -/
theorem exists_right_neighbourhood_subset {Λ : ℝ → Set ℂ} {T : ℝ} (hT : 0 < T)
    (hcont : HausdorffContinuousOn Λ (Ioi 0)) (hT' : Λ T ⊆ closedBall (0 : ℂ) (1 / 2)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, T < s → s < T + δ → Λ s ⊆ ball (0 : ℂ) (9 / 16) := by
  have hev := hcont T (show T ∈ Ioi (0 : ℝ) from hT) (ENNReal.ofReal (1 / 16))
    (ENNReal.ofReal_pos.2 (by norm_num))
  rw [isOpen_Ioi.nhdsWithin_eq (show T ∈ Ioi (0 : ℝ) from hT)] at hev
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun s hs1 hs2 y hy => ?_⟩
  have hdist : dist s T < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 hs1)]
    linarith
  have hE := hball hdist
  obtain ⟨x, hx, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hy hE
  have hxy' : dist y x < 1 / 16 := edist_lt_ofReal.1 hxy
  have hx' : dist x 0 ≤ 1 / 2 := mem_closedBall.1 (hT' hx)
  have htri := dist_triangle y x 0
  exact mem_ball.2 (by linarith)

/-- **Pathwise clauses from one Theorem 5.5 family (deterministic, q1).** Let `Λ` satisfy `IsRegularizedClusterFamily μ Λ 0`
(Theorem 5.5, pathwise), with raw clusters open, compatible at natural radii (Lemma 3.5), monotone regularized clusters and
mass `μ(Λ_t) = t` on `{closure Λ_t ⊆ closedBall(1/2)}`; let the regularized clusters meet `B_{1/2}` at some time, and let
each `Λ_t` be a harmonic ball. Then `μ` satisfies `ConePathwiseHalfBallInputs` with the witness `A_t = regularizedCluster μ (3/4) 0 t`.
The radius-`3/4` data `hrad` is supplied on the half-ball range only (Proposition 5.3 at radius `1` through Lemma 3.5). -/
theorem conePathwiseHalfBallInputs_of_family {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {Λ : ℝ → Set ℂ}
    (hopen : ∀ t : ℝ, 0 < t → IsOpen (cluster μ (3 / 4) 0 t))
    (hrad : ∀ t : ℝ, 0 < t → closure (cluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) →
      RadiusThreeQuartersData μ t)
    (hmono : MonotoneOn (regularizedCluster μ (3 / 4) 0) (Ioi 0))
    (hmass : ∀ t : ℝ, 0 < t → closure (cluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) →
      μ (cluster μ (3 / 4) 0 t) = ENNReal.ofReal t)
    (hconf : ∃ s : ℝ, 0 < s ∧ regularizedCluster μ (3 / 4) 0 s ⊆ ball (0 : ℂ) (1 / 2))
    (hfam : IsRegularizedClusterFamily μ Λ 0)
    (hcomp : ∀ N : ℕ, 0 < N → ClusterCompatibleAt μ (N : ℝ))
    (hHB : ∀ t : ℝ, 0 < t → IsHarmonicBall μ (Λ t) 0) :
    ConePathwiseHalfBallInputs μ := by
  obtain ⟨s0, hs0, hs0B⟩ := hconf
  set S : Set ℝ := {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} with hSdef
  have hSmem : ∀ t ∈ S, 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2) := fun t ht => ht
  -- the canonical time is finite: the mass of a half-ball cluster is at most the mass of `B_1`
  have hBdd : BddAbove S := by
    refine ⟨(μ (ball (0 : ℂ) 1)).toReal, fun t ht => ?_⟩
    obtain ⟨ht0, hsub⟩ := hSmem t ht
    have hcl := closure_cluster_subset_closedBall_half (hopen t ht0) hsub
    have hle : μ (cluster μ (3 / 4) 0 t) ≤ μ (ball (0 : ℂ) 1) :=
      measure_mono fun x hx => closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1) (hcl (subset_closure hx))
    rw [hmass t ht0 hcl] at hle
    exact (ENNReal.ofReal_le_iff_le_toReal measure_ball_lt_top.ne).1 hle
  have hne : S.Nonempty := ⟨s0, hs0, hs0B⟩
  have hT0 : 0 < sSup S := lt_of_lt_of_le hs0 (le_csSup hBdd ⟨hs0, hs0B⟩)
  have hsubT : ∀ t ∈ Ioo 0 (sSup S), regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2) :=
    fun t ht => regularizedCluster_subset_half_of_lt_sSup hmono ⟨s0, hs0, hs0B⟩ ht
  have hclT : ∀ t ∈ Ioo 0 (sSup S), closure (cluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) :=
    fun t ht => closure_cluster_subset_closedBall_half (hopen t ht.1) (hsubT t ht)
  -- identification `Λ_t = A_t` for `0 < t < T` (local-to-global, Lemma 3.5 at the radius `9/16`)
  have hEqLT : ∀ t ∈ Ioo 0 (sSup S), regularizedCluster μ (3 / 4) 0 t = Λ t := fun t ht =>
    (eq_regularizedCluster_of_closure_ball hfam.2.2 hfam.1.isBounded hcomp ht.1 (by norm_num : (0 : ℝ) < 9 / 16)
      (by norm_num) ((hclT t ht).trans (closedBall_subset_ball (by norm_num)))).symm
  have hΛT : Λ (sSup S) ⊆ closedBall (0 : ℂ) (1 / 2) :=
    subset_closedBall_half_of_hausdorff_left hT0 hfam.1.hausdorffContinuousOn
      (fun s h1 h2 => by rw [← hEqLT s ⟨h1, h2⟩]; exact hsubT s ⟨h1, h2⟩)
  have hAT : regularizedCluster μ (3 / 4) 0 (sSup S) = Λ (sSup S) :=
    (eq_regularizedCluster_of_subset_ball hfam.2.2 hT0 (hΛT.trans (closedBall_subset_ball (by norm_num)))).symm
  obtain ⟨δ, hδ, hright⟩ := exists_right_neighbourhood_subset hT0 hfam.1.hausdorffContinuousOn hΛT
  have hEqRight : ∀ t ∈ Ioo 0 (sSup S + δ), regularizedCluster μ (3 / 4) 0 t = Λ t := by
    intro t ht
    rcases lt_trichotomy t (sSup S) with h | h | h
    · exact hEqLT t ⟨ht.1, h⟩
    · rw [h]
      exact hAT
    · exact (eq_regularizedCluster_of_subset_ball hfam.2.2 ht.1 (hright t h ht.2)).symm
  -- Hausdorff continuity on `(0, T + δ)` (clause 5)
  have hcontT : HausdorffContinuousOn (regularizedCluster μ (3 / 4) 0) (Ioo 0 (sSup S + δ)) := by
    intro t ht ε hε
    have h1 := hfam.1.hausdorffContinuousOn t (show t ∈ Ioi (0 : ℝ) from ht.1) ε hε
    have h2 : ∀ᶠ s in 𝓝[Ioo 0 (sSup S + δ)] t, hausdorffEDist (Λ s) (Λ t) < ε :=
      Filter.Eventually.filter_mono (nhdsWithin_mono t Ioo_subset_Ioi_self) h1
    filter_upwards [h2, self_mem_nhdsWithin] with s hs hs'
    rw [hEqRight s hs', hEqRight t ht]
    exact hs
  have hsubIoo : Ioo 0 (sSup S) ⊆ Ioo 0 (sSup S + δ) := Ioo_subset_Ioo_right (by linarith)
  refine ⟨inferInstance, hopen, fun t ht => hrad t ht.1 (hclT t ht), hmono, ⟨δ, hδ, hcontT⟩,
    ⟨s0, hs0, hs0B⟩, hBdd, fun t ht => ?_, ?_⟩
  · rw [hEqLT t ht]
    exact hHB t ht.1
  · exact
    { measure_eq := fun t ht => by rw [hEqLT t ht]; exact hfam.1.measure_eq t ht.1
      measure_frontier := fun t ht => by rw [hEqLT t ht]; exact hfam.1.measure_frontier t ht.1
      isRegularOpen := fun t ht => by rw [hEqLT t ht]; exact hfam.1.isRegularOpen t ht.1
      isBounded := fun t ht => by rw [hEqLT t ht]; exact hfam.1.isBounded t ht.1
      isConnected := fun t ht => by rw [hEqLT t ht]; exact hfam.1.isConnected t ht.1
      mem := fun t ht => by rw [hEqLT t ht]; exact hfam.1.mem t ht.1
      monotoneOn := hmono.mono Ioo_subset_Ioi_self
      hausdorffContinuousOn := fun t ht ε hε =>
        (hcontT t (hsubIoo ht) ε hε).filter_mono (nhdsWithin_mono t hsubIoo)
      iInter_eq := by
        ext x
        simp only [mem_iInter, mem_singleton_iff]
        constructor
        · intro hx
          by_contra hx0
          have hnot : ¬ (∀ t ∈ Ioi (0 : ℝ), x ∈ Λ t) := by
            intro h
            apply hx0
            have hmem : x ∈ ⋂ t ∈ Ioi (0 : ℝ), Λ t := mem_iInter₂.2 h
            rw [hfam.1.iInter_eq] at hmem
            exact hmem
          obtain ⟨t1, ht1, hxt1⟩ : ∃ t1 ∈ Ioi (0 : ℝ), x ∉ Λ t1 := by
            by_contra hc
            exact hnot fun t ht => by
              by_contra h
              exact hc ⟨t, ht, h⟩
          have ht1' : 0 < t1 := ht1
          have hpos : 0 < min t1 (sSup S) / 2 := half_pos (lt_min ht1' hT0)
          have hlt : min t1 (sSup S) / 2 < sSup S := by
            linarith [min_le_right t1 (sSup S)]
          have hle : min t1 (sSup S) / 2 ≤ t1 := by
            linarith [min_le_left t1 (sSup S), lt_min ht1' hT0]
          have hxs := hx (min t1 (sSup S) / 2) ⟨hpos, hlt⟩
          rw [hEqLT _ ⟨hpos, hlt⟩] at hxs
          exact hxt1 (hfam.1.monotoneOn (show min t1 (sSup S) / 2 ∈ Ioi (0 : ℝ) from hpos)
            (show t1 ∈ Ioi (0 : ℝ) from ht1) hle hxs)
        · rintro rfl t ht
          rw [hEqLT t ht]
          exact hfam.1.mem t ht.1 }

end MatedCRT
