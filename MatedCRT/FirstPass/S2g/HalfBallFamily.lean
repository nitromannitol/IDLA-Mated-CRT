import MatedCRT.FirstPass.S2g.AllDisksCont
import MatedCRT.FirstPass.S2g.HalfBallPathwise
import MatedCRT.FirstPass.S2g.RadiusContinuity

/-! # Pathwise canonical half-ball family from the radius-3/4 data (fp-S2g, q1; CHATGPT-q1-open-steps.md H6-H8)

The deterministic assembly of `ConeCanonicalHalfBallStep`. The witness is `Λ t = regularizedCluster μ (3/4) 0 t` and the
canonical time is `T = sup {t > 0 : Λ_t ⊆ B_{1/2}}`. The predicate `ConePathwiseHalfBallInputs μ` collects the pathwise
inputs, which are NEW (open) statements about the cone measure, not frozen facts:

* `RadiusThreeQuartersData μ t` at every `t > 0` (the H2/H3 transfer of the radius-3/4 obstacle data);
* monotonicity and Hausdorff continuity of `t ↦ Λ_t` on `(0, ∞)`, boundedness and a small-time inclusion (H4, H5);
* the HB harmonic-ball conditions for the family on `(0, T)` (H6).

Deterministic consequences proved here: the obstacle characterization of the family on `(0, T)` from the radius-3/4 data
(`obstacle_clause_all_radii`), the inclusion `Λ_t ⊆ B_{1/2}` for `t < T` from monotonicity, continuity of the closure radius
(`RadiusContinuity.lean`), and the canonical stopped family (`canonical_witness_of_pathwise`). -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- The radius-`3/4` obstacle data of the measure `μ` at the single time `t`: the raw cluster is open, the least
supersolution at radius `3/4` lies in the supersolutions, vanishes on `∂B_{3/4}`, and has Laplacian `μ|_{Λ_t}` on `B_{3/4}`
(the clauses of `SatisfiesObstacleCharacterizationOn` at radius `3/4`). NEW: a property of the cone measure, not frozen. -/
def RadiusThreeQuartersData (μ : Measure ℂ) (t : ℝ) : Prop :=
  IsOpen (cluster μ (3 / 4) 0 t) ∧
    leastSupersolution μ (3 / 4) 0 t ∈ supersolutions μ (3 / 4) 0 t ∧
    (∀ x ∈ sphere (0 : ℂ) (3 / 4), leastSupersolution μ (3 / 4) 0 t x = 0) ∧
    HasLaplacian (leastSupersolution μ (3 / 4) 0 t) (μ.restrict (regularizedCluster μ (3 / 4) 0 t)) 0
      (ball (0 : ℂ) (3 / 4))

/-- **Obstacle characterization of the regularized-cluster family (deterministic, q1).** If the radius-`3/4` data holds at
each `t ∈ (0,T)` and `Λ_t ⊆ B_{1/2}` there, the family `Λ_t = regularizedCluster μ (3/4) 0 t` satisfies
`SatisfiesObstacleCharacterizationOn` on `(0, T)`: it is `obstacle_clause_all_radii` at each time. -/
theorem satisfiesObstacleCharacterizationOn_of_data {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {T : ℝ}
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hdat : ∀ t ∈ Ioo 0 T, RadiusThreeQuartersData μ t)
    (hsub : ∀ t ∈ Ioo 0 T, regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)) :
    SatisfiesObstacleCharacterizationOn μ (regularizedCluster μ (3 / 4) 0) T := by
  intro t r ht hr hAr ρ hrρ
  obtain ⟨hopen, hmem, hsph, hW⟩ := hdat t ht
  obtain ⟨h1, h2, h3, h4⟩ := obstacle_clause_all_radii hmin hC hGB hpole hopen hmem hsph hW (hsub t ht) hAr hrρ
  exact ⟨h1.symm, h2, h3, h4⟩

/-- Inclusion below the canonical time: if the regularized clusters are monotone and some time lies in the set
`{t > 0 : Λ_t ⊆ B_{1/2}}`, then `Λ_t ⊆ B_{1/2}` for every `0 < t < sup` of that set. -/
theorem regularizedCluster_subset_half_of_lt_sSup {μ : Measure ℂ}
    (hmono : MonotoneOn (regularizedCluster μ (3 / 4) 0) (Ioi 0))
    (hne : ∃ s : ℝ, 0 < s ∧ regularizedCluster μ (3 / 4) 0 s ⊆ ball 0 (1 / 2))
    {t : ℝ} (ht : t ∈ Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)})) :
    regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2) := by
  obtain ⟨s0, hs0, hs0B⟩ := hne
  have hSne : {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)}.Nonempty := ⟨s0, hs0, hs0B⟩
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hSne ht.2
  exact (hmono (show t ∈ Ioi 0 from ht.1) (show s ∈ Ioi 0 from hs.1) hts.le).trans hs.2

/-- **Pathwise canonical inputs of the cone measure `μ` (NEW, open; q1).** The statement that `μ` satisfies, pathwise, what
`ConeCanonicalHalfBallStep` needs for the witness `Λ_t = regularizedCluster μ (3/4) 0 t`. Each conjunct is a NEW input with
its source in `notes/fp-gaps/CHATGPT-q1-open-steps.md`: the radius-3/4 data at every time (H2, H3); monotonicity (H4, from
HB Theorem 1.1 and Lemma 3.3); Hausdorff continuity on `(0,T+ε)` for some `ε > 0` (H5; the stopping argument uses continuity at `T` only); a small-time inclusion and boundedness of the stopping set
(H4, using `μ(Λ_t) = t`); the HB harmonic-ball conditions on `(0, T)` (H6). -/
def ConePathwiseHalfBallInputs (μ : Measure ℂ) : Prop :=
  IsLocallyFiniteMeasure μ ∧
  (∀ t : ℝ, 0 < t → RadiusThreeQuartersData μ t) ∧
  MonotoneOn (regularizedCluster μ (3 / 4) 0) (Ioi 0) ∧
  (∃ ε : ℝ, 0 < ε ∧ HausdorffContinuousOn (regularizedCluster μ (3 / 4) 0)
    (Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} + ε))) ∧
  (∃ s : ℝ, 0 < s ∧ regularizedCluster μ (3 / 4) 0 s ⊆ ball (0 : ℂ) (1 / 2)) ∧
  BddAbove {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} ∧
  (∀ t ∈ Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}),
      IsHarmonicBall μ (regularizedCluster μ (3 / 4) 0 t) 0) ∧
  SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ (3 / 4) 0) 0
    (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)})

/-- **Canonical stopped family from the pathwise inputs (deterministic, q1).** Under `ConePathwiseHalfBallInputs μ` and the
frozen potential-theory inputs, the canonical time `T = sup {t > 0 : Λ_t ⊆ B_{1/2}}` is positive, `Λ` is a family of harmonic
balls on `(0,T)` with the properties of Theorem 2.3 and the obstacle characterization, and it is stopped at `∂B_{1/2}` at `T`. -/
theorem canonical_stopped_family_of_pathwise {μ : Measure ℂ}
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (h : ConePathwiseHalfBallInputs μ) :
    0 < sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} ∧
      IsConeHarmonicBallFamilyOn μ (regularizedCluster μ (3 / 4) 0)
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}) ∧
      IsStoppedAtHalfBall (regularizedCluster μ (3 / 4) 0)
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}) := by
  obtain ⟨hloc, hdat, hmono, hH, hne, hbdd, hHB, hSat⟩ := h
  have := hloc
  have hsub := fun t ht => regularizedCluster_subset_half_of_lt_sSup hmono hne (t := t) ht
  have hfam : IsConeHarmonicBallFamilyOn μ (regularizedCluster μ (3 / 4) 0)
      (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}) := by
    unfold IsConeHarmonicBallFamilyOn
    refine ⟨hHB, hSat, ?_⟩
    exact satisfiesObstacleCharacterizationOn_of_data hmin hC hGB hpole (fun t ht => hdat t ht.1) hsub
  have hb : ∀ t, Bornology.IsBounded (regularizedCluster μ (3 / 4) 0 t) := fun t =>
    Metric.isBounded_ball.subset (regularizedCluster_subset_ball_three_quarters μ t)
  obtain ⟨ε, hε, hHε⟩ := hH
  have hcontU : ∃ U : ℝ, sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} < U ∧
      ContinuousOn (fun t => closureRadius (regularizedCluster μ (3 / 4) 0 t)) (Ioo 0 U) :=
    ⟨_, lt_add_of_pos_right _ hε, continuousOn_closureRadius_of_hausdorffContinuousOn hHε hb⟩
  exact canonical_witness_of_pathwise (fun t ht => (hdat t ht).1) hmono hcontU hne hbdd hfam

/-- **Almost-sure canonical family (deterministic reduction, q1).** If almost surely the pathwise inputs hold for the cone
measures `μ ω`, then almost surely there is a stopped family of harmonic balls at the canonical time (the shape of
`ConeCanonicalHalfBallStep`). -/
theorem ae_canonical_family_of_pathwise {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (h : ∀ᵐ ω ∂P, ConePathwiseHalfBallInputs (μ ω)) :
    ∀ᵐ ω ∂P, ∃ Λ : ℝ → Set ℂ,
      0 < sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)} ∧
      IsConeHarmonicBallFamilyOn (μ ω) Λ
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}) ∧
      IsStoppedAtHalfBall Λ
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster (μ ω) (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}) := by
  filter_upwards [h] with ω hω
  exact ⟨_, canonical_stopped_family_of_pathwise hmin hC hGB hpole hω⟩

end MatedCRT
