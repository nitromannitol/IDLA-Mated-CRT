import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauAE
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.WholePlaneLocality
import HarmonicBalls.Proofs.Sec5.RegularizedFamilyHarmonicBridge

/-! # A.e. measurability of the radii of the whole-plane global family (open item (f), closure of Proposition 4.2)

The radius of a family set is `familyRadius U = sSup {‖x‖ : x ∈ U}` (draft line 232). For an open bounded set `U`, this
supremum is the supremum over a dense sequence `(d_n)` of the norms of the points `d_n ∈ U`
(`familyRadius_eq_iSup_denseSeq`). Each term `ω ↦ 1[d_n ∈ Λ_ω(q)] ‖d_n‖` is almost everywhere measurable by the locality
of the whole-plane harmonic balls (`nullMeasurableSet_mem_wholePlaneHarmonicBall`, HB22 Thm 1.1 locality), hence so is the
countable supremum (`AEMeasurable.iSup`). A regularized cluster family is a family of harmonic balls
(`regularizedClusterFamily_isHarmonicBallFamily`, HB Section 5 bridge), so the locality applies to the global family
`Λ̂_t(0)` of Theorem 5.5 (`ExistenceHarmonicBallsStmt`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- For an open bounded set `U ⊆ ℂ`, the radius `sup {‖x‖ : x ∈ U}` is the supremum over a dense sequence of the norms of
the points of the sequence that lie in `U`. -/
theorem familyRadius_eq_iSup_denseSeq {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    familyRadius U = ⨆ n : ℕ, U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n) := by
  unfold familyRadius
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hFnn : ∀ n : ℕ, 0 ≤ U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n) :=
    fun n => Set.indicator_nonneg (fun x _ => norm_nonneg x) _
  have hbdd : BddAbove (Set.range fun n : ℕ => U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n)) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    show U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n) ≤ max M 0
    by_cases h : denseSeq ℂ n ∈ U
    · rw [Set.indicator_of_mem h]
      exact (hM _ h).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h]
      exact le_max_right _ _
  have hSbdd : BddAbove ((fun x : ℂ => ‖x‖) '' U) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hM x hx
  apply le_antisymm
  · rcases Set.eq_empty_or_nonempty U with hUe | hUne
    · have hS : (fun x : ℂ => ‖x‖) '' U = ∅ := by
        rw [hUe, Set.image_empty]
      rw [hS, Real.sSup_empty]
      exact (hFnn 0).trans (le_ciSup hbdd 0)
    · apply csSup_le (hUne.image _)
      rintro _ ⟨x, hx, rfl⟩
      show ‖x‖ ≤ _
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
      obtain ⟨n, hn⟩ := (denseRange_denseSeq (α := ℂ)).exists_mem_open (isOpen_ball (x := x) (ε := min δ ε))
        ⟨x, mem_ball_self (lt_min hδ hε)⟩
      have hdU : denseSeq ℂ n ∈ U := hball (Metric.ball_subset_ball (min_le_left δ ε) hn)
      have hdist : dist (denseSeq ℂ n) x < ε :=
        lt_of_lt_of_le (mem_ball.mp hn) (min_le_right δ ε)
      have h1 : ‖x‖ - ‖denseSeq ℂ n‖ ≤ ‖x - denseSeq ℂ n‖ := norm_sub_norm_le x _
      have h2 : ‖x - denseSeq ℂ n‖ = dist (denseSeq ℂ n) x := by
        rw [dist_eq_norm, norm_sub_rev]
      have h3 : U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n) = ‖denseSeq ℂ n‖ :=
        Set.indicator_of_mem hdU _
      have h4 : U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n) ≤
          ⨆ m : ℕ, U.indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ m) := le_ciSup hbdd n
      linarith
  · refine ciSup_le fun n => ?_
    by_cases h : denseSeq ℂ n ∈ U
    · rw [Set.indicator_of_mem h]
      exact le_csSup hSbdd (Set.mem_image_of_mem (fun x : ℂ => ‖x‖) h)
    · rw [Set.indicator_of_notMem h]
      exact Real.sSup_nonneg (fun y hy => by
        obtain ⟨x, -, rfl⟩ := hy
        exact norm_nonneg x)

/-- **A.e. measurability of the radii of the whole-plane global family.** Let `Λ` be a family with almost surely the
regularized-cluster property at the origin (`ExistenceHarmonicBallsStmt`, HB Theorem 5.5). Then for every `q > 0` the
radius `ω ↦ R_q(ω) = familyRadius (Λ ω q)` is almost everywhere measurable, given the locality input `hloc`. -/
theorem aemeasurable_familyRadius_of_regularized (hloc : HarmonicBallLocalSetStmt.{0}) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α < lqgQ γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0)
    {q : ℝ} (hq : 0 < q) :
    AEMeasurable (fun ω => familyRadius (Λ ω q)) P := by
  have hHB : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0 :=
    hΛ.mono fun ω h => regularizedClusterFamily_isHarmonicBallFamily (μ ω) (Λ ω) 0 h
  have hgood : ∀ᵐ ω ∂P, IsOpen (Λ ω q) ∧ Bornology.IsBounded (Λ ω q) :=
    hΛ.mono fun ω h => by
      obtain ⟨hs, -, -⟩ := h
      exact ⟨(hs.isRegularOpen q hq).isOpen, hs.isBounded q hq⟩
  have hmeas : ∀ n : ℕ,
      AEMeasurable (fun ω => (Λ ω q).indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n)) P := by
    intro n
    have hset := nullMeasurableSet_mem_wholePlaneHarmonicBall hloc hγ hγ2 hα hh hμ 0 Λ hHB hq (denseSeq ℂ n)
    have heq : (fun ω => (Λ ω q).indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n)) =
        {ω : Ω | denseSeq ℂ n ∈ Λ ω q}.indicator (fun _ : Ω => ‖denseSeq ℂ n‖) := by
      funext ω
      by_cases h : denseSeq ℂ n ∈ Λ ω q
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show ω ∈ {ω' : Ω | denseSeq ℂ n ∈ Λ ω' q} from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show ω ∉ {ω' : Ω | denseSeq ℂ n ∈ Λ ω' q} from h)]
    rw [heq]
    exact aemeasurable_const.indicator₀ hset
  have hsup : AEMeasurable (fun ω => ⨆ n : ℕ, (Λ ω q).indicator (fun x : ℂ => ‖x‖) (denseSeq ℂ n)) P :=
    AEMeasurable.iSup hmeas
  refine hsup.congr ?_
  filter_upwards [hgood] with ω hω
  exact (familyRadius_eq_iSup_denseSeq hω.1 hω.2).symm

end MatedCRT
