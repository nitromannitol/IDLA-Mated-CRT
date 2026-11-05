import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleLocalization

/-! Extension of sampled constraints to frontier neighborhoods.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology TopologicalSpace Set Metric _root_.HarmonicBalls

/-- A closed constraint on a dense sample of an open set holds on the whole
open set. -/
theorem dense_open_subset_closed {C U D : Set ℂ} (hC : Dense C)
    (hU : IsOpen U) (hD : IsClosed D) (h : U ∩ C ⊆ D) : U ⊆ D :=
  (hC.open_subset_closure_inter hU).trans (closure_minimal h hD)

/-- A sampled localization controls the whole smaller closed frontier
neighborhood whenever the sample is dense. -/
theorem initialSampleLocalization_subset_frontierLocalization
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Λ : Ω → ℝ → Set ℂ) (C : Set ℂ) (hC : Dense C)
    {ρ t q : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (n : ℕ) {ω : Ω}
    (hfam : IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hω : ω ∈ initialSampleLocalization S Λ C ρ t q n) :
    ω ∈ initialFrontierLocalization S Λ ρ t q n := by
  obtain ⟨hT, hsamples⟩ := hω
  let r := initialAnnulusRadius ρ n
  let U : Set ℂ := thickening (2 * r) (frontier (Λ ω t))
  have hr : 0 < r := (initialAnnulus_properties hρ n).1
  have hU : IsOpen U := isOpen_thickening
  have hannulus : U ⊆ closedBall 0 (ρ - r) ∩ (ball 0 r)ᶜ := by
    apply dense_open_subset_closed hC hU (isClosed_closedBall.inter isOpen_ball.isClosed_compl)
    intro x hx
    obtain ⟨hout, hin, _⟩ := hsamples x hx.2 hx.1
    refine ⟨hout, ?_⟩
    simpa [mem_ball, dist_comm, not_lt] using hin
  have hpuncture : U ⊆ ball (0 : ℂ) ρ \ {0} := by
    intro x hx
    obtain ⟨hout, hin⟩ := hannulus hx
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall] at hout
      rw [mem_ball]
      linarith
    · intro hzero
      apply hin
      simpa [Set.mem_singleton_iff.mp hzero] using (mem_ball_self hr : (0 : ℂ) ∈ ball 0 r)
  have hgapcont := (coneFamily_gap_continuous_and_zero_on_frontier
    (c := S.c₀ / 6) hfam hρ ht hT).1
  have hgap : ∀ x ∈ U, S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
      (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q := by
    intro x hx
    have hxcl : x ∈ closure (U ∩ C) := hC.open_subset_closure_inter hU hx
    have hc := (hgapcont x (hpuncture hx)).mono
      (show U ∩ C ⊆ ball (0 : ℂ) ρ \ {0} from inter_subset_left.trans hpuncture)
    have hs : ∀ y ∈ U ∩ C, S.c₀ / 6 *
        (leastSupersolution (S.μ ω) ρ 0 t y -
          (-t * greenFunction (ball 0 ρ) 0 y)) ≤ q := by
      intro y hy
      have hh := (hsamples y hy.2 hy.1).2.2
      convert hh using 1; ring
    have hh := ContinuousWithinAt.closure_le hxcl hc continuousWithinAt_const hs
    convert hh using 1; ring
  have hsub : cthickening r (frontier (Λ ω t)) ⊆ U :=
    cthickening_subset_thickening' (by positivity) (by linarith) _
  refine ⟨hT, ?_, fun x hx => hgap x (hsub hx)⟩
  intro x hx
  exact ⟨(hpuncture (hsub hx)).1, (hannulus (hsub hx)).2⟩

end MatedCRT.Sec7
