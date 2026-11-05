import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialAnnuli
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.FrontierMeasurable

/-! Countable sampling of frontier neighborhoods.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology TopologicalSpace Set Metric _root_.HarmonicBalls

/-- A sampled frontier neighborhood satisfies a closed annular constraint and
an upper bound for the continuum obstacle gap. -/
def initialSampleLocalization {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Λ : Ω → ℝ → Set ℂ) (C : Set ℂ) (ρ t q : ℝ) (n : ℕ) : Set Ω := {ω |
  t < clusterExitTime (Λ ω) ρ ∧ ∀ x ∈ C,
    x ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (Λ ω t)) →
      (x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
      initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
      S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q}

/-- Countably sampled neighborhood constraints are null measurable before a
null-measurable exit event. -/
theorem nullMeasurableSet_initialSampleLocalization
    {𝒮 : SpaceFillingSLEModel} {γ ρ t q : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (C : Set ℂ) (hC : C.Countable) (n : ℕ) :
    NullMeasurableSet (initialSampleLocalization S Λ C ρ t q n) S.P := by
  classical
  let : Countable C := hC.to_subtype
  have hr : 0 ≤ initialAnnulusRadius ρ n := (initialAnnulus_properties hρ n).1.le
  have hpoint : ∀ x : C, NullMeasurableSet {ω |
      (x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
      initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
      S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q} S.P := by
    intro x
    by_cases hx : (x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
        initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0
    · have hxρ : (x : ℂ) ∈ closedBall 0 ρ :=
        closedBall_subset_closedBall (by linarith) hx.1
      have hmeas := hS.aemeasurable_leastSupersolution_inside_unit hγ hγ' h27
        hρ hρ' ht (mem_ball_self hρ) hxρ
      have hgap : AEMeasurable (fun ω =>
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) S.P :=
        (aemeasurable_const.mul hmeas).sub aemeasurable_const
      simpa only [hx.1, hx.2, true_and] using (nullMeasurableSet_le hgap (aemeasurable_const : AEMeasurable (fun _ : Ω => q) S.P))
    · have hempty : {ω | (x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
          initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, _⟩
        exact hx ⟨h1, h2⟩
      rw [hempty]
      exact nullMeasurableSet_empty
  have hsample : ∀ x : C, NullMeasurableSet {ω |
      ¬ (t < clusterExitTime (Λ ω) ρ ∧
        (x : ℂ) ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (Λ ω t))) ∨
      ((x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
        initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q)} S.P := by
    intro x
    exact (nullMeasurableSet_beforeExit_mem_frontier_thickening hγ hγ' hS h27
      hρ hρ' ht Λ hΛ hexit x _).compl.union (hpoint x)
  have hm := hexit.inter (NullMeasurableSet.iInter hsample)
  convert hm using 1
  ext ω
  simp only [initialSampleLocalization, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hT, h⟩
    exact ⟨hT, fun x => by
      by_cases hx : (x : ℂ) ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (Λ ω t))
      · exact Or.inr (h x x.2 hx)
      · exact Or.inl (by simp [hx])⟩
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_⟩
    intro x hx hthick
    rcases h ⟨x, hx⟩ with hbad | hgood
    · exact False.elim (hbad ⟨hT, hthick⟩)
    · exact hgood

end MatedCRT.Sec7
