import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleLocalization
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable

/-! Measurable sampled frontier neighborhoods for bounded obstacle clusters.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology TopologicalSpace Set Metric _root_.HarmonicBalls

/-- Sampled frontier constraints for the bounded obstacle cluster. -/
def localSampleLocalization {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (C : Set ℂ) (ρ t q : ℝ) (n : ℕ) : Set Ω := {ω | ∀ x ∈ C,
    x ∈ thickening (2 * initialAnnulusRadius ρ n)
      (frontier (interior (closure (cluster (S.μ ω) ρ 0 t)))) →
      (x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
      initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
      S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q}

/-- Sampled frontier constraints of a bounded obstacle cluster are null measurable. -/
theorem nullMeasurableSet_localSampleLocalization
    {𝒮 : SpaceFillingSLEModel} {γ ρ t q : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (C : Set ℂ) (hC : C.Countable) (n : ℕ) :
    NullMeasurableSet (localSampleLocalization S C ρ t q n) S.P := by
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
  let A : Ω → Set ℂ := fun ω => interior (closure (cluster (S.μ ω) ρ 0 t))
  have hmem : ∀ z, NullMeasurableSet {ω | z ∈ A ω} S.P :=
    fun z => hS.nullMeasurableSet_mem_regularizedLocalCluster hγ hγ' h27 hρ hρ' ht z
  have hopen : ∀ᵐ ω ∂S.P, IsOpen (A ω) := Eventually.of_forall fun _ => isOpen_interior
  have hreg : ∀ᵐ ω ∂S.P, interior (closure (A ω)) = A ω := by
    apply Eventually.of_forall
    intro ω
    apply subset_antisymm
    · exact interior_mono (closure_minimal interior_subset isClosed_closure)
    · exact isOpen_interior.subset_interior_closure
  have hfront : ∀ x : C, NullMeasurableSet {ω |
      (x : ℂ) ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (A ω))} S.P := by
    intro x
    have hm := nullMeasurableSet_frontier_inter_ball_nonempty S.P A hmem hopen hreg x
      (2 * initialAnnulusRadius ρ n)
    convert hm using 1
    ext ω
    simp [mem_thickening_iff, Set.Nonempty, dist_comm]
  have hm : ∀ x : C, NullMeasurableSet {ω |
      ¬ ((x : ℂ) ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (A ω))) ∨
      ((x : ℂ) ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) ∧
        initialAnnulusRadius ρ n ≤ dist (x : ℂ) 0 ∧
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q)} S.P :=
    fun x => (hfront x).compl.union (hpoint x)
  convert NullMeasurableSet.iInter hm using 1
  ext ω
  simp only [localSampleLocalization, mem_ofPred_eq, mem_iInter]
  constructor
  · intro h x
    by_cases hx : (x : ℂ) ∈ thickening (2 * initialAnnulusRadius ρ n) (frontier (A ω))
    · exact Or.inr (h x x.2 hx)
    · exact Or.inl hx
  · intro h x hx hthick
    exact (h ⟨x, hx⟩).resolve_left (not_not_intro hthick)

end MatedCRT.Sec7
