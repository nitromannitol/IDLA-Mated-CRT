import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialShellBudgetMargins
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps

/-! Combining localized shell estimates with good and almost-sure events. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- A conditional high-probability estimate remains valid on any smaller
conditioning event, without measurability assumptions on either event. -/
theorem tendsToOneOn_mono_condition {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) {F G : Set Ω} {E : ℝ → Set Ω}
    (hFG : G ⊆ F) (hE : TendsToOneOn P F E) : TendsToOneOn P G E := by
  unfold TendsToOneOn at hE ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
    (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun ε => measure_mono (fun ω hω => ⟨hFG hω.1, hω.2⟩)

/-- An almost-sure event can be added to a conditional high-probability
estimate, even when the events are not known to be measurable. -/
theorem tendsToOneOn_inter_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F A : Set Ω) (E : ℝ → Set Ω)
    (hA : ∀ᵐ ω ∂P, ω ∈ A) (hE : TendsToOneOn P F E) :
    TendsToOneOn P F (fun ε => E ε ∩ A) := by
  unfold TendsToOneOn at hE ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hA] with ω hω hbad
  exact ⟨hbad.1, fun hEω => hbad.2 ⟨hEω, hω⟩⟩

/-- Two unconditional good events and an almost-sure structural event can be
combined with any conditional high-probability shell estimate. -/
theorem tendsToOneOn_shell_good_events {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F G A : Set Ω) (E H J : ℝ → Set Ω)
    (hGF : G ⊆ F) (hE : TendsToOneOn P F E)
    (hH : ProbTendsToOne P H) (hJ : ProbTendsToOne P J)
    (hA : ∀ᵐ ω ∂P, ω ∈ A) :
    TendsToOneOn P G (fun ε => (E ε ∩ H ε ∩ J ε) ∩ A) := by
  have h1 : TendsToOneOn P G (fun ε => E ε ∩ H ε) :=
    MeanValueSurplus.tendsToOneOn_of_inter (tendsToOneOn_mono_condition P hGF hE) hH
      (Eventually.of_forall fun _ => Subset.rfl)
  have h2 : TendsToOneOn P G (fun ε => (E ε ∩ H ε) ∩ J ε) :=
    MeanValueSurplus.tendsToOneOn_of_inter h1 hJ (Eventually.of_forall fun _ => Subset.rfl)
  exact tendsToOneOn_inter_ae P G A _ hA h2

end MatedCRT.Sec7
