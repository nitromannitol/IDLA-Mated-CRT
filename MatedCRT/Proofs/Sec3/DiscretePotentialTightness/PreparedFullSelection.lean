import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PathwiseBoundaryCompactness
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CommonEventUniformAny
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedCommonLocal

/-! # Prepared measurable selection with conditional boundary convergence -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Pathwise prepared compactness yields the full measurable prepared
    conclusion on a single event, including the conditional closure limit. -/
theorem discretePotentialTightnessPrepared_of_pathwise (𝒮 : SpaceFillingSLEModel)
    (hp : PreparedTightnessPathwiseStep 𝒮) : DiscretePotentialTightnessPreparedStmt 𝒮 := by
  classical
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he he0
  obtain ⟨φ, hφ, A, hA, hpath⟩ := preparedTightness_boundary_relative_compactness 𝒮 hp
    hγ hγ2 hρ hρ1 S hS e he he0
  obtain ⟨B, hB, hlocalSelect⟩ := hS.exists_commonEvent_uniform_rescale_randomMesh
  obtain ⟨B', hB', hclosedSelect⟩ := hS.exists_commonEvent_uniform_rescale_any
  refine ⟨φ, hφ, A ∩ B ∩ B', (hA.and hB).and hB', ?_⟩
  intro D hD E u C hEm hEr hE0 hum hCm
  choose K x hK hx hd hcover hdom using fun j =>
    exists_compact_cover_dense_samples (D j) (hD j).2.1 (hD j).2.2.nonempty
  let P : Ω → ℕ → ℕ → Prop := fun ω _ _ => ω ∈ A ∧ PreparedTightnessBounds S D E u C ω
  have hc : ∀ ω ∈ B, ∀ j q, P ω j q → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q) := by
    intro ω _ j q hP ψ hψ
    obtain ⟨θ, hθ, hlim⟩ := hpath D hD E u C hEm hEr hE0 hum hCm ω hP.1 hP.2 ψ hψ
    obtain ⟨v, hv, hloc, _⟩ := hlim j
    exact ⟨θ, hθ, v, hv.mono (hK j q).2, hloc (K j q) (hK j q).1 (hK j q).2⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := hlocalSelect (e ∘ φ) (fun n => he (φ n)) E hEm hEr u hum
    P K x hx hd hc
  let E' : Ω → ℕ → ℝ := fun ω n => E ω (Φ ω n)
  let u' : ℕ → Ω → ℕ → ℤ → ℝ := fun j ω n a => u j ω (Φ ω n) a
  have hE'm : ∀ n, Measurable[S.envSigma] fun ω => E' ω n := by
    intro n
    exact @Tightness.measurable_comp_nat Ω S.envSigma ℝ _ E hEm
      (fun ω => Φ ω n) (hΦm n)
  have hu'm : ∀ j n a, Measurable[S.envSigma] fun ω => u' j ω n a := by
    intro j n a
    exact @Tightness.measurable_comp_nat Ω S.envSigma ℝ _ (fun ω k => u j ω k a)
      (fun k => hum j k a) (fun ω => Φ ω n) (hΦm n)
  have hKcl : ∀ j, IsCompact (closure (D j)) := by
    intro j
    exact ((isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) ρ)).subset (hD j).1).isCompact_closure
  let Q : Ω → ℕ → Prop := fun ω j => ω ∈ A ∧ ω ∈ B ∧
    PreparedTightnessBounds S D E u C ω ∧ PreparedHolderBoundary S (D j) E (u j) ω
  have hc' : ∀ ω ∈ B', ∀ j, Q ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
        TendstoUniformlyOn (fun n => rescale (S.mε (E' ω (ψ (θ n))))
          (E' ω (ψ (θ n))) (S.η ω) (u' j ω (ψ (θ n)))) w atTop (closure (D j)) := by
    intro ω _ j hQ ψ hψ
    have hmono := (hΦ ω hQ.2.1).1
    obtain ⟨θ, hθ, hlim⟩ := hpath D hD E u C hEm hEr hE0 hum hCm ω hQ.1 hQ.2.2.1
      (Φ ω ∘ ψ) (hmono.comp hψ)
    obtain ⟨v, _, _, hboundary⟩ := hlim j
    exact ⟨θ, hθ, v, hboundary hQ.2.2.2⟩
  obtain ⟨Ψ, hΨm, hΨ⟩ := hclosedSelect (e ∘ φ) (fun n => he (φ n)) E' hE'm
    (fun ω n => hEr ω (Φ ω n)) u' hu'm (fun j => closure (D j)) hKcl Q hc'
  refine ⟨fun ω n => Φ ω (Ψ ω n), ?_, ?_⟩
  · intro n
    exact @Tightness.measurable_comp_nat Ω S.envSigma ℕ _ Φ hΦm
      (fun ω => Ψ ω n) (hΨm n)
  · intro ω hω hb
    have hΦω := hΦ ω hω.1.2
    have hΨω := hΨ ω hω.2
    refine ⟨hΦω.1.comp hΨω.1, ?_⟩
    intro j
    have hlocal : ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
        ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (Φ ω (Ψ ω n)))) (E ω (Φ ω (Ψ ω n)))
            (S.η ω) (u j ω (Φ ω (Ψ ω n)))) v atTop O := by
      obtain ⟨v, hv, hconv⟩ := local_limit_of_uniform_compact_cover _ (D j) (K j)
        (hcover j) (hdom j) (fun q => hΦω.2 j q ⟨hω.1.1, hb⟩)
      refine ⟨v, hv, fun O hO hOD V hV => ?_⟩
      exact hΨω.1.tendsto_atTop.eventually (hconv O hO hOD V hV)
    by_cases hh : PreparedHolderBoundary S (D j) E (u j) ω
    · obtain ⟨w, hw⟩ := hΨω.2 j ⟨hω.1.1, hω.1.2, hb, hh⟩
      obtain ⟨v, hv, hl⟩ := hlocal
      have hclosed : TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (Φ ω (Ψ ω n)))) (E ω (Φ ω (Ψ ω n)))
            (S.η ω) (u j ω (Φ ω (Ψ ω n)))) w atTop (closure (D j)) := hw
      obtain ⟨hwc, hwl⟩ := local_limit_of_uniform_superset _ (D j) (closure (D j))
        subset_closure v w hv hl hclosed
      exact ⟨w, hwc, fun O hO hOD => hwl O hO (by simpa [hO.isClosed.closure_eq] using hOD),
        fun _ => hclosed⟩
    · obtain ⟨v, hv, hl⟩ := hlocal
      exact ⟨v, hv, fun O hO hOD => hl O hO (subset_trans subset_closure hOD), False.elim ∘ hh⟩

end MatedCRT
