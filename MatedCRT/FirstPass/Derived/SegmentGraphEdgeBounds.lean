import MatedCRT.FirstPass.Derived.LocalMeshBoundedDomain
import MatedCRT.Proofs.Infra.DiscretePotential
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-! # Embedded edge bounds for segment-labelled graph walks -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov

namespace MatedCRT

/-- Along a common deterministic subsequence, each curve segment has a
pathwise vanishing bound on all graph edges starting in that segment and on
all steps before a finite exit of any legal walk from its labelled vertices. -/
theorem exists_subseq_segment_graph_edge_bounds
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ a b : ℝ,
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ j k : ℤ, (adjGraph (S.mult (ε (φ n)) ω)).Adj j k →
          ε (φ n) * j ∈ Icc a b →
          dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
            (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ≤ δ n) ∧
        (∀ (x : ℕ → ℤ) (N : ℕ),
          hitTime {j : ℤ | ε (φ n) * j ∈ Icc a b}ᶜ x = N →
          (∀ j, x (j + 1) = x j ∨
            (adjGraph (S.mult (ε (φ n)) ω)).Adj (x j) (x (j + 1))) →
          ∀ j < N, dist (vertexPoint (ε (φ n)) (⇑(η' ω)) (x j))
            (vertexPoint (ε (φ n)) (⇑(η' ω)) (x (j + 1))) ≤ δ n) := by
  obtain ⟨φ, hφ, hφae⟩ := exists_subseq_bounded_domain_edge_majorant hγ hγ2 hS hae hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  intro a b
  have hK : Bornology.IsBounded ((⇑(η' ω)) '' Icc a b) :=
    (isCompact_Icc.image (η' ω).continuous).isBounded
  obtain ⟨d, hd, hbound⟩ := hω _ hK
  refine ⟨fun n => max (d n) 0, ?_, ?_⟩
  · simpa only [max_self] using hd.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · filter_upwards [hbound] with n hn
    have hedge : ∀ j k : ℤ, (adjGraph (S.mult (ε (φ n)) ω)).Adj j k →
        ε (φ n) * j ∈ Icc a b →
        dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
          (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ≤ max (d n) 0 := by
      intro j k hjk hj
      have hm := ((adjGraph_adj_iff (S.mult_symm (ε (φ n)) ω)).mp hjk).2
      exact le_trans (hn j k hm ⟨ε (φ n) * j, hj, rfl⟩) (le_max_left _ _)
    refine ⟨hedge, ?_⟩
    intro x N hexit hstep j hj
    have hinside : ε (φ n) * (x j) ∈ Icc a b := by
      have h := (hitTime_eq_coe_iff.mp hexit).2 j hj
      simpa only [mem_compl_iff, mem_ofPred_eq, not_not] using h
    rcases hstep j with heq | hadj
    · rw [heq, dist_self]
      exact le_max_right _ _
    · exact hedge _ _ hadj hinside

end MatedCRT
end
