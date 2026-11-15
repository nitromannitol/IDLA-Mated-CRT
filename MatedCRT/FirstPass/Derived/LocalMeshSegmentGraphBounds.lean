import MatedCRT.FirstPass.Derived.LocalMeshJointSubsequence
import MatedCRT.Proofs.Infra.DiscretePotential
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-! # Joint local mesh and segment graph edge bounds -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov
open scoped ENNReal

namespace MatedCRT

/-- On one deterministic subsequence, the local cell diameters tend to zero and
one pathwise majorant controls the edges of every segment contained in the disk. -/
theorem exists_subseq_local_mesh_and_segment_graph_bounds
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η' ω)) R)
        atTop (𝓝 0) ∧
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        ∀ a b : ℝ, (⇑(η' ω)) '' Icc a b ⊆ ball (0 : ℂ) R →
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
  classical
  obtain ⟨φ, hφ, hφae⟩ :=
    exists_subseq_local_mesh_and_edges_tendsto_zero hγ hγ2 hS hae hε hε0 R
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  refine ⟨hω.1, ?_⟩
  let E : ℕ → Set ℝ := fun n => insert 0 {d | ∃ j k : ℤ,
    S.mult (ε (φ n)) ω j k ≠ 0 ∧
    vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ ball (0 : ℂ) R ∧
    d = dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
      (vertexPoint (ε (φ n)) (⇑(η' ω)) k)}
  let δ : ℕ → ℝ := fun n => if BddAbove (E n) then sSup (E n) else 0
  have hne (n : ℕ) : (E n).Nonempty := ⟨0, by simp [E]⟩
  have hupper (a : ℝ) (ha : 0 < a) : ∀ᶠ n in atTop,
      ∀ d ∈ E n, d ≤ a := by
    filter_upwards [hω.2 a ha] with n hn d hd
    rcases Set.mem_insert_iff.mp hd with rfl | ⟨j, k, hjk, hj, rfl⟩
    · exact ha.le
    · exact (hn j k hjk hj).le
  have hbounded : ∀ᶠ n in atTop, BddAbove (E n) := by
    filter_upwards [hupper 1 (by norm_num)] with n hn
    exact ⟨1, hn⟩
  have hnonneg : ∀ n, 0 ≤ δ n := by
    intro n
    by_cases hb : BddAbove (E n)
    · simpa only [δ, ite_eq_left hb] using le_csSup hb (show (0 : ℝ) ∈ E n by simp [E])
    · simp only [δ, ite_eq_right hb, le_refl]
  have hδ : Tendsto δ atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha (hnonneg n))
    · intro a ha
      filter_upwards [hbounded, hupper (a / 2) (by linarith)] with n hb hn
      have hd : δ n ≤ a / 2 := by
        simpa only [δ, ite_eq_left hb] using csSup_le (hne n) hn
      linarith
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbounded] with n hb a b hcontain
  have hedge : ∀ j k : ℤ, (adjGraph (S.mult (ε (φ n)) ω)).Adj j k →
      ε (φ n) * j ∈ Icc a b →
      dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
        (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ≤ δ n := by
    intro j k hjk hj
    have hm := ((adjGraph_adj_iff (S.mult_symm (ε (φ n)) ω)).mp hjk).2
    have hmem : dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
        (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ∈ E n := by
      simp only [E, mem_insert_iff, mem_ofPred_eq]
      exact Or.inr ⟨j, k, hm, hcontain ⟨ε (φ n) * j, hj, rfl⟩, rfl⟩
    simpa only [δ, ite_eq_left hb] using le_csSup hb hmem
  refine ⟨hedge, ?_⟩
  intro x N hexit hstep j hj
  have hinside : ε (φ n) * (x j) ∈ Icc a b := by
    have h := (hitTime_eq_coe_iff.mp hexit).2 j hj
    simpa only [mem_compl_iff, mem_ofPred_eq, not_not] using h
  rcases hstep j with heq | hadj
  · rw [heq, dist_self]
    exact hnonneg n
  · exact hedge _ _ hadj hinside

end MatedCRT
end
