import MatedCRT.FirstPass.Derived.LocalMeshAllDisks

/-! # Edge bounds on bounded domains along a common mesh subsequence -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace MatedCRT

/-- On one deterministic mesh subsequence, every bounded set has a pathwise
vanishing majorant for all edges starting in the set, eventually in the mesh. -/
theorem exists_subseq_bounded_domain_edge_majorant
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ K : Set ℂ, Bornology.IsBounded K →
        ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
          ∀ᶠ n in atTop, ∀ j k : ℤ,
            S.mult (ε (φ n)) ω j k ≠ 0 →
            vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ K →
            dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
              (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ≤ δ n := by
  classical
  obtain ⟨φ, hφ, hφae⟩ := exists_subseq_all_local_edges_tendsto_zero hγ hγ2 hS hae hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  intro K hK
  obtain ⟨R, hR⟩ := hK.subset_ball (0 : ℂ)
  let E : ℕ → Set ℝ := fun n => insert 0 {d | ∃ j k : ℤ,
    S.mult (ε (φ n)) ω j k ≠ 0 ∧
    vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ K ∧
    d = dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
      (vertexPoint (ε (φ n)) (⇑(η' ω)) k)}
  let δ : ℕ → ℝ := fun n => if BddAbove (E n) then sSup (E n) else 0
  have hne (n : ℕ) : (E n).Nonempty := ⟨0, by simp [E]⟩
  have hupper (a : ℝ) (ha : 0 < a) : ∀ᶠ n in atTop,
      ∀ d ∈ E n, d ≤ a := by
    filter_upwards [hω R a ha] with n hn d hd
    rcases Set.mem_insert_iff.mp hd with rfl | ⟨j, k, hjk, hj, rfl⟩
    · exact ha.le
    · exact (hn j k hjk (hR hj)).le
  have hbounded : ∀ᶠ n in atTop, BddAbove (E n) := by
    filter_upwards [hupper 1 (by norm_num)] with n hn
    exact ⟨1, hn⟩
  have hnonneg : ∀ n, 0 ≤ δ n := by
    intro n
    by_cases hb : BddAbove (E n)
    · simpa only [δ, ite_eq_left hb] using le_csSup hb (show (0 : ℝ) ∈ E n by simp [E])
    · simp only [δ, ite_eq_right hb, le_refl]
  refine ⟨δ, ?_, ?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha (hnonneg n))
    · intro a ha
      filter_upwards [hbounded, hupper (a / 2) (by linarith)] with n hb hn
      have hd : δ n ≤ a / 2 := by
        simpa only [δ, ite_eq_left hb] using csSup_le (hne n) hn
      linarith
  · filter_upwards [hbounded] with n hb j k hjk hj
    have hd : dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
        (vertexPoint (ε (φ n)) (⇑(η' ω)) k) ∈ E n := by
      simp only [E, mem_insert_iff, mem_ofPred_eq]
      exact Or.inr ⟨j, k, hjk, hj, rfl⟩
    simpa only [δ, ite_eq_left hb] using le_csSup hb hd

end MatedCRT
end
