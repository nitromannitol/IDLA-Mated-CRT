import MatedCRT.FirstPass.Derived.IntegerWalkEscapeSubsequence

/-! # Shifted bounded-set exit for the embedded walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- On one almost-sure event, every shift of the embedded walk exits every
bounded set in finitely many steps. -/
theorem ae_embeddedExitTime_ne_top_all_bounded_all_shifts
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ U : Set ℂ, Bornology.IsBounded U → ∀ K : ℕ,
        embeddedExitTime ε η U (fun n => ξ (K + n)) ≠ ⊤ := by
  classical
  filter_upwards [ae_exists_escape_subsequence_vertexPoint h hε m hlf H hH hconn
    (s := 1) one_ne_zero x] with ξ hξ
  obtain ⟨f, hfmono, hf⟩ := hξ
  intro U hU K
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hU
  obtain ⟨k, hk⟩ := exists_nat_gt (max R (K : ℝ))
  have hkR : R < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hkK : K ≤ f k := by
    have : (K : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have : K ≤ k := by exact_mod_cast this.le
    exact this.trans (hfmono.id_le k)
  have hnorm : (k : ℝ) ≤ ‖vertexPoint ε η (ξ (f k))‖ := by
    simpa only [one_smul, LinearIsometryEquiv.norm_map] using hf k
  have hout : vertexPoint ε η (ξ (f k)) ∉ U := by
    intro hmem
    have := hR _ hmem
    linarith
  have hex : ∃ n, ξ (K + n) ∉ {j : ℤ | vertexPoint ε η j ∈ U} := by
    refine ⟨f k - K, ?_⟩
    simpa only [Nat.add_sub_of_le hkK, Set.mem_ofPred_eq] using hout
  unfold embeddedExitTime vExitTime
  split_ifs with h
  · exact ENat.natCast_ne_top _
  · exact (h hex).elim

end MatedCRT
end
