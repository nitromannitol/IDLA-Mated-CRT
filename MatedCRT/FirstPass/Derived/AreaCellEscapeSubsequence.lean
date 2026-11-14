import MatedCRT.FirstPass.Derived.AreaCellLateExteriorVisit

/-! # Escaping subsequences for area-parametrized curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- Almost every relabelled walk has a strictly increasing sequence of times
at which the scaled cell representative has norm at least the sequence index. -/
theorem ae_exists_escape_subsequence_areaCellRepresentative
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {s : ℝ} (hs : s ≠ 0) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n))) :
    ∀ᵐ ξ ∂Q, ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ k : ℕ,
      (k : ℝ) ≤ ‖s • areaCellRepresentative h hε m (ξ (f k))‖ := by
  classical
  filter_upwards [ae_visit_all_exteriors_late_areaCellRepresentative h hε m hlf H hH hconn hs x Q hQ]
    with ξ hξ
  have hex : ∀ k N : ℕ, ∃ n : ℕ, N < n ∧
      (k : ℝ) ≤ ‖s • areaCellRepresentative h hε m (ξ n)‖ := by
    intro k N
    obtain ⟨n, hn, hout⟩ := hξ (ball (0 : ReflectedGMS.Plane) (k : ℝ))
      (isBounded_ball) (N + 1)
    refine ⟨n, Nat.lt_of_succ_le hn, ?_⟩
    simpa only [mem_ball, dist_zero_right, not_lt] using hout
  choose g hg using hex
  let f : ℕ → ℕ := fun k => Nat.rec (g 0 0) (fun j n => g (j + 1) n) k
  refine ⟨f, strictMono_nat_of_lt_succ ?_, ?_⟩
  · intro k
    exact (hg (k + 1) (f k)).1
  · intro k
    cases k with
    | zero => exact (hg 0 0).2
    | succ k => exact (hg (k + 1) (f k)).2

end MatedCRT
end
