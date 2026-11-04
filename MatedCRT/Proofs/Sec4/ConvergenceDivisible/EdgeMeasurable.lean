import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Infra.MatingOfTrees

/-! # Measurability of the Brownian encoding of the mated-CRT map -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- The infimum over a compact interval is continuous in a continuous path. -/
theorem continuous_path_interval_inf (a b : ℝ) (q : ℝ × ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (fun p : C(ℝ, ℝ × ℝ) => sInf ((fun t => q (p t)) '' Icc a b)) := by
  apply isCompact_Icc.continuous_sInf
  exact hq.comp ContinuousEval.continuous_eval

/-- Brownian adjacency is a closed condition on the path. -/
theorem isClosed_bmAdjacent (ε : ℝ) (j k : ℤ) (q : ℝ × ℝ → ℝ)
    (hq : Continuous q) :
    IsClosed {p : C(ℝ, ℝ × ℝ) | bmAdjacent ε (fun t => q (p t)) j k} := by
  unfold bmAdjacent
  exact isClosed_le
    ((continuous_path_interval_inf _ _ q hq).max (continuous_path_interval_inf _ _ q hq))
    (continuous_path_interval_inf _ _ q hq)

/-- Each edge multiplicity of a valid environment is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_mult
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (j k : ℤ) : Measurable (fun ω => S.mult ε ω j k) := by
  classical
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  have hL : MeasurableSet {ω | bmAdjacent ε (fun t => (S.bm ω t).1) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.fst continuous_fst).measurableSet.preimage
      hc.measurable_curves.2.2.2
  have hR : MeasurableSet {ω | bmAdjacent ε (fun t => (S.bm ω t).2) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.snd continuous_snd).measurableSet.preimage
      hc.measurable_curves.2.2.2
  unfold MatedCRTEnv.mult bmEdgeCount
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    apply Measurable.ite (hL.union hR)
    · by_cases hdist : 1 < max j k - min j k
      · simp only [hdist, true_and]
        exact Measurable.ite (hL.inter hR) measurable_const measurable_const
      · simp [hdist]
    · exact measurable_const

end MatedCRT
