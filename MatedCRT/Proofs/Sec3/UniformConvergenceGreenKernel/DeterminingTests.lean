import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.CountableSubsequence
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.LimitIdentification
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Pairing

/-! # Countable localizing tests for Green-kernel limits -/

namespace MatedCRT.GreenEnvironment

open Set Metric Topology MeasureTheory Filter
open scoped ContDiff

/-- A fixed countable collection of smooth nonnegative compactly supported
functions contains a nonzero function supported in every nonempty open set. -/
theorem exists_countable_localizing_tests :
    ∃ f : ℕ → ℂ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      (∀ i x, 0 ≤ f i x) ∧
      ∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ i, tsupport (f i) ⊆ U ∧ ∃ x, 0 < f i x := by
  let c : ℕ → ℂ := TopologicalSpace.denseSeq ℂ
  let R : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hR : ∀ n, 0 < R n := fun n => by positivity
  let b : ℕ → ℕ → ℂ → ℝ := fun i n =>
    (⟨R n / 2, R n, half_pos (hR n), half_lt_self (hR n)⟩ : ContDiffBump (c i))
  let f : ℕ → ℂ → ℝ := fun k => b (Nat.unpair k).1 (Nat.unpair k).2
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (show ContDiffBump (c (Nat.unpair i).1) from
      ⟨R (Nat.unpair i).2 / 2, R (Nat.unpair i).2,
        half_pos (hR _), half_lt_self (hR _)⟩).contDiff
  · intro i
    exact (show ContDiffBump (c (Nat.unpair i).1) from
      ⟨R (Nat.unpair i).2 / 2, R (Nat.unpair i).2,
        half_pos (hR _), half_lt_self (hR _)⟩).hasCompactSupport
  · intro i x
    exact (show ContDiffBump (c (Nat.unpair i).1) from
      ⟨R (Nat.unpair i).2 / 2, R (Nat.unpair i).2,
        half_pos (hR _), half_lt_self (hR _)⟩).nonneg
  · intro U hU hUne
    obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq (α := ℂ)).exists_mem_open hU hUne
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hi)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hδ)
    refine ⟨Nat.pair i n, ?_, c i, ?_⟩
    · have hsupport : tsupport (f (Nat.pair i n)) = closedBall (c i) (R n) := by
        dsimp [f]
        rw [Nat.unpair_pair]
        exact (show ContDiffBump (c i) from ⟨R n / 2, R n, half_pos (hR n),
            half_lt_self (hR n)⟩).tsupport_eq
      rw [hsupport]
      apply Set.Subset.trans _ hδU
      intro x hx
      have hx' : dist x (c i) ≤ R n := hx
      change dist x (c i) < δ
      dsimp [R] at hx'
      linarith
    · have hone : f (Nat.pair i n) (c i) = 1 := by
        dsimp [f]
        rw [Nat.unpair_pair]
        exact (show ContDiffBump (c i) from ⟨R n / 2, R n, half_pos (hR n),
            half_lt_self (hR n)⟩).one_of_mem_closedBall (mem_closedBall_self (half_pos (hR n)).le)
      rw [hone]
      norm_num

/-- A continuous function is nonpositive on an open set if its integrals
against every localizing nonnegative test vanish. -/
theorem nonposOn_of_localizing_tests {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ}
    (hu : ContinuousOn u U) (f : ℕ → ℂ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hfn : ∀ i x, 0 ≤ f i x)
    (hlocal : ∀ V : Set ℂ, IsOpen V → V.Nonempty →
      ∃ i, tsupport (f i) ⊆ V ∧ ∃ x, 0 < f i x)
    (hzero : ∀ i, tsupport (f i) ⊆ U → ∫ x, f i x * u x ∂μ = 0) :
    ∀ x ∈ U, u x ≤ 0 := by
  intro x hx
  by_contra hxu
  have hxpos : 0 < u x := lt_of_not_ge hxu
  let V := U ∩ {x | 0 < u x}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have huy : ContinuousAt u y := hu.continuousAt (hU.mem_nhds hy.1)
    exact inter_mem (hU.mem_nhds hy.1) (huy (Ioi_mem_nhds hy.2))
  obtain ⟨i, hiV, w, hw⟩ := hlocal V hV ⟨x, hx, hxpos⟩
  have hiU : tsupport (f i) ⊆ U := hiV.trans inter_subset_left
  let g : ℂ → ℝ := f i * u
  have hgV : tsupport g ⊆ V := (tsupport_mul_subset_left (f := f i) (g := u)).trans hiV
  have hgcontV : ContinuousOn g V := (hf i).continuousOn.mul (hu.mono inter_subset_left)
  have hgcont : Continuous g := hgcontV.continuous_of_tsupport_subset hV hgV
  have hgcompact : HasCompactSupport g := (hfc i).mul_right
  have hgnonneg : 0 ≤ g := by
    intro y
    by_cases hy : y ∈ V
    · exact mul_nonneg (hfn i y) (le_of_lt hy.2)
    · have hnot : y ∉ tsupport (f i) := fun hm => hy (hiV hm)
      have hz : f i y = 0 := Function.notMem_support.mp (fun hm => hnot (subset_tsupport _ hm))
      simp [g, hz]
  have hwV : w ∈ V := hiV (subset_tsupport _ (show w ∈ Function.support (f i) from ne_of_gt hw))
  have hwg : g w ≠ 0 := ne_of_gt (mul_pos hw hwV.2)
  have hpos : 0 < ∫ y, g y ∂μ :=
    hgcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hgcompact hgnonneg hwg
  have hzero' : ∫ y, g y ∂μ = 0 := hzero i hiU
  linarith

/-- The countable localizing tests determine continuous functions pointwise on
an open set for every locally finite measure of full support. -/
theorem eqOn_of_localizing_tests {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {U : Set ℂ} (hU : IsOpen U) {u v : ℂ → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U) (f : ℕ → ℂ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hfn : ∀ i x, 0 ≤ f i x)
    (hlocal : ∀ V : Set ℂ, IsOpen V → V.Nonempty →
      ∃ i, tsupport (f i) ⊆ V ∧ ∃ x, 0 < f i x)
    (hzero : ∀ i, tsupport (f i) ⊆ U → ∫ x, f i x * (u x - v x) ∂μ = 0) :
    EqOn u v U := by
  have hle := nonposOn_of_localizing_tests hU (hu.sub hv) f hf hfc hfn hlocal hzero
  have hzero' : ∀ i, tsupport (f i) ⊆ U → ∫ x, f i x * (v x - u x) ∂μ = 0 := by
    intro i hi
    have hneg := integral_neg (f := fun x => f i x * (u x - v x)) (μ := μ)
    have heq : (fun x => f i x * (v x - u x)) =
        (fun x => -(f i x * (u x - v x))) := by
      funext x
      ring
    rw [heq, hneg, hzero i hi, neg_zero]
  have hge := nonposOn_of_localizing_tests hU (hv.sub hu) f hf hfc hfn hlocal hzero'
  intro x hx
  have h1 := hle x hx
  have h2 := hge x hx
  dsimp only [Pi.sub_apply] at h1 h2
  linarith

end MatedCRT.GreenEnvironment
