import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-! # Convergence of inverses of increasing clocks -/

namespace MatedCRT

open Filter HarmonicBalls Topology
open scoped NNReal

/-- Pointwise convergence of strictly increasing clocks implies convergence
of their inverses at every clock value of the limiting clock. The
approximating clocks need not have infinite lifetime. -/
theorem tendsto_clockInverse_clockValue_of_tendsto
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i))
    (hGzero : G 0 = 0) (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (r : ℝ≥0)
    (u : ι → ℝ≥0) (hu : Tendsto u l (𝓝 (Real.toNNReal (G r)))) :
    Tendsto (fun i => clockInverse (F i) (u i)) l (𝓝 r) := by
  have hGr : 0 ≤ G r := by
    simpa [hGzero] using hGmono.monotone (show 0 ≤ r from bot_le)
  have hvalue : (Real.toNNReal (G r) : ℝ) = G r := Real.coe_toNNReal _ hGr
  have hu' : Tendsto (fun i => (u i : ℝ)) l (𝓝 (G r)) := by
    simpa [Function.comp_def, hvalue] using NNReal.continuous_coe.continuousAt.tendsto.comp hu
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨s, has, hsr⟩ := exists_between ha
    have hGs : G s < G r := hGmono hsr
    have hupper : G r < G (r + 1) := hGmono (by simp)
    filter_upwards [(hconv s).eventually_lt hu' hGs,
      hu'.eventually_lt (hconv (r + 1)) hupper] with i hi hj
    have hs : s ≤ clockInverse (F i) (u i) := by
      unfold clockInverse
      apply le_csInf
      · exact ⟨r + 1, hj⟩
      · intro t ht
        exact (hmono i).lt_iff_lt.mp (lt_trans hi ht) |>.le
    exact has.trans_le hs
  · intro a ha
    obtain ⟨s, hrs, hsa⟩ := exists_between ha
    have hGs : G r < G s := hGmono hrs
    filter_upwards [hu'.eventually_lt (hconv s) hGs] with i hi
    have hs : clockInverse (F i) (u i) ≤ s := clockInverse_le_of_lt hi
    exact hs.trans_lt hsa

/-- Pointwise convergence of clocks implies convergence of the inverses at
a fixed value of the limiting clock. -/
theorem tendsto_clockInverse_clockValue
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hGzero : G 0 = 0) (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (r : ℝ≥0) :
    Tendsto (fun i => clockInverse (F i) (Real.toNNReal (G r))) l (𝓝 r) :=
  tendsto_clockInverse_clockValue_of_tendsto hmono hGzero hGmono hconv r _ tendsto_const_nhds

/-- If the limiting clock has infinite lifetime, inverse convergence holds
at every nonnegative clock time. -/
theorem tendsto_clockInverse_of_pointwise
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hG : IsTimeChangeClock G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (u : ℝ≥0) :
    Tendsto (fun i => clockInverse (F i) u) l (𝓝 (clockInverse G u)) := by
  obtain ⟨r, hr⟩ := IsTimeChangeClock.surjective_toNNReal hG u
  rw [← hr, clockInverse_clockValue hG.map_zero hG.strictMono]
  exact tendsto_clockInverse_clockValue hmono hG.map_zero hG.strictMono hconv r

end MatedCRT
