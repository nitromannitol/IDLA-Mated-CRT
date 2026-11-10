import MatedCRT.FirstPass.S3t.Integrate
import MatedCRT.FirstPass.S3t.EpsShell
import MatedCRT.FirstPass.S3t.BoundaryShells
import MatedCRT.FirstPass.S3t.RiemannSum
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.S3t.VanishingMesh
import MatedCRT.FirstPass.S3t.Normalization
import MatedCRT.FirstPass.S5c.CellFirstHit
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Truncated quenched laws: the staged assembly (fp-S3t, z8; answer section 4)

Source: `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md`, Steps 5–12 and section 4 (the replacement theorem).

`truncatedQuenchedLawsFixedTime_of_steps` assembles Steps 11 and 12 with the outputs of Steps 5–8 and 10, taken as
hypotheses with the answer's Lean types. Concrete now: the disk `D = B_r(z)`, the exhaustion `D_n = ballExhaustion z r a n`
and the shell functional `shellTime (D_n) (B_r(z)) T` (`S3t/BoundaryShells.lean`); the walk measurability of the stopped
occupation and of the shell functional is proved (`S3t/Integrate.lean`).

Notation (answer section 3): `W ε ω q := interpolatedWalk ε (S.η ω) (S.mε ε) q` is the interpolated walk,
`X ω b := rescaledLBMPath (S.clock ω) S.m₀ b` the rescaled LBM path, and the quenched walk law is
`srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- Sum of a term converging to `0` in probability and a term converging in probability to `Y`. Same statement and
proof as `MatedCRT.TruncatedLawsBridge.tendstoInProbability_add_of_zero` (`FirstPass/S3S4b/TruncatedLawsBridge.lean`),
restated here to keep the `S3t` closure free of the first-pass bridge. -/
theorem tendstoInProbability_add_of_zero_left {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D X : ℝ → Ω → ℝ} {Y : Ω → ℝ}
    (hD : TendstoInProbability P D (fun _ : Ω => (0 : ℝ))) (hX : TendstoInProbability P X Y) :
    TendstoInProbability P (fun ε ω => D ε ω + X ε ω) Y := by
  intro δ hδ
  have h2 : (0 : ℝ) < δ / 2 := by positivity
  have hsum : Tendsto (fun ε => P {ω | δ / 2 < |D ε ω - (0 : ℝ)|} + P {ω | δ / 2 < |X ε ω - Y ω|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hD (δ / 2) h2).add (hX (δ / 2) h2)
    rwa [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro ε
  have hsub : {ω | δ < |D ε ω + X ε ω - Y ω|} ⊆
      {ω | δ / 2 < |D ε ω - (0 : ℝ)|} ∪ {ω | δ / 2 < |X ε ω - Y ω|} := by
    intro ω hω
    have htri := abs_add_le (D ε ω - 0) (X ε ω - Y ω)
    have heq : D ε ω - 0 + (X ε ω - Y ω) = D ε ω + X ε ω - Y ω := by ring
    rw [heq] at htri
    rcases lt_or_ge (δ / 2) |D ε ω - 0| with h1 | h1
    · exact Or.inl h1
    rcases lt_or_ge (δ / 2) |X ε ω - Y ω| with h2 | h2
    · exact Or.inr h2
    have hω' : δ < |D ε ω + X ε ω - Y ω| := hω
    linarith
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **Staged truncated-laws theorem** (Steps 11–12 and section 4 of the answer). For the disk `D = B_r(z)`, the concentric
exhaustion `D_n = ballExhaustion z r a n` (`a ≥ 0`, Step 6 uses `a = (r - |y - z|)/2`), the fixed-`T` quenched expected
truncated discrete occupation converges in probability to the quenched expected truncated LBM occupation, given the
outputs of Steps 5, 6, 7, 8 and 10 as hypotheses. The conclusion is the body of `FrozenTruncatedQuenchedLawsFixedTime`
at `ball z r`. -/
theorem truncatedQuenchedLawsFixedTime_of_steps {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    [IsProbabilityMeasure S.P] (z : ℂ) (r a : ℝ) (ha : 0 ≤ a) (y : ℂ) (g : ℂ → ℝ) (hgc : Continuous g)
    {T M C χ α : ℝ} (hT : 0 < T) (hg : ∀ x, |g x| ≤ M) (hM : 0 < M) (hχ : 0 < χ) (hα : 0 < α)
    {Good : ℝ → Ω → Prop}
    -- Step 5 (Theorem 2.11 with K = {y}): the stopped occupation converges to the LBM stopped occupation.
    (hOcc : TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation (Metric.ball z r) T g (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    -- Step 6: boundary-shell functionals, their convergence in probability, and their a.s. limit.
    (hShell : ∀ n, TendstoInProbability S.P
      (fun ε ω => ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    (hShellLimit : ∀ᵐ ω ∂S.P,
      Tendsto (fun n => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) atTop (𝓝 0))
    -- Named measurability of the LBM shell limit in the environment (G1: not written in the answer; see report).
    (hShellMeas : ∀ n, AEMeasurable (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P)
    -- Step 7: mesh-good events have probability tending to one (upper half of Lemma 2.8).
    (hMesh : Tendsto (fun ε => S.P {ω | ¬ Good ε ω}) (𝓝[>] (0 : ℝ)) (𝓝 0))
    -- Step 8: normalization error (lower half of MepsScalingInput).
    (hMInv : Tendsto (fun ε => (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < S.mε ε)
    -- Step 10: pathwise Riemann-sum estimate, for quenched-a.e. walk on the mesh-good event, for small ε (depending on n).
    (hpath : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
        |quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
            - stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)|
          ≤ T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹
            + M * shellTime (ballExhaustion z r a n) (Metric.ball z r) T (interpolatedWalk ε (S.η ω) (S.mε ε) q)) :
    TendstoInProbability S.P
      (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, rescaledLBMOccupation S ω (Metric.ball z r) (ENNReal.ofReal T) g b
        ∂planarBrownianMotion y) := by
  -- Step 8 and Step 7 give the deterministic error `E ε → 0`.
  have hE : Tendsto (fun ε : ℝ => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_deterministicError hα hχ hMInv
  -- Step 11: integrate the pathwise bound on the good event, for each shell index `n`.
  have hpath11 : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      |(∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        - ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
            ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)|
        ≤ (T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹)
          + M * ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
              (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
    intro n
    filter_upwards [hpath n, hmpos] with ε hε hm ω hG
    exact abs_quenchedDiscrete_sub_stopped_integral_le S ω hgc.measurable hg hT.le hm
      (W := fun q => interpolatedWalk ε (S.η ω) (S.mε ε) q)
      (Rq := fun q => shellTime (ballExhaustion z r a n) (Metric.ball z r) T (interpolatedWalk ε (S.η ω) (S.mε ε) q))
      (measurable_stoppedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T hgc)
      (measurable_shellTime_interpolatedWalk ε (S.η ω) (S.mε ε) z r a T n)
      (fun q => shellTime_nonneg (ballExhaustion_subset z r ha n) T _)
      (fun q => shellTime_le hT.le _) (hε ω hG)
  -- Step 12: epsilon first, shell width second: `A - C → 0` in probability.
  have hstep12 := tendstoInProbability_sub_zero_of_shell (P := S.P) hM
    (A := fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (C := fun ε ω => ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (R := fun n ε ω => ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
      (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (Rlim := fun n ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
      (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)
    (E := fun ε => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (Good := Good)
    hpath11 hE hMesh hShell hShellMeas hShellLimit
  -- Section 4: add the fixed-`T` LBM comparison of Step 5.
  have hsum := tendstoInProbability_add_of_zero_left hstep12 hOcc
  have hfun : (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      = (fun ε ω => (∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          - ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          + ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) := by
    funext ε ω
    ring
  rw [hfun]
  exact hsum


/-! ## Step 10 discharged: the walk estimate on the mesh-good event (fp-S3t, z8)

The walk inputs are proved, not assumed. The walk starts at `vertexOf ε η y` (`srwLaw_ae_start`); each step is
stationary or along an edge of positive multiplicity (`srwLaw_nonadjacent_null`); adjacent cells meet
(`adjacentCellsMeetAeStep`); the cell of `vertexOf ε η y` contains `y` (`MatedCRT.S5c.mem_cell_vertexOf_of_first_hit`),
whose first-hit hypothesis follows from the properness of `η` (`Tendsto η (cocompact ℝ) (cocompact ℂ)`). -/

/-- The almost-sure properties of the environment used by the walk estimate, at a fixed `ω`: `η ω` is continuous,
surjective and proper, and cells joined by an edge of the multiplicity graph meet. -/
def WalkEnvAe {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : Prop :=
  Continuous (S.η ω) ∧ Function.Surjective (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty

/-- A proper curve visits each point at bounded-below times (the preimage of a point is compact). -/
theorem bddBelow_preimage_of_tendsto_cocompact {η : ℝ → ℂ} (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (x : ℂ) :
    BddBelow {s : ℝ | η s = x} :=
  by
  have h1 : ({x} : Set ℂ)ᶜ ∈ cocompact ℂ := isCompact_singleton.compl_mem_cocompact
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (hp h1)
  refine hK.bddBelow.mono fun s hs => ?_
  by_contra hsK
  exact (hKs hsK : η s ∉ ({x} : Set ℂ)) (Set.mem_singleton_iff.2 hs)

/-- Consecutive cells of a walk are adjacent: a stationary step keeps the cell, and a step along an edge of positive
multiplicity meets by `adjacentCellsMeetAeStep`. -/
theorem walk_adjacent_cells {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (hε : 0 < ε)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (q : ℕ → ℤ)
    (hq : ∀ n : ℕ, q (n + 1) = q n ∨ m (q n) (q (n + 1)) ≠ 0) (n : ℕ) :
    (cell ε η (q n) ∩ cell ε η (q (n + 1))).Nonempty := by
  rcases hq n with h | h
  · rw [h, Set.inter_self]
    exact ⟨vertexPoint ε η (q n), vertexPoint_mem_cell_of_nonneg hε.le (q n)⟩
  · exact hedge _ _ h

/-- Pathwise walk estimate (truncated-laws Step 10, with the walk inputs proved): on the mesh-good event, for each `ε`
with `2 ε^α < δ` and `dist y z + ε^α < r`, the quenched discrete occupation differs from the stopped occupation by the
Riemann-sum error plus the shell functional of the disk `B_{r-δ}(z)`, for quenched-almost every walk. -/
theorem quenched_walk_bound {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ω : Ω} (hW : WalkEnvAe S ω)
    {γ ζ ρ ε : ℝ} (hε : 0 < ε) (hm : 0 < S.mε ε) (hG : MeshGood S γ ζ ρ ε ω)
    {z y : ℂ} {r δ T M : ℝ} {C χ : ℝ≥0} {g : ℂ → ℝ} (hgH : HolderOnWith C χ g (Metric.ball z r)) (hχ : 0 < χ)
    (hg : ∀ x, |g x| ≤ M) (hT : 0 ≤ T) (hr : 0 < r) (hyz : y ∈ Metric.ball z r)
    (hball : Metric.ball z r ⊆ Metric.ball 0 ρ) (hρ1 : ρ < 1)
    (hδ : 2 * ε ^ (2 / (2 + γ) ^ 2 - ζ) < δ) (hmarg : dist y z + ε ^ (2 / (2 + γ) ^ 2 - ζ) < r) :
    ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
      |quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
          - stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)|
        ≤ T * C * (2 * ε ^ (2 / (2 + γ) ^ 2 - ζ)) ^ (χ : ℝ) + 4 * M * (S.mε ε)⁻¹
          + M * shellTime (Metric.ball z (r - δ)) (Metric.ball z r) T
              (interpolatedWalk ε (S.η ω) (S.mε ε) q) := by
  obtain ⟨hη, hsurj, hcoc, hadj⟩ := hW
  have hD : Metric.ball z r ⊆ Metric.ball (0 : ℂ) ((1 + ρ) / 2) :=
    hball.trans (Metric.ball_subset_ball (by linarith))
  have hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ Metric.ball z r).Nonempty →
      Metric.diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := by
    rintro k ⟨p, hp1, hp2⟩
    exact hG k ⟨p, hp1, hD hp2⟩
  have hy_cell : y ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) y) :=
    MatedCRT.S5c.mem_cell_vertexOf_of_first_hit hε hsurj
      (fun x => bddBelow_preimage_of_tendsto_cocompact hcoc x) y
  have hdy : Metric.diam (cell ε (S.η ω) (vertexOf ε (S.η ω) y)) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
    hdiam _ ⟨y, hy_cell, hyz⟩
  have hq0 : vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (Metric.ball z r) :=
    vertexOf_mem_interiorCellVertices hη hy_cell hdy hmarg
  have hd0 : 0 ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := Real.rpow_nonneg hε.le _
  have hstart : ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y), q 0 = vertexOf ε (S.η ω) y :=
    srwLaw_ae_start _ _
  have hnadj : ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
      ∀ n : ℕ, q (n + 1) = q n ∨ S.mult ε ω (q n) (q (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    exact ae_iff.2 (MatedCRT.WalkSteps.srwLaw_nonadjacent_null _ n _)
  filter_upwards [hstart, hnadj] with q h0 hn
  have hq0' : q 0 ∈ interiorCellVertices ε (S.η ω) (Metric.ball z r) := by
    rw [h0]
    exact hq0
  have hadj' : ∀ j < ⌊T * S.mε ε⌋₊, (cell ε (S.η ω) (q j) ∩ cell ε (S.η ω) (q (j + 1))).Nonempty :=
    fun j _ => walk_adjacent_cells hε (fun j k => hadj ε hε j k) q hn j
  have hdiam' : ∀ j ≤ ⌊T * S.mε ε⌋₊, (cell ε (S.η ω) (q j) ∩ Metric.ball z r).Nonempty →
      Metric.diam (cell ε (S.η ω) (q j)) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
    fun j _ hj => hdiam (q j) hj
  have key := quenched_sub_stopped_le (C := C) (χ := χ) (z := z) (r := r) (M := M)
    (d := ε ^ (2 / (2 + γ) ^ 2 - ζ)) (δ := δ) (T := T) (g := g) hη hε hm hT hr hd0 hδ hgH hχ hg hq0' hadj' hdiam'
  unfold quenchedDiscreteOccupation stoppedOccupation shellTime
  exact key

/-- **Truncated quenched laws at a fixed time, staged with the walk inputs proved.** The Steps 7, 8 and 10 outputs are
now proved from the environment (`MeshGood`, `mepsInv_tendsto`, `quenched_walk_bound`); the remaining named inputs are
Step 5 (`hOcc`), Step 6 (`hShell`, `hShellLimit`) and the measurability `hShellMeas` (G1). -/
theorem truncatedQuenchedLawsFixedTime_of_walk {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    {ζ ρ : ℝ} (hζ0 : 0 < ζ) (hζγ : ζ < 2 / (2 + γ) ^ 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {z y : ℂ} {r a : ℝ} (hr : 0 < r) (hyz : y ∈ Metric.ball z r) (hball : Metric.ball z r ⊆ Metric.ball 0 ρ)
    (ha : 0 < a) (g : ℂ → ℝ) (hgc : Continuous g) {C χ : ℝ≥0} (hχ : 0 < χ)
    (hgH : HolderOnWith C χ g (Metric.ball z r)) {T M : ℝ} (hT : 0 < T) (hg : ∀ x, |g x| ≤ M) (hM : 0 < M)
    -- Step 5 (named input).
    (hOcc : TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation (Metric.ball z r) T g (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    -- Step 6 (named inputs).
    (hShell : ∀ n, TendstoInProbability S.P
      (fun ε ω => ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    (hShellLimit : ∀ᵐ ω ∂S.P,
      Tendsto (fun n => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) atTop (𝓝 0))
    -- G1 (named measurability input, see reports/z8.md).
    (hShellMeas : ∀ n, AEMeasurable (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P) :
    TendstoInProbability S.P
      (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, rescaledLBMOccupation S ω (Metric.ball z r) (ENNReal.ofReal T) g b
        ∂planarBrownianMotion y) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hα : 0 < 2 / (2 + γ) ^ 2 - ζ := by linarith
  have hWae : ∀ᵐ ω ∂S.P, WalkEnvAe S ω := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      adjacentCellsMeetAeStep 𝒮 γ hγ0 hγ2 Ω S hS] with ω hap hcoc hadj
    exact ⟨hap.1, hap.2.2.1, hcoc, hadj⟩
  obtain ⟨hmpos, hMInv⟩ := mepsInv_tendsto hm hγ0 hγ2 S hS
  -- Step 7: mesh-good events, up to the null set where the walk inputs fail.
  have hMesh : Tendsto (fun ε => S.P {ω | ¬ (MeshGood S γ ζ ρ ε ω ∧ WalkEnvAe S ω)}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hB := meshBad_tendsto_zero h28 hγ0 hγ2 hζ0 hζγ hρ0 hρ1 S hS
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun ε => zero_le) (fun ε => ?_)
    exact measure_mono_ae (hWae.mono fun ω hω h hA => h ⟨hA, hω⟩)
  -- Step 10: the pathwise walk estimate, for small `ε` depending on the shell index `n`.
  have hpath : ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, (MeshGood S γ ζ ρ ε ω ∧ WalkEnvAe S ω) →
      ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
        |quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
            - stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)|
          ≤ T * C * (2 * ε ^ (2 / (2 + γ) ^ 2 - ζ)) ^ (χ : ℝ) + 4 * M * (S.mε ε)⁻¹
            + M * shellTime (ballExhaustion z r a n) (Metric.ball z r) T
                (interpolatedWalk ε (S.η ω) (S.mε ε) q) := by
    intro n
    have hpow : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝 0)
          (𝓝 ((0 : ℝ) ^ (2 / (2 + γ) ^ 2 - ζ))) :=
        (continuous_id.rpow_const (fun _ => Or.inr hα.le)).tendsto 0
      rw [Real.zero_rpow hα.ne'] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ^ (2 / (2 + γ) ^ 2 - ζ) < a / ((n : ℝ) + 1) := by
      have h2 : Tendsto (fun ε : ℝ => 2 * ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)) :=
        hpow.const_mul 2
      rw [mul_zero] at h2
      exact Filter.Tendsto.eventually_lt_const (div_pos ha (by positivity)) h2
    have hmarg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist y z + ε ^ (2 / (2 + γ) ^ 2 - ζ) < r := by
      have h2 : Tendsto (fun ε : ℝ => dist y z + ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] (0 : ℝ))
          (𝓝 (dist y z + 0)) :=
        tendsto_const_nhds.add hpow
      rw [add_zero] at h2
      exact Filter.Tendsto.eventually_lt_const (Metric.mem_ball.1 hyz) h2
    filter_upwards [hδ, hmarg, hmpos, self_mem_nhdsWithin] with ε hδε hmε hmpos' hεmem
    intro ω hG
    exact quenched_walk_bound S hG.2 (Set.mem_Ioi.1 hεmem) hmpos' hG.1 hgH hχ hg hT.le hr hyz hball hρ1 hδε hmε
  exact truncatedQuenchedLawsFixedTime_of_steps S z r a ha.le y g hgc (T := T) (M := M) (C := (C : ℝ))
    (χ := (χ : ℝ)) (α := 2 / (2 + γ) ^ 2 - ζ) hT hg hM (by exact_mod_cast hχ) hα
    (Good := fun ε ω => MeshGood S γ ζ ρ ε ω ∧ WalkEnvAe S ω) hOcc hShell hShellLimit hShellMeas hMesh hMInv hmpos
    hpath

#print axioms truncatedQuenchedLawsFixedTime_of_steps
#print axioms truncatedQuenchedLawsFixedTime_of_walk

end MatedCRT.TruncatedLaws
