import MatedCRT.FirstPass.S2h.LogScale
import HarmonicBalls.Draft.Section3

/-!
# Pathwise cluster monotonicity and compatibility from the almost sure statements (fp-S2h, z1, round 12)

Step 1 of CHATGPT-cone-good-set.md Section 5.2-5.3 (the pathwise input of the log-GFF zero law). The Harmonic
Balls statements `ClusterMonotoneStmt` (Lemma 3.3, Draft Section 3, line 89) and `ClusterCompatibilityStmt` (Lemma 3.5,
Draft Section 3, line 119) hold almost surely, the first for all times and radii at once, the second for each fixed
real outer radius `R`. The deterministic `ClusterCompatAt` (LogScale.lean) quantifies over all real `R`; it follows
from its integer-radius form, which is almost surely a countable intersection (`ae_all_iff`), since any `R` lies below
the integer `⌈R⌉₊`, and the compatibility on `[s₁, R]` is the compatibility on `[s₁, ⌈R⌉₊]` restricted.
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls

/-- The clusters with pole `0` are time monotone for almost every field, from `ClusterMonotoneStmt` (HB Lemma 3.3)
with the pole `z = 0` (which lies in every ball `B_r`, `r > 0`). -/
theorem clusterMonoAt_of_stmt (hmono : ClusterMonotoneStmt.{0}) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hlt : γ < lqgQ γ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) :
    ∀ᵐ ω ∂P, ClusterMonoAt (μ ω) := by
  filter_upwards [hmono γ γ hγ hγ2 hlt Ω P hC hcirc μ hgff hlgm] with ω hω
  intro t₁ t₂ r ht₁ ht₁₂ hr
  exact hω t₁ t₂ r ht₁ ht₁₂ hr 0 (mem_ball_self hr)

/-- Compatibility at integer outer radii implies the compatibility `ClusterCompatAt` at every real outer radius: the
outer radius `R` is at most the integer `⌈R⌉₊`, and both intervals `[s₁, R]` and `[s₁, ⌈R⌉₊]` contain the points used. -/
theorem clusterCompatAt_of_forall_nat {ν : Measure ℂ}
    (h : ∀ N : ℕ, 0 < (N : ℝ) → ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, 0 < s₁ → s₁ ≤ N → ∀ s₂ ∈ Icc s₁ N,
      closure (HarmonicBalls.cluster ν s₂ 0 t) ⊆ ball 0 s₁ →
        ∀ s ∈ Icc s₁ N, HarmonicBalls.cluster ν s 0 t = HarmonicBalls.cluster ν s₂ 0 t) :
    ClusterCompatAt ν := by
  intro t ht s₁ R hs₁ hs₁R s₂ hs₂ hcl s hs
  have hRN : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hN : (0 : ℝ) < (⌈R⌉₊ : ℝ) := lt_of_lt_of_le (hs₁.trans_le hs₁R) hRN
  have hs₂N : s₂ ∈ Icc s₁ (⌈R⌉₊ : ℝ) := ⟨hs₂.1, hs₂.2.trans hRN⟩
  have hsN : s ∈ Icc s₁ (⌈R⌉₊ : ℝ) := ⟨hs.1, hs.2.trans hRN⟩
  exact h ⌈R⌉₊ hN t ht s₁ hs₁ (hs₁R.trans hRN) s₂ hs₂N hcl s hsN

/-- The clusters with pole `0` are compatible for almost every field, from `ClusterCompatibilityStmt` (HB Lemma 3.5) at
the integer outer radii `N` (for `N = 0` the hypothesis `0 < N` is false and the statement is vacuous), then
`clusterCompatAt_of_forall_nat`. -/
theorem ae_clusterCompatAt_of_stmt (hcomp : ClusterCompatibilityStmt.{0}) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hlt : γ < lqgQ γ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) :
    ∀ᵐ ω ∂P, ClusterCompatAt (μ ω) := by
  have h : ∀ N : ℕ, ∀ᵐ ω ∂P, 0 < (N : ℝ) → ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, 0 < s₁ → s₁ ≤ N →
      ∀ s₂ ∈ Icc s₁ N, closure (HarmonicBalls.cluster (μ ω) s₂ 0 t) ⊆ ball 0 s₁ →
        ∀ s ∈ Icc s₁ N, HarmonicBalls.cluster (μ ω) s 0 t = HarmonicBalls.cluster (μ ω) s₂ 0 t := by
    intro N
    by_cases hN : (0 : ℝ) < (N : ℝ)
    · filter_upwards [hcomp γ γ hγ hγ2 hlt Ω P hC hcirc μ hgff hlgm (N : ℝ) hN] with ω hω
      intro _ t ht s₁ hs₁ hs₁N s₂ hs₂ hcl s hs
      exact hω t ht s₁ hs₁N 0 (mem_ball_self hs₁) s₂ hs₂ hcl s hs
    · exact Eventually.of_forall fun ω h0 => absurd h0 hN
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact clusterCompatAt_of_forall_nat fun N => hω N

end MatedCRT
