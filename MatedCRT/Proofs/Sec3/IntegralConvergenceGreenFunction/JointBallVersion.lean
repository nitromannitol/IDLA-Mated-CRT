import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ExitTimeClockChange
import MatedCRT.Proofs.Measurability.EnvSigmaCore

/-!
# Lemma 3.4 (item 3): a jointly measurable version of an environment-measurable family on a ball

For a family `f ω x` that is measurable in the environment (for each `x`, with respect to `S.envSigma`) and continuous
in `x` on a ball, there is a jointly measurable `F (ω, x)` equal to `f ω x` for almost every environment and every
`x` in the ball. The construction uses a dense sequence `w` in the ball, ambient-measurable versions of the countably
many slices `f · (w d)`, a measurable net index (the first `d` with `w d` within `ε` of `x`, for `x` in the ball), and
a limsup.
-/

open Classical

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- For every point some index qualifies: inside `B` by density, outside `B` every index qualifies. -/
lemma exists_netPred (B : Set ℂ) (w : ℕ → ℂ) (ε : ℝ) (hdense : ∀ x ∈ B, ∃ d, dist (w d) x < ε) (x : ℂ) :
    ∃ d, dist (w d) x < ε ∨ x ∉ B := by
  by_cases hx : x ∈ B
  · obtain ⟨d, hd⟩ := hdense x hx
    exact ⟨d, Or.inl hd⟩
  · exact ⟨0, Or.inr hx⟩

/-- The first index `d` with `dist (w d) x < ε` (for `x` in `B`); for `x ∉ B` it is `0`. -/
noncomputable def netIdx (B : Set ℂ) (w : ℕ → ℂ) (ε : ℝ) (hdense : ∀ x ∈ B, ∃ d, dist (w d) x < ε) (x : ℂ) :
    ℕ :=
  Nat.find (exists_netPred B w ε hdense x)

lemma netIdx_spec {B : Set ℂ} {w : ℕ → ℂ} {ε : ℝ} {hdense : ∀ x ∈ B, ∃ d, dist (w d) x < ε} {x : ℂ}
    (hx : x ∈ B) : dist (w (netIdx B w ε hdense x)) x < ε := by
  unfold netIdx
  rcases Nat.find_spec (exists_netPred B w ε hdense x) with h | h
  · exact h
  · exact absurd hx h

/-- The net index is measurable when `B` is measurable. -/
lemma measurable_netIdx {B : Set ℂ} (hB : MeasurableSet B) (w : ℕ → ℂ) (ε : ℝ)
    (hdense : ∀ x ∈ B, ∃ d, dist (w d) x < ε) : Measurable (netIdx B w ε hdense) := by
  refine measurable_find (exists_netPred B w ε hdense) fun d => ?_
  have hd : MeasurableSet {x : ℂ | dist (w d) x < ε} :=
    measurableSet_lt (Continuous.measurable (continuous_const.dist continuous_id)) measurable_const
  have hset : {x : ℂ | dist (w d) x < ε ∨ x ∉ B} = {x : ℂ | dist (w d) x < ε} ∪ Bᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
  rw [hset]
  exact hd.union hB.compl

/-- **Joint measurable version of an environment-measurable family on a ball.** -/
theorem exists_joint_version_ball {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {z : ℂ} {r : ℝ} (hr : 0 < r) (f : Ω → ℂ → ℝ)
    (hfm : ∀ x : ℂ, Measurable[S.envSigma] fun ω => f ω x)
    (hfc : ∀ ω, ContinuousOn (f ω) (ball z r)) :
    ∃ F : Ω × ℂ → ℝ, Measurable F ∧ ∀ᵐ ω ∂S.P, ∀ x ∈ ball z r, F (ω, x) = f ω x := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have : Nonempty (ball z r) := ⟨⟨z, hz⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (ball z r)
  let w : ℕ → ℂ := fun d => ((u d : ball z r) : ℂ)
  have hwB : ∀ d, w d ∈ ball z r := fun d => (u d).2
  have hdens : ∀ η : ℝ, 0 < η → ∀ x ∈ ball z r, ∃ d, dist (w d) x < η := by
    intro η hη x hx
    obtain ⟨d, hd⟩ := Metric.denseRange_iff.1 hu ⟨x, hx⟩ η hη
    refine ⟨d, ?_⟩
    rw [Subtype.dist_eq] at hd
    rw [dist_comm]
    exact hd
  -- ambient versions of the countably many slices `f · (w d)`
  have hG : ∀ d : ℕ, ∃ G : Ω → ℝ, Measurable G ∧ ∀ᵐ ω ∂S.P, f ω (w d) = G ω := by
    intro d
    have hA : AEMeasurable (fun ω => f ω (w d)) S.P := hS.aemeasurable_of_envSigma (hfm (w d))
    exact ⟨hA.mk _, hA.measurable_mk, hA.ae_eq_mk.mono fun ω h => h⟩
  choose G hGm hGae using hG
  have hall : ∀ᵐ ω ∂S.P, ∀ d : ℕ, f ω (w d) = G d ω := ae_all_iff.2 hGae
  -- the net of radii `1/(n+1)` and the measurable net indices
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by
    simp only [ε]
    positivity
  have hdn : ∀ n, ∀ x ∈ ball z r, ∃ d, dist (w d) x < ε n := fun n => hdens (ε n) (hεpos n)
  let idx : ℕ → ℂ → ℕ := fun n x => netIdx (ball z r) w (ε n) (hdn n) x
  have hidx : ∀ n, Measurable (idx n) := fun n => measurable_netIdx measurableSet_ball w (ε n) (hdn n)
  -- the joint approximations, with the countable index first
  let H : Ω × ℕ → ℝ := fun q => G q.2 q.1
  have hH : Measurable H := measurable_from_prod_countable_left fun k => hGm k
  let Fn : ℕ → Ω × ℂ → ℝ := fun n p => if p.2 ∈ ball z r then H (p.1, idx n p.2) else 0
  have hFn : ∀ n, Measurable (Fn n) := by
    intro n
    have hcomp : Measurable fun p : Ω × ℂ => H (p.1, idx n p.2) :=
      hH.comp (measurable_fst.prodMk ((hidx n).comp measurable_snd))
    exact Measurable.ite (measurable_snd measurableSet_ball) hcomp measurable_const
  refine ⟨fun p => limsup (fun n => Fn n p) atTop, Measurable.limsup fun n => hFn n, ?_⟩
  filter_upwards [hall] with ω hω
  intro x hx
  have hEq : ∀ n, Fn n (ω, x) = f ω (w (idx n x)) := by
    intro n
    show (if x ∈ ball z r then H (ω, idx n x) else 0) = f ω (w (idx n x))
    simp only [hx, ↓reduceIte, H]
    rw [hω (idx n x)]
  have hcw : Tendsto (fun n => w (idx n x)) atTop (𝓝[ball z r] x) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      exact (netIdx_spec (B := ball z r) (w := w) (ε := ε n) (hdense := hdn n) hx).le
    · exact Eventually.of_forall fun n => hwB _
  have hT : Tendsto (fun n => f ω (w (idx n x))) atTop (𝓝 (f ω x)) :=
    (hfc ω x hx).tendsto.comp hcw
  have hlim : Tendsto (fun n => Fn n (ω, x)) atTop (𝓝 (f ω x)) :=
    hT.congr fun n => (hEq n).symm
  show limsup (fun n => Fn n (ω, x)) atTop = f ω x
  exact hlim.limsup_eq

end MatedCRT
