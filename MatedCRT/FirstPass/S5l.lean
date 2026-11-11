import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed

/-!
# FirstPass S5l: the everywhere-positive measurable floor constant (Prop 5.1, Part I §5)

Generic form of the floor argument.
Let `What : Ω → ℂ → ℝ` be the continuum surplus `Ŵ(ω, ·)` and `G : ℂ → ℝ` the Green function `G_{B_ρ}(0, ·)`.

* `floorPhi` is the clamped function `φ_ω` of (8);
* `floorCentreEvent` is the event `A_q` of (9): `inf_{p ∈ D ∩ B̄_{δ/8}(q)} φ_ω(p) > 0`, with `D = ℚ + iℚ`
  (written as a uniform positive lower bound, equivalent since the index set is nonempty);
* `floorConstant` is the constant `s` of (9).

Results:
* `floorConstant_measurable_pos` (Step 5.1): `s` is measurable for the given σ-algebra on `Ω`, and `0 < s ω` for every `ω`.
  Positivity is deterministic: on `K = {x | dist(x, {φ_ω ≤ 0}) ≥ δ/8}`, a compact subset of `{φ_ω > 0}`, `φ_ω` has a
  positive minimum, and every `A_q` center lies in `K`.
* `floorConstant_controls` (Step 5.2): if `B(x, δ/4) ⊆ {φ_ω > 0}` (which is `dist(x, Λ_t^c) ≥ δ/4` for `Λ_t = {φ_ω > 0}`
  on the good event) and `x ≠ 0`, then `s(ω) ≤ φ_ω(x) ≤ α (Ŵ(ω, x) + t G(x))`.
* `floorCellConstant_measurable_pos` (13): `c = ℓ s / 2` is measurable and positive for `ℓ > 0`.

The hypotheses are exactly those §5 uses: measurable evaluations `ω ↦ Ŵ(ω, x)`; `Ŵ(ω)` continuous on `B̄_ρ` with zero
boundary values for every `ω`; `G` continuous on `B̄_ρ \ {0}`, zero on `∂B_ρ`, and `G → +∞` at the pole (logarithmic
singularity of the Green function, Armitage-Gardiner). The positivity `Ŵ + tG > 0` on `0 < |x| < ρ` is not used here; it
enters only through the identification `{φ_ω > 0} = Λ_t`, which is not part of this file. No external fact is used.
-/

namespace MatedCRT.S5l

open MeasureTheory Metric Set Filter Topology
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rational centre `(a, b) ↦ a + i b` of `D = ℚ + iℚ`. -/
def ratCentre (p : ℚ × ℚ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The countable set `D = ℚ + iℚ` of rational centres of §5, Step 5.1. -/
def ratComplex : Set ℂ := Set.range ratCentre

/-- The clamped function `φ_ω` of (8): `min(1, max(0, α(Ŵ(ω,x) + tG(x))))` on `0 < |x| < ρ`, `1` at `x = 0`, and `0`
for `|x| ≥ ρ`. -/
noncomputable def floorPhi (α t ρ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  if x = 0 then 1 else if ‖x‖ < ρ then min 1 (max 0 (α * (What ω x + t * G x))) else 0

/-- The event `A_q` of (9): `inf_{p ∈ D ∩ B̄_{δ/8}(q)} φ_ω(p) > 0`, written as a uniform positive lower bound. -/
def floorCentreEvent (α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (q : ℂ) : Set Ω :=
  {ω | ∃ c : ℝ, 0 < c ∧ ∀ p ∈ ratComplex ∩ closedBall q (δ / 8), c ≤ floorPhi α t ρ G What ω p}

/-- The term of the infimum (9): `φ_ω(q)` on `A_q`, and `1` off `A_q`, for `q = ratCentre p`. -/
noncomputable def floorTerm (α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) (p : ℚ × ℚ) : ℝ :=
  if ω ∈ floorCentreEvent α t ρ δ G What (ratCentre p) then floorPhi α t ρ G What ω (ratCentre p) else 1

/-- The constant `s` of (9): `s(ω) = inf_{q ∈ D} (φ_ω(q) on A_q, 1 off A_q)`. -/
noncomputable def floorConstant (α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) : ℝ :=
  ⨅ p : ℚ × ℚ, floorTerm α t ρ δ G What ω p

/-- The constant `c(ω) = ℓ s(ω) / 2` of (13). -/
noncomputable def floorCellConstant (ℓ α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) : ℝ :=
  ℓ * floorConstant α t ρ δ G What ω / 2

/-- The function `y ↦ 1` at `0`, `min(1, max(0, α(Ŵ(ω,y) + tG(y))))` elsewhere; it equals `φ_ω` on `B̄_ρ`. -/
noncomputable def floorG (α t : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) (y : ℂ) : ℝ :=
  if y = 0 then 1 else min 1 (max 0 (α * (What ω y + t * G y)))

lemma ratComplex_countable : ratComplex.Countable := by
  unfold ratComplex
  exact Set.countable_range _

/-- The rational centres are dense in `ℂ`. -/
lemma ratComplex_dense : Dense ratComplex := by
  rw [Metric.dense_iff]
  intro z r hr
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show z.re - r / 2 < z.re + r / 2 by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show z.im - r / 2 < z.im + r / 2 by linarith)
  refine ⟨ratCentre (a, b), ?_, ⟨(a, b), rfl⟩⟩
  rw [mem_ball, dist_eq_norm]
  have hre : (ratCentre (a, b) - z).re = (a : ℝ) - z.re := by simp [ratCentre]
  have him : (ratCentre (a, b) - z).im = (b : ℝ) - z.im := by simp [ratCentre]
  have h1 : |(a : ℝ) - z.re| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |(b : ℝ) - z.im| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  calc ‖ratCentre (a, b) - z‖ ≤ |(ratCentre (a, b) - z).re| + |(ratCentre (a, b) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < r := by rw [hre, him]; linarith

omit [MeasurableSpace Ω] in
lemma floorPhi_nonneg (α t ρ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) (x : ℂ) :
    0 ≤ floorPhi α t ρ G What ω x := by
  unfold floorPhi
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (le_max_left _ _)
  · exact le_rfl

omit [MeasurableSpace Ω] in
lemma floorPhi_le_one (α t ρ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) (x : ℂ) :
    floorPhi α t ρ G What ω x ≤ 1 := by
  unfold floorPhi
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
  · exact zero_le_one

lemma floorPhi_measurable (α t ρ : ℝ) (G : ℂ → ℝ) {What : Ω → ℂ → ℝ}
    (hWm : ∀ x, Measurable fun ω => What ω x) (x : ℂ) :
    Measurable fun ω => floorPhi α t ρ G What ω x := by
  by_cases h0 : x = 0
  · have hfun : (fun ω => floorPhi α t ρ G What ω x) = fun _ => (1 : ℝ) := by
      funext ω
      simp [floorPhi, h0]
    rw [hfun]
    exact measurable_const
  by_cases hρ : ‖x‖ < ρ
  · have hfun : (fun ω => floorPhi α t ρ G What ω x) =
        fun ω => min 1 (max 0 (α * (What ω x + t * G x))) := by
      funext ω
      simp [floorPhi, h0, hρ]
    rw [hfun]
    exact measurable_const.min (measurable_const.max (((hWm x).add_const (t * G x)).const_mul α))
  · have hfun : (fun ω => floorPhi α t ρ G What ω x) = fun _ => (0 : ℝ) := by
      funext ω
      simp [floorPhi, h0, hρ]
    rw [hfun]
    exact measurable_const

/-- The event `A_q` is measurable: an infimum over a countable set is positive iff it is bounded below by some
`1/(n+1)`. -/
lemma measurableSet_floorCentreEvent (α t ρ δ : ℝ) (G : ℂ → ℝ) {What : Ω → ℂ → ℝ}
    (hWm : ∀ x, Measurable fun ω => What ω x) (q : ℂ) :
    MeasurableSet (floorCentreEvent α t ρ δ G What q) := by
  have hcount : (ratComplex ∩ closedBall q (δ / 8)).Countable :=
    ratComplex_countable.mono Set.inter_subset_left
  have heq : floorCentreEvent α t ρ δ G What q =
      ⋃ n : ℕ, ⋂ p ∈ ratComplex ∩ closedBall q (δ / 8),
        {ω | 1 / ((n : ℝ) + 1) ≤ floorPhi α t ρ G What ω p} := by
    ext ω
    simp only [floorCentreEvent, mem_ofPred_eq, mem_iUnion, mem_iInter₂]
    constructor
    · rintro ⟨c, hc, hcp⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
      exact ⟨n, fun p hp => hn.le.trans (hcp p hp)⟩
    · rintro ⟨n, hn⟩
      exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩
  rw [heq]
  refine MeasurableSet.iUnion fun n => ?_
  exact MeasurableSet.biInter hcount fun p _ =>
    measurableSet_le measurable_const (floorPhi_measurable α t ρ G hWm p)

/-- Step 5.1, measurability: `s` is measurable (countable operations on measurable events and values). -/
theorem floorConstant_measurable (α t ρ δ : ℝ) (G : ℂ → ℝ) {What : Ω → ℂ → ℝ}
    (hWm : ∀ x, Measurable fun ω => What ω x) :
    Measurable (floorConstant α t ρ δ G What) := by
  unfold floorConstant floorTerm
  refine Measurable.iInf fun p => ?_
  exact Measurable.ite (measurableSet_floorCentreEvent α t ρ δ G hWm (ratCentre p))
    (floorPhi_measurable α t ρ G hWm (ratCentre p)) measurable_const

omit [MeasurableSpace Ω] in
lemma floorTerm_bddBelow (α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) :
    BddBelow (Set.range (floorTerm α t ρ δ G What ω)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨p, rfl⟩
  unfold floorTerm
  split_ifs
  · exact floorPhi_nonneg α t ρ G What ω _
  · exact zero_le_one

omit [MeasurableSpace Ω] in
lemma floorConstant_le_one (α t ρ δ : ℝ) (G : ℂ → ℝ) (What : Ω → ℂ → ℝ) (ω : Ω) :
    floorConstant α t ρ δ G What ω ≤ 1 := by
  refine (ciInf_le (floorTerm_bddBelow α t ρ δ G What ω) (0, 0)).trans ?_
  unfold floorTerm
  split_ifs
  · exact floorPhi_le_one α t ρ G What ω _
  · exact le_rfl

omit [MeasurableSpace Ω] in
/-- Continuity of `φ_ω` on `ℂ`: at `0` because `Ŵ(ω)` is bounded near `0` and `G → +∞`; at `∂B_ρ` because both
`Ŵ(ω)` and `G` vanish there. -/
theorem floorPhi_continuous {α t ρ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ}
    (hα : 0 < α) (ht : 0 < t) (hρ : 0 < ρ)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall 0 ρ))
    (hWb : ∀ ω x, ‖x‖ = ρ → What ω x = 0)
    (hGc : ContinuousOn G (closedBall 0 ρ \ {0}))
    (hGb : ∀ x, ‖x‖ = ρ → G x = 0)
    (hGp : Tendsto G (𝓝[≠] 0) atTop) (ω : Ω) :
    Continuous (floorPhi α t ρ G What ω) := by
  -- `floorG` is continuous within `B̄_ρ`
  have hgA : ContinuousOn (floorG α t G What ω) (closedBall 0 ρ) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      apply ContinuousAt.continuousWithinAt
      rw [← continuousWithinAt_compl_self]
      have hW0 : Tendsto (What ω) (𝓝[≠] 0) (𝓝 (What ω 0)) :=
        ((hWc ω).continuousAt (closedBall_mem_nhds 0 hρ)).tendsto.mono_left nhdsWithin_le_nhds
      have hsum : Tendsto (fun z => What ω z + t * G z) (𝓝[≠] 0) atTop :=
        Tendsto.congr (fun z => add_comm (t * G z) (What ω z))
          ((Tendsto.const_mul_atTop ht hGp).atTop_add hW0)
      have hge : ∀ᶠ z in 𝓝[≠] (0 : ℂ), 1 ≤ α * (What ω z + t * G z) :=
        (Tendsto.const_mul_atTop hα hsum).eventually_ge_atTop 1
      have hEq : floorG α t G What ω =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (1 : ℝ) := by
        filter_upwards [hge, self_mem_nhdsWithin] with z hz1 hz0
        have hz0' : z ≠ 0 := hz0
        simp [floorG, hz0']
        exact Or.inr hz1
      have hg0 : floorG α t G What ω 0 = 1 := by simp [floorG]
      show Tendsto (floorG α t G What ω) (𝓝[≠] (0 : ℂ)) (𝓝 (floorG α t G What ω 0))
      rw [hg0]
      exact tendsto_const_nhds.congr' hEq.symm
    · have hWy : ContinuousWithinAt (What ω) (closedBall 0 ρ) y := hWc ω y hy
      have hGy : ContinuousWithinAt G (closedBall 0 ρ) y :=
        (hGc y ⟨hy, hy0⟩).mono_of_mem_nhdsWithin
          (inter_mem_nhdsWithin (closedBall 0 ρ) (isOpen_compl_singleton.mem_nhds hy0))
      have hh : ContinuousWithinAt (fun z => min 1 (max 0 (α * (What ω z + t * G z))))
          (closedBall 0 ρ) y :=
        continuousWithinAt_const.min (continuousWithinAt_const.max
          (continuousWithinAt_const.mul (hWy.add (continuousWithinAt_const.mul hGy))))
      refine hh.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [inter_mem_nhdsWithin (closedBall 0 ρ) (isOpen_compl_singleton.mem_nhds hy0)] with z hz
        have hz0 : z ≠ 0 := hz.2
        simp [floorG, hz0]
      · simp [floorG, hy0]
  -- on `B̄_ρ`, `φ_ω = floorG`
  have hφg : ∀ y ∈ closedBall (0 : ℂ) ρ, floorPhi α t ρ G What ω y = floorG α t G What ω y := by
    intro y hy
    by_cases hy0 : y = 0
    · simp [floorPhi, floorG, hy0]
    · by_cases hyρ : ‖y‖ < ρ
      · simp [floorPhi, floorG, hy0, hyρ]
      · have hyeq : ‖y‖ = ρ := le_antisymm (mem_closedBall_zero_iff.1 hy) (not_lt.1 hyρ)
        simp [floorPhi, floorG, hy0, hyρ, hWb ω y hyeq, hGb y hyeq]
  have hA_mem : ∀ x ∈ closedBall (0 : ℂ) ρ,
      ContinuousWithinAt (floorPhi α t ρ G What ω) (closedBall 0 ρ) x := fun x hx =>
    ContinuousWithinAt.congr (hgA x hx) (fun y hy => hφg y hy) (hφg x hx)
  -- `φ_ω = 0` outside `B̄_ρ`
  have hzero : ∀ y, y ∉ closedBall (0 : ℂ) ρ → floorPhi α t ρ G What ω y = 0 := by
    intro y hy
    have hyρ : ρ < ‖y‖ := not_le.1 (fun h => hy (mem_closedBall_zero_iff.2 h))
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hyρ
      linarith
    simp [floorPhi, hy0, not_lt.2 hyρ.le]
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hxA : x ∈ closedBall (0 : ℂ) ρ
  · by_cases hxρ : ‖x‖ < ρ
    · have hAn : closedBall (0 : ℂ) ρ ∈ 𝓝 x :=
        Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hxρ)) ball_subset_closedBall
      exact (hA_mem x hxA).continuousAt hAn
    · have hxeq : ‖x‖ = ρ := le_antisymm (mem_closedBall_zero_iff.1 hxA) (not_lt.1 hxρ)
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hxeq
        linarith
      have hφx : floorPhi α t ρ G What ω x = 0 := by
        simp [floorPhi, hx0, hxρ]
      have hc : ContinuousWithinAt (fun _ : ℂ => (0 : ℝ)) (closedBall 0 ρ)ᶜ x :=
        continuousWithinAt_const
      have h2 : ContinuousWithinAt (floorPhi α t ρ G What ω) (closedBall 0 ρ)ᶜ x :=
        hc.congr (fun y hy => hzero y hy) hφx
      have h3 : ContinuousWithinAt (floorPhi α t ρ G What ω)
          (closedBall 0 ρ ∪ (closedBall 0 ρ)ᶜ) x :=
        (hA_mem x hxA).union h2
      rw [Set.union_compl_self] at h3
      exact (continuousWithinAt_univ _ _).1 h3
  · have hn : (closedBall (0 : ℂ) ρ)ᶜ ∈ 𝓝 x := isClosed_closedBall.isOpen_compl.mem_nhds hxA
    refine (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) x).congr ?_
    filter_upwards [hn] with y hy
    exact (hzero y hy).symm

omit [MeasurableSpace Ω] in
/-- The compact core of §5: `K = {x | dist(x, {φ_ω ≤ 0}) ≥ δ/8}`, a compact subset of `{φ_ω > 0}`. -/
lemma exists_lower_bound_on_core {α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (ω : Ω) (hcont : Continuous (floorPhi α t ρ G What ω)) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : ℂ, (∀ y, floorPhi α t ρ G What ω y ≤ 0 → δ / 8 ≤ dist x y) →
      m ≤ floorPhi α t ρ G What ω x := by
  obtain ⟨K, hKdef⟩ : ∃ K : Set ℂ, K = ⋂ y, ⋂ (_ : floorPhi α t ρ G What ω y ≤ 0),
      {x : ℂ | δ / 8 ≤ dist x y} := ⟨_, rfl⟩
  have hmemK : ∀ x, x ∈ K ↔ ∀ y, floorPhi α t ρ G What ω y ≤ 0 → δ / 8 ≤ dist x y := by
    intro x
    rw [hKdef]
    simp only [mem_iInter, mem_ofPred_eq]
  have hKc : IsClosed K := by
    rw [hKdef]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKU : ∀ x ∈ K, 0 < floorPhi α t ρ G What ω x := by
    intro x hx
    by_contra h
    replace h := not_lt.1 h
    have := (hmemK x).1 hx x h
    rw [dist_self] at this
    linarith
  have hKball : ∀ x ∈ K, ‖x‖ < ρ := by
    intro x hx
    by_contra h
    replace h := not_lt.1 h
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at h
      linarith
    have := hKU x hx
    simp [floorPhi, hx0, not_lt.2 h] at this
  have hKcpt : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc
      ((isBounded_closedBall (x := (0 : ℂ)) (r := ρ)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hKball x hx).le)
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    exact absurd ((hmemK x).2 hx) (by rw [hempty]; simp)
  · obtain ⟨x0, hx0K, hmin⟩ := hKcpt.exists_isMinOn hne hcont.continuousOn
    refine ⟨floorPhi α t ρ G What ω x0, hKU x0 hx0K, fun x hx => ?_⟩
    exact (isMinOn_iff.1 hmin) x ((hmemK x).2 hx)

omit [MeasurableSpace Ω] in
/-- A centre `q` whose closed ball of radius `δ/8` lies in `{φ_ω > 0}` satisfies `A_q` (compactness). -/
lemma floorCentreEvent_of_subset {α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ} (hδ : 0 < δ) (ω : Ω)
    {q : ℂ} (hcont : Continuous (floorPhi α t ρ G What ω))
    (hsub : closedBall q (δ / 8) ⊆ {y | 0 < floorPhi α t ρ G What ω y}) :
    ω ∈ floorCentreEvent α t ρ δ G What q := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_closedBall q (δ / 8)).exists_isMinOn
    (nonempty_closedBall.2 (by linarith)) hcont.continuousOn
  exact ⟨floorPhi α t ρ G What ω w, hsub hw, fun p hp => (isMinOn_iff.1 hmin) p hp.2⟩

omit [MeasurableSpace Ω] in
/-- **Step 5.1, positivity (§5, (10)).** For every `ω`, `0 < s(ω)`. Deterministic: the centres of `A_q` lie in the compact
core `K ⊆ {φ_ω > 0}`, on which `φ_ω` has a positive minimum; an off-core centre is excluded by density of `ℚ + iℚ`. -/
theorem floorConstant_pos {α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ}
    (hα : 0 < α) (ht : 0 < t) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall 0 ρ))
    (hWb : ∀ ω x, ‖x‖ = ρ → What ω x = 0)
    (hGc : ContinuousOn G (closedBall 0 ρ \ {0}))
    (hGb : ∀ x, ‖x‖ = ρ → G x = 0)
    (hGp : Tendsto G (𝓝[≠] 0) atTop) (ω : Ω) :
    0 < floorConstant α t ρ δ G What ω := by
  have hcont := floorPhi_continuous hα ht hρ hWc hWb hGc hGb hGp ω
  obtain ⟨m, hm, hmK⟩ := exists_lower_bound_on_core hρ hδ ω hcont
  have hterm : ∀ p : ℚ × ℚ, min 1 m ≤ floorTerm α t ρ δ G What ω p := by
    intro p
    unfold floorTerm
    split_ifs with hA
    · refine le_trans (min_le_right _ _) (hmK _ ?_)
      intro y hy
      by_contra hlt
      replace hlt := not_le.1 hlt
      obtain ⟨c, hc, hcp⟩ := hA
      have hV : IsOpen (ball (ratCentre p) (δ / 8) ∩ {z | floorPhi α t ρ G What ω z < c}) :=
        isOpen_ball.inter (isOpen_lt hcont continuous_const)
      have hyV : y ∈ ball (ratCentre p) (δ / 8) ∩ {z | floorPhi α t ρ G What ω z < c} :=
        ⟨mem_ball.2 (by rw [dist_comm]; exact hlt), lt_of_le_of_lt hy hc⟩
      obtain ⟨z, hzD, hzV⟩ := ratComplex_dense.exists_mem_open hV ⟨y, hyV⟩
      have hz1 := hcp z ⟨hzD, ball_subset_closedBall hzV.1⟩
      exact absurd hzV.2 (not_lt.2 hz1)
    · exact min_le_left _ _
  unfold floorConstant
  exact lt_of_lt_of_le (lt_min one_pos hm) (le_ciInf hterm)

omit [MeasurableSpace Ω] in
/-- **Step 5.2 (§5, (11)): the continuum floor controlled by `s`.** If `B(x, δ/4) ⊆ {φ_ω > 0}` (this is
`dist(x, Λ_t^c) ≥ δ/4` for `Λ_t = {φ_ω > 0}`, the identification of §5 on the good event) and `x ≠ 0`, then
`s(ω) ≤ φ_ω(x) ≤ α (Ŵ(ω, x) + t G(x))`. -/
theorem floorConstant_controls {α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ}
    (hα : 0 < α) (ht : 0 < t) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall 0 ρ))
    (hWb : ∀ ω x, ‖x‖ = ρ → What ω x = 0)
    (hGc : ContinuousOn G (closedBall 0 ρ \ {0}))
    (hGb : ∀ x, ‖x‖ = ρ → G x = 0)
    (hGp : Tendsto G (𝓝[≠] 0) atTop) (ω : Ω) (x : ℂ) (hx0 : x ≠ 0)
    (hball : ball x (δ / 4) ⊆ {y | 0 < floorPhi α t ρ G What ω y}) :
    floorConstant α t ρ δ G What ω ≤ floorPhi α t ρ G What ω x ∧
      floorPhi α t ρ G What ω x ≤ α * (What ω x + t * G x) := by
  have hcont := floorPhi_continuous hα ht hρ hWc hWb hGc hGb hGp ω
  -- every rational centre `z` within `δ/8` of `x` has `A_z`, hence `s ≤ φ_ω(z)`
  have hSz : ∀ z ∈ ball x (δ / 8) ∩ ratComplex,
      floorConstant α t ρ δ G What ω ≤ floorPhi α t ρ G What ω z := by
    rintro z ⟨hzB, p, rfl⟩
    have hsub : closedBall (ratCentre p) (δ / 8) ⊆ {y | 0 < floorPhi α t ρ G What ω y} := by
      intro y hy
      apply hball
      rw [mem_ball]
      have h1 := mem_closedBall.1 hy
      have h2 := mem_ball.1 hzB
      linarith [dist_triangle y (ratCentre p) x]
    have hA := floorCentreEvent_of_subset hδ ω hcont hsub
    calc floorConstant α t ρ δ G What ω ≤ floorTerm α t ρ δ G What ω p :=
          ciInf_le (floorTerm_bddBelow α t ρ δ G What ω) p
      _ = floorPhi α t ρ G What ω (ratCentre p) := by
          unfold floorTerm
          simp [hA]
  have hxcl : x ∈ closure (ball x (δ / 8) ∩ ratComplex) :=
    ratComplex_dense.open_subset_closure_inter isOpen_ball (mem_ball_self (by linarith))
  have hle : floorConstant α t ρ δ G What ω ≤ floorPhi α t ρ G What ω x :=
    le_on_closure (f := fun _ => floorConstant α t ρ δ G What ω)
      (g := floorPhi α t ρ G What ω) hSz continuousOn_const hcont.continuousOn hxcl
  have hxU : 0 < floorPhi α t ρ G What ω x := hball (mem_ball_self (by linarith))
  have hxρ : ‖x‖ < ρ := by
    by_contra h
    replace h := not_lt.1 h
    simp [floorPhi, hx0, not_lt.2 h] at hxU
  have key : floorPhi α t ρ G What ω x = min 1 (max 0 (α * (What ω x + t * G x))) := by
    simp [floorPhi, hx0, hxρ]
  refine ⟨hle, ?_⟩
  rw [key] at hxU ⊢
  have hmax : 0 < max 0 (α * (What ω x + t * G x)) := lt_of_lt_of_le hxU (min_le_right _ _)
  have ha : 0 < α * (What ω x + t * G x) := (lt_max_iff.1 hmax).resolve_left (lt_irrefl 0)
  exact (min_le_right _ _).trans (le_of_eq (max_eq_right ha.le))

/-- **Step 5.1 (§5, Step 5.1), the statement used by `StoppedFloorCellStep`.** `s` is measurable for the given
σ-algebra on `Ω` and `0 < s(ω)` for every `ω`. -/
theorem floorConstant_measurable_pos {α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ}
    (hα : 0 < α) (ht : 0 < t) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hWm : ∀ x, Measurable fun ω => What ω x)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall 0 ρ))
    (hWb : ∀ ω x, ‖x‖ = ρ → What ω x = 0)
    (hGc : ContinuousOn G (closedBall 0 ρ \ {0}))
    (hGb : ∀ x, ‖x‖ = ρ → G x = 0)
    (hGp : Tendsto G (𝓝[≠] 0) atTop) :
    Measurable (floorConstant α t ρ δ G What) ∧ ∀ ω, 0 < floorConstant α t ρ δ G What ω :=
  ⟨floorConstant_measurable α t ρ δ G hWm,
    fun ω => floorConstant_pos hα ht hρ hδ hWc hWb hGc hGb hGp ω⟩

/-- **The constant `c = ℓ s / 2` of (13)**: measurable and strictly positive for `ℓ > 0`. -/
theorem floorCellConstant_measurable_pos {ℓ α t ρ δ : ℝ} {G : ℂ → ℝ} {What : Ω → ℂ → ℝ} (hℓ : 0 < ℓ)
    (hα : 0 < α) (ht : 0 < t) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hWm : ∀ x, Measurable fun ω => What ω x)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall 0 ρ))
    (hWb : ∀ ω x, ‖x‖ = ρ → What ω x = 0)
    (hGc : ContinuousOn G (closedBall 0 ρ \ {0}))
    (hGb : ∀ x, ‖x‖ = ρ → G x = 0)
    (hGp : Tendsto G (𝓝[≠] 0) atTop) :
    Measurable (floorCellConstant ℓ α t ρ δ G What) ∧
      ∀ ω, 0 < floorCellConstant ℓ α t ρ δ G What ω := by
  refine ⟨?_, fun ω => ?_⟩
  · unfold floorCellConstant
    exact ((floorConstant_measurable α t ρ δ G hWm).const_mul ℓ).div_const 2
  · unfold floorCellConstant
    exact div_pos (mul_pos hℓ (floorConstant_pos hα ht hρ hδ hWc hWb hGc hGb hGp ω)) two_pos

end MatedCRT.S5l
