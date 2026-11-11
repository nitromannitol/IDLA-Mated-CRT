import Mathlib.Probability.BrownianMotion.Basic

/-!
# Continuous version of a real Brownian motion (R-CV)

This file proves `ContVersion`, the continuous-version step of the arbitrary-space transfer of
DMS Remark 4.4: every real Brownian motion `B` on a probability space
has a process `D` with measurable coordinates that is again Brownian (Mathlib's
`ProbabilityTheory.IsBrownianReal`), is indistinguishable from `B` almost surely, and has every path continuous.

Construction (the standard continuous modification of Brownian motion). The field `cont` of
`IsBrownianReal` gives almost-surely continuous paths. Choose measurable versions `f t` of the coordinates
`B t`. Let `N` be a measurable null set containing every event where the path of `B` is discontinuous or where
`B` and `f` differ on the grid `{k/(n+1)}`. Off `N`, `D t` is the `limsup` over `n` of the grid values
`f (brownianGridTime n t)`, where `brownianGridTime n t ↑ t`; on `N`, `D` is `0`. Off `N`, `D` equals `B` at all
times at once, so `D` has the finite-dimensional laws of `B` (`IsPreBrownianReal.congr`) and continuous paths.

This file does not use the lattice-probability lemma `LatticeProb.IsBrownianReal.exists_continuous_indistinguishable`
(LatticeProb/Prob/BrownianPathCoords.lean:28), which does not build at the pinned Mathlib.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace MatedCRT.Sec1

/-- Grid approximant of `t : ℝ≥0` at level `n : ℕ`: `⌊t (n+1)⌋ / (n+1)`. It lies in `ℚ≥0`, is at most `t`,
and tends to `t` as `n → ∞` (`tendsto_brownianGridTime`). -/
def brownianGridTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ((⌊t * ((n : ℝ≥0) + 1)⌋₊ : ℕ) : ℝ≥0) / ((n : ℝ≥0) + 1)

lemma brownianGridTime_le (n : ℕ) (t : ℝ≥0) : brownianGridTime n t ≤ t := by
  unfold brownianGridTime
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

lemma lt_brownianGridTime_add (n : ℕ) (t : ℝ≥0) :
    t < brownianGridTime n t + 1 / ((n : ℝ≥0) + 1) := by
  unfold brownianGridTime
  rw [← add_div, lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one (t * ((n : ℝ≥0) + 1))

lemma tendsto_brownianGridTime (t : ℝ≥0) :
    Tendsto (fun n : ℕ => brownianGridTime n t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hlow : Tendsto (fun n : ℕ => (t : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
    have h0 : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) := tendsto_const_nhds
    simpa using h0.sub tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => ?_) (fun n => ?_)
  · show (t : ℝ) - 1 / ((n : ℝ) + 1) ≤ ((brownianGridTime n t : ℝ≥0) : ℝ)
    have h := NNReal.coe_lt_coe.2 (lt_brownianGridTime_add n t)
    push_cast at h
    linarith
  · show ((brownianGridTime n t : ℝ≥0) : ℝ) ≤ (t : ℝ)
    exact NNReal.coe_le_coe.2 (brownianGridTime_le n t)

/-- The continuous modification of the grid limits off the null set `N`: `t ↦ limsup_n f (grid n t)` on `Nᶜ`,
and `0` on `N`. -/
def brownianModif {Ω : Type} (N : Set Ω) (f : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Nᶜ.indicator (fun ω' => limsup (fun n : ℕ => f (brownianGridTime n t) ω') atTop) ω

lemma measurable_brownianModif {Ω : Type} [MeasurableSpace Ω] {N : Set Ω} (hN : MeasurableSet N)
    {f : ℝ≥0 → Ω → ℝ} (hfm : ∀ t, Measurable (f t)) (t : ℝ≥0) :
    Measurable (brownianModif N f t) := by
  unfold brownianModif
  exact (Measurable.limsup fun n : ℕ => hfm (brownianGridTime n t)).indicator hN.compl

lemma brownianModif_of_notMem {Ω : Type} {N : Set Ω} {f : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω}
    (hω : ω ∉ N) :
    brownianModif N f t ω = limsup (fun n : ℕ => f (brownianGridTime n t) ω) atTop :=
  Set.indicator_of_mem (show ω ∈ Nᶜ from hω) _

lemma brownianModif_of_mem {Ω : Type} {N : Set Ω} {f : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω}
    (hω : ω ∈ N) : brownianModif N f t ω = 0 :=
  Set.indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hω) _

/-- Off the null set, the modification equals the path of `B` at every time, once the grid values of `f`
agree with `B` on the grid and the path of `B` is continuous. -/
lemma brownianModif_eq {Ω : Type} {N : Set Ω} {f B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∉ N)
    (hgr : ∀ n k : ℕ, B ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω = f ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω)
    (hcont : Continuous fun t => B t ω) (t : ℝ≥0) :
    brownianModif N f t ω = B t ω := by
  rw [brownianModif_of_notMem hω]
  have hseq : (fun n : ℕ => f (brownianGridTime n t) ω) =
      fun n : ℕ => B (brownianGridTime n t) ω := by
    funext n
    exact (hgr n ⌊t * ((n : ℝ≥0) + 1)⌋₊).symm
  rw [hseq]
  exact ((hcont.tendsto t).comp (tendsto_brownianGridTime t)).limsup_eq

/-- **R-CV: continuous version of a real Brownian motion.** For every probability space `(Ω, P)` and every
`B : ℝ≥0 → Ω → ℝ` with `IsBrownianReal B P`, there is `D : ℝ≥0 → Ω → ℝ` with measurable coordinates,
`IsBrownianReal D P`, `D` indistinguishable from `B` almost surely, and every path `t ↦ D t ω` continuous. -/
def ContVersion : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∃ D : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (D t)) ∧ IsBrownianReal D P ∧
      (∀ᵐ ω ∂P, ∀ t, B t ω = D t ω) ∧ ∀ ω, Continuous fun t => D t ω

/-- Proof of R-CV (`ContVersion`): the continuous modification `brownianModif N f` of measurable grid versions
`f` of `B`, off a measurable null set `N` of bad events. -/
theorem contVersion_holds : ContVersion := by
  intro Ω _ P _ B hB
  have hpre : IsPreBrownianReal B P := hB.toIsPreBrownianReal
  obtain ⟨f, hfm, hfae⟩ : ∃ f : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (f t)) ∧ ∀ t, B t =ᵐ[P] f t :=
    ⟨fun t => (hpre.aemeasurable t).mk (B t), fun t => (hpre.aemeasurable t).measurable_mk,
      fun t => (hpre.aemeasurable t).ae_eq_mk⟩
  have hgrid : ∀ᵐ ω ∂P, ∀ n k : ℕ, B ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω =
      f ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hfae _
  obtain ⟨N, hsub, hNm, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 (hgrid.and hB.cont))
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hgoodN : ∀ ω, ω ∉ N → (∀ n k : ℕ, B ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω =
      f ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ω) ∧ Continuous fun t => B t ω := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  have hcontall : ∀ ω, Continuous fun t => brownianModif N f t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have hzero : (fun t => brownianModif N f t ω) = fun _ => 0 :=
        funext fun t => brownianModif_of_mem hω
      rw [hzero]
      exact continuous_const
    · have hg := hgoodN ω hω
      have heq : (fun t => brownianModif N f t ω) = fun t => B t ω :=
        funext fun t => brownianModif_eq hω hg.1 hg.2 t
      rw [heq]
      exact hg.2
  have hind : ∀ᵐ ω ∂P, ∀ t, B t ω = brownianModif N f t ω := by
    filter_upwards [hNae] with ω hω t
    exact (brownianModif_eq hω (hgoodN ω hω).1 (hgoodN ω hω).2 t).symm
  have hBD : IsBrownianReal (brownianModif N f) P :=
    { toIsPreBrownianReal := hpre.congr fun t => hind.mono fun ω h => h t
      cont := Filter.Eventually.of_forall hcontall }
  exact ⟨brownianModif N f, fun t => measurable_brownianModif hNm hfm t, hBD, hind, hcontall⟩

end MatedCRT.Sec1
