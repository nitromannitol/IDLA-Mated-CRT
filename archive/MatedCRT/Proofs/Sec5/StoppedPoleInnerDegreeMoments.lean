import Mathlib
import MatedCRT.Proposed.StoppedPoleCanonicalMoments2026

/-!
# Inner-degree tail and moment component

Internal component of the moment proof for the inner degree `D = deg_in(H₀)` of GMS arXiv:1705.11161v5,
Definition 4.5 (pp. 32-33). It formalizes the written Chebyshev split and tail-to-moment integration on a probability space, for `ℝ≥0∞`-valued `D` and normalized masses `Y_C`.
No independence between the exceptional events `E_C` and the masses `Y_C` is used.

Proved here (no tail bound and no moment bound is assumed):
* `chebyshev_split`: `P(D > C) ≤ P(E_C^c) + C^{-β(1-ζ)} · E*[Y_C^β]` when `D ≤ C^ζ · Y_C` on `E_C` almost surely;
* `tail_le_of_split`: with a uniform β-moment `M` and an exceptional bound `K C^{-N}`,
  `P(D > C) ≤ M C^{-β(1-ζ)} + K C^{-N}` at one level `C`;
* `lintegral_pow_le_of_tail`: tail-to-moment by the layer-cake formula (Mathlib
  `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul`) with `q = β(1-ζ) > p` and `N > p`:
  `E[D^p] ≤ C₀^p + p M C₀^{p-q}/(q-p) + p K C₀^{p-N}/(N-p)`. This needs `AEMeasurable D P`
  (the measurability residual), used only for the Tonelli identity;
* `outer_pow_lt_top_of_split`: the same finiteness for the outer expectation `E*[D^p]`, with no measurability
  (through `tail_moment_outer`, in this file);
* `lintegral_pow_lt_top_of_split`: the combined finiteness from the named premises below (`hD` is not needed for this
  conclusion, see the next item);
* `lintegral_le_outerLIntegral`, `lintegral_pow_lt_top_of_outer`, `canonical_innerDegree_lintegral_lt_top_of_outer`: the
  plain lower integral is bounded by the outer integral with no measurability, so a finite outer expectation gives
  `∫⁻ D^p < ∞` without `AEMeasurable D P`;
* `exceptional_of_eq46`, `uniform_of_mass_beta`, `cover_of_printed`: the consumers of the printed GMS inputs
  (Lemma 4.3 (4.6) read at the level `C^ζ`, the mass-β moment of GMS p. 33, the coordinate change (4.3) and the
  inner-degree bound (4.20));
* `canonical_premises`, `canonical_innerDegree_lintegral_lt_top`, `canonical_innerDegree_outer_lt_top`: the canonical
  zero-cone model. Continuity of `η` comes from `IsAreaParametrized`; the layer-cake form has the single premise
  `AEMeasurable (deg_in ∘ η) P`, the outer form has none.

Moved here from `MatedCRT/Proposed/StoppedPoleCanonicalMoments2026.lean`, with names and namespace
`MatedCRT.StoppedCanonicalMoments` unchanged: `outer_markov`, `dyadic_identity`, `dyadic_tail_series_lt_top`,
`tail_moment_outer`, `gmsB0_subset_ball`, `image_mul_ball_one`, `pointwise_tail_bound`, `markov_power_bound`,
`tail_level_bound`. `gms_innerDegree_moment` is now the corollary of `canonical_innerDegree_outer_lt_top` (end of this
file), so the moment is proved once.

Named premises, hypothesis shapes and not literature Props: `CoverOnEvent`, `UniformMassMoment`,
`ExceptionalInversePoly`. The printed inputs are the Props of `StoppedPoleCanonicalMoments2026.lean`
(read-only here). The malformed printed range (4.22) and the sign of the last bound in (4.25) are not used.
Exponent ranges: `1 ≤ p`, `p < β < 4/γ²`, `ζ < 1 - p/β` (so `q = β(1-ζ) > p`), `N > p`.
The generic component uses no sign of `ζ`; `0 < ζ` enters only through the reparametrization `N ↦ N/ζ` of
Lemma 4.3 (4.6) and the printed mass-β range `0 < ζ < 1`.
-/

open MeasureTheory Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section
/-! ## Internal consequences moved from `MatedCRT/Proposed/StoppedPoleCanonicalMoments2026.lean`

The Chebyshev, dyadic-tail and moment proofs staged in the Proposed file (commit 9ec52ac) are moved here with their
statements and names unchanged, into the namespace `MatedCRT.StoppedCanonicalMoments`. The Proposed file keeps the
statements and does not import this file; this file imports it. The inner-degree moment `gms_innerDegree_moment` is
restated at the end of this file as a corollary of `MatedCRT.StoppedInnerDegreeMoments.canonical_innerDegree_outer_lt_top`,
so that the moment is proved once. -/
namespace MatedCRT.StoppedCanonicalMoments

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal
open MatedCRT

/-- Markov's inequality for the outer integral: `c^β · P[c < Y] ≤ E*[Y^β]` for `β > 0`. -/
theorem outer_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ≥0∞) {β : ℝ} (hβ : 0 < β)
    (c : ℝ≥0∞) :
    c ^ β * P {ω | c < Y ω} ≤ MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) := by
  unfold MatedCRT.outerLIntegral
  refine le_iInf fun G => le_iInf fun hG => le_iInf fun hYG => ?_
  have hsub : {ω | c < Y ω} ⊆ {ω | c ^ β ≤ G ω} := fun ω hω =>
    le_trans (ENNReal.rpow_le_rpow hω.le hβ.le) (hYG ω)
  calc c ^ β * P {ω | c < Y ω} ≤ c ^ β * P {ω | c ^ β ≤ G ω} := by
        gcongr
    _ ≤ ∫⁻ ω, G ω ∂P := mul_meas_ge_le_lintegral hG (c ^ β)

/-- The dyadic identity `(C₀ 2^{j+1})^p · M (C₀ 2^j)^{-q} = 2^p C₀^{p-q} M (2^{p-q})^j`. -/
theorem dyadic_identity (p q M C₀ : ℝ) (hC₀ : 0 < C₀) (j : ℕ) :
    (C₀ * 2 ^ (j + 1)) ^ p * (M * (C₀ * 2 ^ j) ^ (-q)) =
      (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by
  have hx : 0 < C₀ * 2 ^ j := by positivity
  have hsplit : (C₀ * 2 ^ j) ^ (p - q) = C₀ ^ (p - q) * ((2 : ℝ) ^ (p - q)) ^ j := by
    rw [Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_natCast (2 : ℝ) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast ((2 : ℝ) ^ (p - q)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hpow : (C₀ * 2 ^ j) ^ p * (C₀ * 2 ^ j) ^ (-q) = (C₀ * 2 ^ j) ^ (p - q) := by
    rw [← Real.rpow_add hx]
    ring_nf
  have h2 : C₀ * 2 ^ (j + 1) = (C₀ * 2 ^ j) * 2 := by ring
  rw [h2, Real.mul_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2)]
  calc (C₀ * 2 ^ j) ^ p * 2 ^ p * (M * (C₀ * 2 ^ j) ^ (-q))
      = 2 ^ p * M * ((C₀ * 2 ^ j) ^ p * (C₀ * 2 ^ j) ^ (-q)) := by ring
    _ = 2 ^ p * M * (C₀ ^ (p - q) * ((2 : ℝ) ^ (p - q)) ^ j) := by rw [hpow, hsplit]
    _ = (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by ring

/-- The dyadic series `∑_j 2^{(j+1)p}·(M (C₀2^j)^{-q} + K (C₀2^j)^{-N})` is finite when `p < q` and `p < N`. -/
theorem dyadic_tail_series_lt_top {p q N C₀ M K : ℝ} (hpq : p < q) (hpN : p < N) (hC₀ : 0 < C₀)
    (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) *
      (ENNReal.ofReal (M * (C₀ * 2 ^ j) ^ (-q)) + ENNReal.ofReal (K * (C₀ * 2 ^ j) ^ (-N))) < ⊤ := by
  have hr1 : (0 : ℝ) ≤ (2 : ℝ) ^ (p - q) := by positivity
  have hr1' : (2 : ℝ) ^ (p - q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (p - N) := by positivity
  have hr2' : (2 : ℝ) ^ (p - N) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) *
      (ENNReal.ofReal (M * (C₀ * 2 ^ j) ^ (-q)) + ENNReal.ofReal (K * (C₀ * 2 ^ j) ^ (-N))) =
      ENNReal.ofReal ((2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j) +
        ENNReal.ofReal ((2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j) := by
    intro j
    have hx1 : 0 ≤ (C₀ * 2 ^ (j + 1)) ^ p := by positivity
    have hx2 : 0 ≤ M * (C₀ * 2 ^ j) ^ (-q) := by positivity
    have hx3 : 0 ≤ K * (C₀ * 2 ^ j) ^ (-N) := by positivity
    have e1 := dyadic_identity p q M C₀ hC₀ j
    have e2 := dyadic_identity p N K C₀ hC₀ j
    have n1 : 0 ≤ (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by positivity
    have n2 : 0 ≤ (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j := by positivity
    rw [← ENNReal.ofReal_add hx2 hx3, ← ENNReal.ofReal_mul hx1,
      ← ENNReal.ofReal_add n1 n2]
    congr 1
    rw [mul_add, e1, e2]
  simp only [hterm]
  rw [ENNReal.tsum_add]
  have s1 : Summable (fun j : ℕ => (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j) :=
    (summable_geometric_of_lt_one hr1 hr1').mul_left _
  have s2 : Summable (fun j : ℕ => (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j) :=
    (summable_geometric_of_lt_one hr2 hr2').mul_left _
  have p1 : ∀ j : ℕ, 0 ≤ (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := fun j => by
    have : 0 ≤ M := hM
    positivity
  have p2 : ∀ j : ℕ, 0 ≤ (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j := fun j => by
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg p1 s1, ← ENNReal.ofReal_tsum_of_nonneg p2 s2]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- Tail-to-moment lemma (the Chebyshev and tail-integration step). If `P[X > C] ≤ M C^{-q} + K C^{-N}`
for all `C ≥ C₀`, with `p < q` and `p < N`, then the outer `p`-th moment of `X` is finite. The majorant uses measurable
supersets of the dyadic level sets `{X > C₀ 2^k}`, so no measurability of `X` is assumed. -/
theorem tail_moment_outer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ≥0∞) {p q N C₀ M K : ℝ} (hp : 0 < p) (hpq : p < q) (hpN : p < N) (hC₀ : 0 < C₀)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (htail : ∀ C : ℝ, C₀ ≤ C → P {ω | ENNReal.ofReal C < X ω} ≤
      ENNReal.ofReal (M * C ^ (-q)) + ENNReal.ofReal (K * C ^ (-N))) :
    MatedCRT.outerLIntegral P (fun ω => X ω ^ p) < ⊤ := by
  classical
  have hge : ∀ k : ℕ, C₀ ≤ C₀ * 2 ^ k := fun k =>
    le_mul_of_one_le_right hC₀.le (one_le_pow₀ (by norm_num))
  have hsup : ∀ k : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      {ω | ENNReal.ofReal (C₀ * 2 ^ k) < X ω} ⊆ B ∧
      P B = P {ω | ENNReal.ofReal (C₀ * 2 ^ k) < X ω} := fun k =>
    ⟨_, measurableSet_toMeasurable _ _, subset_toMeasurable _ _, measure_toMeasurable _⟩
  choose A hAm hAsub hAeq using hsup
  have hAb : ∀ k : ℕ, P (A k) ≤ ENNReal.ofReal (M * (C₀ * 2 ^ k) ^ (-q)) +
      ENNReal.ofReal (K * (C₀ * 2 ^ k) ^ (-N)) := fun k => by
    rw [hAeq k]
    exact htail _ (hge k)
  have hbd_tend : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (M * (C₀ * 2 ^ k) ^ (-q)) +
      ENNReal.ofReal (K * (C₀ * 2 ^ k) ^ (-N))) Filter.atTop (nhds 0) := by
    have hL : Filter.Tendsto (fun k : ℕ => C₀ * 2 ^ k) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hC₀
    have h1 : Filter.Tendsto (fun k : ℕ => M * (C₀ * 2 ^ k) ^ (-q)) Filter.atTop (nhds 0) := by
      have := ((tendsto_rpow_neg_atTop (show 0 < q by linarith)).comp hL).const_mul M
      simpa using this
    have h2 : Filter.Tendsto (fun k : ℕ => K * (C₀ * 2 ^ k) ^ (-N)) Filter.atTop (nhds 0) := by
      have := ((tendsto_rpow_neg_atTop (show 0 < N by linarith)).comp hL).const_mul K
      simpa using this
    simpa using (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
  have hTop : P {ω | X ω = ⊤} = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto' hbd_tend fun k => ?_
    refine le_trans (measure_mono ?_) (hAb k)
    intro ω hω
    have hω' : ENNReal.ofReal (C₀ * 2 ^ k) < X ω := by
      rw [show X ω = ⊤ from hω]
      exact ENNReal.ofReal_lt_top
    exact hAsub k hω'
  obtain ⟨Z, hZm, hZsub, hZeq⟩ : ∃ Z : Set Ω, MeasurableSet Z ∧ {ω | X ω = ⊤} ⊆ Z ∧
      P Z = P {ω | X ω = ⊤} :=
    ⟨_, measurableSet_toMeasurable _ _, subset_toMeasurable _ _, measure_toMeasurable _⟩
  have hZ0 : P Z = 0 := by rw [hZeq, hTop]
  have hterm_m : ∀ j : ℕ, Measurable ((A j).indicator
      (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p))) := fun j =>
    measurable_const.indicator (hAm j)
  obtain ⟨H, hHdef⟩ : ∃ H : Ω → ℝ≥0∞, ∀ ω, H ω = ENNReal.ofReal (C₀ ^ p) +
      (∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
      Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := ⟨_, fun ω => rfl⟩
  have hHm : Measurable H := by
    have hfun : H = fun ω => (ENNReal.ofReal (C₀ ^ p) +
        ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
        Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := funext hHdef
    rw [hfun]
    exact (measurable_const.add (Measurable.tsum fun j => hterm_m j)).add
      (measurable_const.indicator hZm)
  have hcore : ∀ ω, ω ∉ Z → X ω ^ p ≤ ENNReal.ofReal (C₀ ^ p) +
      ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω := by
    intro ω hZω
    have hXω : X ω ≠ ⊤ := fun h => hZω (hZsub (show ω ∈ {ω | X ω = ⊤} from h))
    by_cases hc : X ω ≤ ENNReal.ofReal C₀
    · calc X ω ^ p ≤ (ENNReal.ofReal C₀) ^ p := ENNReal.rpow_le_rpow hc hp.le
        _ = ENNReal.ofReal (C₀ ^ p) := ENNReal.ofReal_rpow_of_nonneg hC₀.le hp.le
        _ ≤ _ := le_self_add
    · rw [not_le] at hc
      have hex : ∃ j : ℕ, X ω ≤ ENNReal.ofReal (C₀ * 2 ^ (j + 1)) := by
        obtain ⟨n, hn⟩ := (((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hC₀).eventually_gt_atTop
          ((X ω).toReal)).exists
        refine ⟨n, ?_⟩
        rw [← ENNReal.ofReal_toReal hXω]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : C₀ * 2 ^ n ≤ C₀ * 2 ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC₀.le
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have hk := Nat.find_spec hex
      have hlt : ENNReal.ofReal (C₀ * 2 ^ Nat.find hex) < X ω := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
        · rw [h0]
          simpa using hc
        · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
          have hmin : ¬ X ω ≤ ENNReal.ofReal (C₀ * 2 ^ (j + 1)) := Nat.find_min hex (by omega)
          rw [hj]
          exact not_le.mp hmin
      have hωA : ω ∈ A (Nat.find hex) := hAsub _ hlt
      calc X ω ^ p ≤ (ENNReal.ofReal (C₀ * 2 ^ (Nat.find hex + 1))) ^ p :=
            ENNReal.rpow_le_rpow hk hp.le
        _ = ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le
        _ = (A (Nat.find hex)).indicator
              (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p)) ω :=
            (Set.indicator_of_mem hωA (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p))).symm
        _ ≤ ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω :=
            ENNReal.le_tsum (f := fun j => (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) (Nat.find hex)
        _ ≤ _ := le_add_self
  have hpt : ∀ ω, X ω ^ p ≤ H ω := by
    intro ω
    by_cases hZω : ω ∈ Z
    · rw [hHdef ω, Set.indicator_of_mem hZω, add_top]
      exact le_top
    · rw [hHdef ω]
      exact le_trans (hcore ω hZω) le_self_add
  have hout : MatedCRT.outerLIntegral P (fun ω => X ω ^ p) ≤ ∫⁻ ω, H ω ∂P := by
    unfold MatedCRT.outerLIntegral
    exact iInf_le_of_le H (iInf_le_of_le hHm (iInf_le_of_le (fun ω => hpt ω) le_rfl))
  have hint : ∫⁻ ω, H ω ∂P = ENNReal.ofReal (C₀ ^ p) +
      ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) := by
    have hfun : H = fun ω => (ENNReal.ofReal (C₀ ^ p) +
        ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
        Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := funext fun ω => by rw [hHdef ω, add_assoc]
    rw [hfun, lintegral_add_right _ (measurable_const.indicator hZm),
      lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_tsum fun j => (hterm_m j).aemeasurable, lintegral_indicator_const hZm, hZ0,
      mul_zero, add_zero]
    congr 1
    refine tsum_congr fun j => ?_
    rw [lintegral_indicator_const (hAm j)]
  have hfin : ENNReal.ofReal (C₀ ^ p) + ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) < ⊤ := by
    refine ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_)
      (dyadic_tail_series_lt_top hpq hpN hC₀ hM hK)⟩
    gcongr
    exact hAb j
  calc MatedCRT.outerLIntegral P (fun ω => X ω ^ p) ≤ ∫⁻ ω, H ω ∂P := hout
    _ = ENNReal.ofReal (C₀ ^ p) + ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) := hint
    _ < ⊤ := hfin

/-! ## Consequences of the published inputs: the inner-degree moment -/

/-- Geometry of the good event: if `η([-1,1]) ⊂ B_{R/8}(0)` and `η` is continuous, then `R > 0` and the closed ball
`B̄₀` of (4.19) lies in the open ball `B_R(0)`. A point `x₀` of maximal norm on the compact `η([-1,1])` gives
`diam η([-1,1]) ≤ 2 ‖x₀‖ < R/4`. -/
theorem gmsB0_subset_ball {η : ℝ → ℂ} (hη : Continuous η) {R : ℝ}
    (hE : η '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (R / 8)) :
    0 < R ∧ gmsB0 η ⊆ Metric.ball 0 R := by
  have hK : IsCompact (η '' Set.Icc (-1) 1) := isCompact_Icc.image hη
  have hne : (η '' Set.Icc (-1) 1).Nonempty := ⟨η 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨x₀, hx₀K, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hx₀ : ‖x₀‖ < R / 8 := by
    have h := hE hx₀K
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hdiam : Metric.diam (η '' Set.Icc (-1) 1) ≤ 2 * ‖x₀‖ := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' : ‖x‖ ≤ ‖x₀‖ := isMaxOn_iff.mp hmax x hx
    have hy' : ‖y‖ ≤ ‖x₀‖ := isMaxOn_iff.mp hmax y hy
    rw [dist_eq_norm]
    linarith [norm_sub_le x y]
  have hR : 0 < R := by
    have := norm_nonneg x₀
    linarith
  refine ⟨hR, fun z hz => ?_⟩
  unfold gmsB0 at hz
  have hz' : dist z 0 ≤ 4 * Metric.diam (η '' Set.Icc (-1) 1) := Metric.mem_closedBall.mp hz
  rw [dist_zero_right] at hz'
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- The image of the unit ball under multiplication by a positive real `R` is the ball of radius `R`. -/
theorem image_mul_ball_one {R : ℝ} (hR : 0 < R) :
    (fun z : ℂ => (R : ℂ) * z) '' Metric.ball 0 1 = Metric.ball 0 R := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact mul_lt_of_lt_one_right hR hw
  · intro hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    refine ⟨z / R, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
        div_lt_iff₀ hR]
      linarith
    · field_simp

/-- Pointwise inclusion of the level event on the good set: if `x > C` and `x ≤ μ_h(B̄₀)` with `η([-1,1]) ⊂ B_{R/8}(0)`,
then `C^{1-ζ} < C^{-ζ} μ_{h^b}(𝔻)` for `b` with `R = R_b` (the mass identity `μ_{h^b}(𝔻) = μ_h(B_R(0))` of (2.3)). -/
theorem pointwise_tail_bound {η : ℝ → ℂ} (hη : Continuous η) {R C ζ : ℝ} (hC1 : 1 < C) (_hζ0 : 0 < ζ)
    {μω : Measure ℂ} {Zω : ℝ≥0∞} (hZ : Zω = μω ((fun z : ℂ => (R : ℂ) * z) '' Metric.ball 0 1))
    {x : ℝ≥0∞} (hx : ENNReal.ofReal C < x) (hxle : x ≤ μω (gmsB0 η))
    (hE : η '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (R / 8)) :
    ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * Zω := by
  obtain ⟨hR, hsub⟩ := gmsB0_subset_ball hη hE
  have h1 : μω (gmsB0 η) ≤ μω (Metric.ball 0 R) := measure_mono hsub
  rw [← image_mul_ball_one hR] at h1
  have hmass : x ≤ Zω := by
    rw [hZ]
    exact hxle.trans h1
  have hlt : ENNReal.ofReal C < Zω := lt_of_lt_of_le hx hmass
  have hC0 : 0 < C := by linarith
  have hpos : 0 < ENNReal.ofReal (C ^ (-ζ)) := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hC0 _)
  have hfin : ENNReal.ofReal (C ^ (-ζ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (C ^ (1 - ζ)) = ENNReal.ofReal (C ^ (-ζ)) * ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]
    congr 1
    rw [show (1 - ζ) = -ζ + 1 by ring, Real.rpow_add hC0, Real.rpow_one]
  rw [hsplit, mul_comm (ENNReal.ofReal (C ^ (-ζ))) (ENNReal.ofReal C), mul_comm (ENNReal.ofReal (C ^ (-ζ))) Zω]
  exact ENNReal.mul_lt_mul_left hpos.ne' hfin hlt

/-- The Markov step for the normalized masses: if `E*[Y^β] ≤ M < ∞`, then `P[t < Y] ≤ M · t^{-β}` (outer
probability, `t > 0`). This is the Chebyshev inequality. -/
theorem markov_power_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ≥0∞) {β t : ℝ} (hβ : 0 < β)
    (ht : 0 < t) {M : ℝ≥0∞} (hMfin : M < ⊤) (hbd : MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) ≤ M) :
    P {ω | ENNReal.ofReal t < Y ω} ≤ ENNReal.ofReal (M.toReal * t ^ (-β)) := by
  have hmk := outer_markov P Y hβ (ENNReal.ofReal t)
  rw [ENNReal.ofReal_rpow_of_nonneg ht.le hβ.le] at hmk
  have hprod : ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal (t ^ β) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  have hM' : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMfin.ne
  calc P {ω | ENNReal.ofReal t < Y ω}
      = ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal (t ^ β) * P {ω | ENNReal.ofReal t < Y ω} := by
        rw [hprod, one_mul]
    _ = ENNReal.ofReal (t ^ (-β)) * (ENNReal.ofReal (t ^ β) * P {ω | ENNReal.ofReal t < Y ω}) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (t ^ (-β)) * M := by
        gcongr
        exact hmk.trans hbd
    _ = ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal M.toReal := by rw [hM']
    _ = ENNReal.ofReal (M.toReal * t ^ (-β)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm]

/-- The tail bound at one level `C > 1`, from the almost-sure inputs: the inner-degree bound (4.20), continuity of `η`
and the coordinate change (2.3) at `b = C^ζ`. Off the null set, `deg_in > C` forces `η([-1,1])` out of `B_{R/8}(0)`
or the mass `C^{-ζ} μ_{h^b}(𝔻)` above `C^{1-ζ}`.

Assumptions, exactly as used: `hX` (the inner-degree bound (4.20), almost surely), `hcont` (continuity of `η`, almost
surely) and `hcoord`, the transport identity at the single level `b = C^ζ` and the single ball `𝔻`: almost surely
`μbC ω 𝔻 = μ_h(R 𝔻)` with `R = coneScaleRadius γ (hcirc ω) (C^ζ)`. The measure-valued family `μbC` is an arbitrary
random measure satisfying `hcoord`; it is not assumed to be the LQG measure of `h^b`. No measurability of `X` or of
`deg_in` is assumed. -/
theorem tail_level_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ ζ C : ℝ} (hC1 : 1 < C) (hζ0 : 0 < ζ)
    {X : Ω → ℝ≥0∞} {η : Ω → ℝ → ℂ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {μbC : Ω → Measure ℂ}
    (hX : ∀ᵐ ω ∂P, X ω ≤ μ ω (gmsB0 (η ω))) (hcont : ∀ᵐ ω ∂P, Continuous (η ω))
    (hcoord : ∀ᵐ ω ∂P, μbC ω (Metric.ball 0 1) =
      μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1)) :
    P {ω | ENNReal.ofReal C < X ω} ≤
      P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
      P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)} := by
  have hgood : ∀ᵐ ω ∂P, (X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
      μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1) :=
    (hX.and hcont).and hcoord
  have hN0 : P {ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
      μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} = 0 :=
    ae_iff.mp hgood
  have hsub : {ω | ENNReal.ofReal C < X ω} ⊆
      {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} ∪
      ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) := by
    intro ω hω
    by_cases hE : η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)
    · by_cases hg : (X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1)
      · exact Or.inr (Or.inr (pointwise_tail_bound hg.1.2 hC1 hζ0 hg.2 hω hg.1.1 hE))
      · exact Or.inr (Or.inl hg)
    · exact Or.inl hE
  calc P {ω | ENNReal.ofReal C < X ω}
      ≤ P ({ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} ∪
          ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)})) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          P ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) :=
        measure_union_le _ _
    _ ≤ P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          (P {ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} +
        P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ = P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)} := by
        rw [hN0, zero_add]

end MatedCRT.StoppedCanonicalMoments


namespace MatedCRT.StoppedInnerDegreeMoments

open MatedCRT.StoppedCanonicalMoments

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Named covering premise: for every level `C > 1`, almost surely, on the event `E C`,
`D ≤ C^ζ · Y_C`. An internal hypothesis shape, not a literature Prop. -/
def CoverOnEvent (P : Measure Ω) (D : Ω → ℝ≥0∞) (Y : ℝ → Ω → ℝ≥0∞) (E : ℝ → Set Ω) (ζ : ℝ) : Prop :=
  ∀ C : ℝ, 1 < C → ∀ᵐ ω ∂P, ω ∈ E C → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y C ω

/-- Uniform β-moment of the normalized masses `Y_C` (GMS p. 33, `GMSMassBetaMomentStmt`), with a real bound `M ≥ 0`. -/
def UniformMassMoment (P : Measure Ω) (Y : ℝ → Ω → ℝ≥0∞) (β M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ C : ℝ, 1 < C → MatedCRT.outerLIntegral P (fun ω => Y C ω ^ β) ≤ ENNReal.ofReal M

/-- Inverse-polynomial bound for the exceptional events, for every `N > 0` (GMS Lemma 4.3 (4.6),
`GMSLemma43Eq46Stmt`), with a nonnegative constant `K`. -/
def ExceptionalInversePoly (P : Measure Ω) (E : ℝ → Set Ω) : Prop :=
  ∀ N : ℝ, 0 < N → ∃ K C₁ : ℝ, 0 ≤ K ∧ ∀ C : ℝ, C₁ ≤ C → P (E C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N))

/-- **Chebyshev split**. With outer integrals, so no measurability of `D`, `Y` or `E` is needed,
and with no independence: if `D ≤ C^ζ · Y` on `E` almost surely, then
`P(D > C) ≤ P(Eᶜ) + C^{-β(1-ζ)} · E*[Y^β]`. The exponent `β(1-ζ)` is the one written in r3, with a negative sign. -/
theorem chebyshev_split {P : Measure Ω} {D Y : Ω → ℝ≥0∞} {E : Set Ω} {β ζ C : ℝ}
    (hβ : 0 < β) (hC : 0 < C)
    (hcov : ∀ᵐ ω ∂P, ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω) :
    P {ω | ENNReal.ofReal C < D ω} ≤
      P Eᶜ + ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) := by
  have hsplit : ENNReal.ofReal (C ^ ζ) * ENNReal.ofReal (C ^ (1 - ζ)) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _), ← Real.rpow_add hC]
    simp
  have hz0 : ENNReal.ofReal (C ^ ζ) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hC ζ)).ne'
  have hztop : ENNReal.ofReal (C ^ ζ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : {ω | ENNReal.ofReal C < D ω} ⊆
      (Eᶜ ∪ {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}) ∪
        {ω | ¬ (ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω)} := by
    intro ω hω
    have hω' : ENNReal.ofReal C < D ω := hω
    by_cases hE : ω ∈ E
    · by_cases hle : D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω
      · have hlt : ENNReal.ofReal (C ^ ζ) * ENNReal.ofReal (C ^ (1 - ζ)) <
            ENNReal.ofReal (C ^ ζ) * Y ω := by
          rw [hsplit]
          exact lt_of_lt_of_le hω' hle
        exact Or.inl (Or.inr (lt_of_mul_lt_mul_left hlt zero_le))
      · exact Or.inr fun h => hle (h hE)
    · exact Or.inl (Or.inl hE)
  have hw : ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * ENNReal.ofReal (C ^ (1 - ζ)) ^ β = 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC.le _) hβ.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _), ← Real.rpow_mul hC.le, ← Real.rpow_add hC]
    rw [show -(β * (1 - ζ)) + (1 - ζ) * β = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]
  have hmk := outer_markov P Y hβ (ENNReal.ofReal (C ^ (1 - ζ)))
  have hY : P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω} ≤
      ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) := by
    calc P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}
        = (ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * ENNReal.ofReal (C ^ (1 - ζ)) ^ β) *
            P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω} := by rw [hw, one_mul]
      _ = ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) *
            (ENNReal.ofReal (C ^ (1 - ζ)) ^ β * P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}) :=
          mul_assoc _ _ _
      _ ≤ ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) :=
          mul_le_mul_of_nonneg_left hmk zero_le
  have hnull : P {ω | ¬ (ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω)} = 0 := ae_iff.1 hcov
  calc P {ω | ENNReal.ofReal C < D ω}
      ≤ P ((Eᶜ ∪ {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}) ∪
          {ω | ¬ (ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω)}) := measure_mono hsub
    _ ≤ P (Eᶜ ∪ {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}) +
          P {ω | ¬ (ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω)} := measure_union_le _ _
    _ ≤ (P Eᶜ + P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω}) + 0 := by
          rw [hnull]
          exact add_le_add (measure_union_le _ _) le_rfl
    _ = P Eᶜ + P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < Y ω} := add_zero _
    _ ≤ P Eᶜ + ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) :=
          add_le_add le_rfl hY

/-- **Single-level tail bound**: with the uniform β-moment `M` and the exceptional bound
`K C^{-N}`, `P(D > C) ≤ M C^{-β(1-ζ)} + K C^{-N}` at one level `C > 0`. -/
theorem tail_le_of_split {P : Measure Ω} {D Y : Ω → ℝ≥0∞} {E : Set Ω} {β ζ C M K N : ℝ}
    (hβ : 0 < β) (hC : 0 < C) (hM : 0 ≤ M)
    (hcov : ∀ᵐ ω ∂P, ω ∈ E → D ω ≤ ENNReal.ofReal (C ^ ζ) * Y ω)
    (hmom : MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) ≤ ENNReal.ofReal M)
    (hexc : P Eᶜ ≤ ENNReal.ofReal (K * C ^ (-N))) :
    P {ω | ENNReal.ofReal C < D ω} ≤
      ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) + ENNReal.ofReal (K * C ^ (-N)) := by
  have hw : ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) ≤
      ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) := by
    calc ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β)
        ≤ ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * ENNReal.ofReal M := mul_le_mul_of_nonneg_left hmom zero_le
      _ = ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) := by
          rw [ENNReal.ofReal_mul hM]
          ring
  calc P {ω | ENNReal.ofReal C < D ω}
      ≤ P Eᶜ + ENNReal.ofReal (C ^ (-(β * (1 - ζ)))) * MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) :=
        chebyshev_split hβ hC hcov
    _ ≤ ENNReal.ofReal (K * C ^ (-N)) + ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) := add_le_add hexc hw
    _ = ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) + ENNReal.ofReal (K * C ^ (-N)) := add_comm _ _

/-- **Tail-to-moment by the layer-cake formula**. If `P(D > C) ≤ M C^{-q} + K C^{-N}` for all
`C ≥ C₀`, with `p < q` and `p < N`, then `E[D^p] ≤ C₀^p + p M C₀^{p-q}/(q-p) + p K C₀^{p-N}/(N-p)`.
The premise `hD : AEMeasurable D P` is used only for the Tonelli identity (the measurability residual). -/
theorem lintegral_pow_le_of_tail {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → ℝ≥0∞}
    (hD : AEMeasurable D P) {p q N C₀ M K : ℝ} (hp : 1 ≤ p) (hpq : p < q) (hpN : p < N) (hC₀ : 0 < C₀)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (htail : ∀ C : ℝ, C₀ ≤ C → P {ω | ENNReal.ofReal C < D ω} ≤
      ENNReal.ofReal (M * C ^ (-q)) + ENNReal.ofReal (K * C ^ (-N))) :
    ∫⁻ ω, D ω ^ p ∂P ≤ ENNReal.ofReal (C₀ ^ p) +
      ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) +
      ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p)) := by
  have hp0 : 0 < p := by linarith
  -- Step 1: `D < ⊤` almost surely, since the tail bound tends to `0` as `C → ∞`.
  have htop : P {ω | D ω = ⊤} = 0 := by
    have hlim : Tendsto (fun C : ℝ => ENNReal.ofReal (M * C ^ (-q)) + ENNReal.ofReal (K * C ^ (-N)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun C : ℝ => M * C ^ (-q)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < q)).const_mul M
      have h2 : Tendsto (fun C : ℝ => K * C ^ (-N)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < N)).const_mul K
      simpa using (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hlim (eventually_atTop.2 ⟨C₀, fun C hC => ?_⟩)
    refine le_trans (measure_mono ?_) (htail C hC)
    intro ω hω
    have hω' : D ω = ⊤ := hω
    show ENNReal.ofReal C < D ω
    rw [hω']
    exact ENNReal.ofReal_lt_top
  have hae : ∀ᵐ ω ∂P, D ω ≠ ⊤ := by
    rw [ae_iff]
    simpa using htop
  -- Step 2: the layer-cake formula for `(D ·).toReal`, with the power integral `∫₀^x p s^{p-1} ds = x^p`.
  have hint : ∀ t : ℝ, 0 < t → IntervalIntegrable (fun s : ℝ => p * s ^ (p - 1)) volume 0 t := fun t _ =>
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1)).const_mul p
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ p * s ^ (p - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg hp0.le (Real.rpow_nonneg (Set.mem_Ioi.1 hs).le _)
  have hint_eq : ∀ x : ℝ, 0 ≤ x → ∫ s in (0 : ℝ)..x, p * s ^ (p - 1) = x ^ p := by
    intro x _hx
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne', sub_zero]
    field_simp
  have hf_meas : AEMeasurable (fun ω => (D ω).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable hD
  have hLC := lintegral_comp_eq_lintegral_meas_lt_mul P (f := fun ω => (D ω).toReal)
    (g := fun s : ℝ => p * s ^ (p - 1)) (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    hf_meas hint hnn
  have hL : ∫⁻ ω, D ω ^ p ∂P =
      ∫⁻ s in Ioi (0 : ℝ), P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) := by
    calc ∫⁻ ω, D ω ^ p ∂P = ∫⁻ ω, ENNReal.ofReal ((D ω).toReal ^ p) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le, ENNReal.ofReal_toReal hω]
      _ = ∫⁻ ω, ENNReal.ofReal (∫ s in (0 : ℝ)..(D ω).toReal, p * s ^ (p - 1)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hint_eq _ ENNReal.toReal_nonneg]
      _ = _ := hLC
  -- Step 3: split the `s`-integral at `C₀`.
  have hA : ∫⁻ s in Ioc (0 : ℝ) C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) ≤
      ENNReal.ofReal (C₀ ^ p) := by
    have hfi : IntegrableOn (fun s : ℝ => p * s ^ (p - 1)) (Ioc (0 : ℝ) C₀) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hC₀.le).1 (hint C₀ hC₀)
    have hfnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) C₀)] (fun s : ℝ => p * s ^ (p - 1)) :=
      (ae_restrict_mem measurableSet_Ioc).mono fun s hs =>
        mul_nonneg hp0.le (Real.rpow_nonneg (le_of_lt hs.1) _)
    calc ∫⁻ s in Ioc (0 : ℝ) C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1))
        ≤ ∫⁻ s in Ioc (0 : ℝ) C₀, ENNReal.ofReal (p * s ^ (p - 1)) :=
          lintegral_mono fun s => mul_le_of_le_one_left zero_le prob_le_one
      _ = ENNReal.ofReal (∫ s in Ioc (0 : ℝ) C₀, p * s ^ (p - 1)) :=
          (ofReal_integral_eq_lintegral_ofReal hfi hfnn).symm
      _ = ENNReal.ofReal (C₀ ^ p) := by
          rw [← intervalIntegral.integral_of_le hC₀.le, hint_eq C₀ hC₀.le]
  have hB : ∫⁻ s in Ioi C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) ≤
      ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) +
        ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p)) := by
    have hpt : ∀ s ∈ Ioi C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) ≤
        ENNReal.ofReal (p * M * s ^ (p - 1 - q)) + ENNReal.ofReal (p * K * s ^ (p - 1 - N)) := by
      intro s hs
      have hs0 : 0 < s := lt_trans hC₀ hs
      have hsub : {ω | s < (D ω).toReal} ⊆ {ω | ENNReal.ofReal s < D ω} := by
        intro ω hω
        have hω' : s < (D ω).toReal := hω
        show ENNReal.ofReal s < D ω
        by_cases hDt : D ω = ⊤
        · rw [hDt]
          exact ENNReal.ofReal_lt_top
        · exact (ENNReal.ofReal_lt_iff_lt_toReal hs0.le hDt).2 hω'
      have hbd := (measure_mono hsub).trans (htail s (le_of_lt hs))
      have e1 : ENNReal.ofReal (M * s ^ (-q)) * ENNReal.ofReal (p * s ^ (p - 1)) =
          ENNReal.ofReal (p * M * s ^ (p - 1 - q)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hM (Real.rpow_nonneg hs0.le _))]
        congr 1
        rw [show p - 1 - q = (p - 1) + (-q) by ring, Real.rpow_add hs0]
        ring
      have e2 : ENNReal.ofReal (K * s ^ (-N)) * ENNReal.ofReal (p * s ^ (p - 1)) =
          ENNReal.ofReal (p * K * s ^ (p - 1 - N)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hs0.le _))]
        congr 1
        rw [show p - 1 - N = (p - 1) + (-N) by ring, Real.rpow_add hs0]
        ring
      calc P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1))
          ≤ (ENNReal.ofReal (M * s ^ (-q)) + ENNReal.ofReal (K * s ^ (-N))) *
              ENNReal.ofReal (p * s ^ (p - 1)) := mul_le_mul_of_nonneg_right hbd zero_le
        _ = ENNReal.ofReal (M * s ^ (-q)) * ENNReal.ofReal (p * s ^ (p - 1)) +
              ENNReal.ofReal (K * s ^ (-N)) * ENNReal.ofReal (p * s ^ (p - 1)) := add_mul _ _ _
        _ = ENNReal.ofReal (p * M * s ^ (p - 1 - q)) + ENNReal.ofReal (p * K * s ^ (p - 1 - N)) := by
          rw [e1, e2]
    have hm1 : Measurable (fun s : ℝ => ENNReal.ofReal (p * M * s ^ (p - 1 - q))) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).const_mul _)
    have hm2 : Measurable (fun s : ℝ => ENNReal.ofReal (p * K * s ^ (p - 1 - N))) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).const_mul _)
    have hI1 : ∫⁻ s in Ioi C₀, ENNReal.ofReal (p * M * s ^ (p - 1 - q)) =
        ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) := by
      have hint1 : IntegrableOn (fun s : ℝ => p * M * s ^ (p - 1 - q)) (Ioi C₀) :=
        Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hC₀) (p * M)
      have hnn1 : 0 ≤ᵐ[volume.restrict (Ioi C₀)] (fun s : ℝ => p * M * s ^ (p - 1 - q)) :=
        (ae_restrict_mem measurableSet_Ioi).mono fun s hs =>
          mul_nonneg (mul_nonneg hp0.le hM) (Real.rpow_nonneg (le_trans hC₀.le (le_of_lt hs)) _)
      rw [← ofReal_integral_eq_lintegral_ofReal hint1 hnn1, integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) hC₀]
      congr 1
      rw [show p - 1 - q + 1 = p - q by ring, show q - p = -(p - q) by ring, div_neg]
      ring
    have hI2 : ∫⁻ s in Ioi C₀, ENNReal.ofReal (p * K * s ^ (p - 1 - N)) =
        ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p)) := by
      have hint2 : IntegrableOn (fun s : ℝ => p * K * s ^ (p - 1 - N)) (Ioi C₀) :=
        Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hC₀) (p * K)
      have hnn2 : 0 ≤ᵐ[volume.restrict (Ioi C₀)] (fun s : ℝ => p * K * s ^ (p - 1 - N)) :=
        (ae_restrict_mem measurableSet_Ioi).mono fun s hs =>
          mul_nonneg (mul_nonneg hp0.le hK) (Real.rpow_nonneg (le_trans hC₀.le (le_of_lt hs)) _)
      rw [← ofReal_integral_eq_lintegral_ofReal hint2 hnn2, integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) hC₀]
      congr 1
      rw [show p - 1 - N + 1 = p - N by ring, show N - p = -(p - N) by ring, div_neg]
      ring
    calc ∫⁻ s in Ioi C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1))
        ≤ ∫⁻ s in Ioi C₀, (ENNReal.ofReal (p * M * s ^ (p - 1 - q)) +
            ENNReal.ofReal (p * K * s ^ (p - 1 - N))) := setLIntegral_mono (hm1.add hm2) hpt
      _ = (∫⁻ s in Ioi C₀, ENNReal.ofReal (p * M * s ^ (p - 1 - q))) +
            ∫⁻ s in Ioi C₀, ENNReal.ofReal (p * K * s ^ (p - 1 - N)) := lintegral_add_left hm1 _
      _ = ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) +
            ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p)) := by rw [hI1, hI2]
  -- Step 4: assemble.
  calc ∫⁻ ω, D ω ^ p ∂P
      = ∫⁻ s in Ioi (0 : ℝ), P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) := hL
    _ = (∫⁻ s in Ioc (0 : ℝ) C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1))) +
          ∫⁻ s in Ioi C₀, P {ω | s < (D ω).toReal} * ENNReal.ofReal (p * s ^ (p - 1)) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi hC₀.le,
          lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    _ ≤ ENNReal.ofReal (C₀ ^ p) + (ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) +
          ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p))) := add_le_add hA hB
    _ = ENNReal.ofReal (C₀ ^ p) + ENNReal.ofReal (p * M * C₀ ^ (p - q) / (q - p)) +
          ENNReal.ofReal (p * K * C₀ ^ (p - N) / (N - p)) := (add_assoc _ _ _).symm

/-- The exponent gap: `ζ < 1 - p/β` gives `q = β(1-ζ) > p`. -/
theorem exponent_gap {β ζ p : ℝ} (hp1 : 1 ≤ p) (hpβ : p < β) (hζ1 : ζ < 1 - p / β) :
    p < β * (1 - ζ) := by
  have hβ0 : 0 < β := by linarith
  have h1 : p / β < 1 - ζ := by linarith
  have h2 := (div_lt_iff₀ hβ0).1 h1
  rw [mul_comm] at h2
  exact h2

/-- The tail bound at every level `C ≥ C₀ := max C₁ 1 + 1`, from the covering, the uniform β-moment and the
exceptional bound (the one-level bound of `tail_le_of_split`, read at all levels above `C₀`). -/
theorem tail_bound_of_premises {P : Measure Ω} {D : Ω → ℝ≥0∞} {Y : ℝ → Ω → ℝ≥0∞} {E : ℝ → Set Ω}
    {β ζ M K N C₁ : ℝ}
    (hβ : 0 < β) (hcov : CoverOnEvent P D Y E ζ) (hmom : UniformMassMoment P Y β M)
    (hexc : ∀ C : ℝ, C₁ ≤ C → P (E C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N))) :
    ∀ C : ℝ, max C₁ 1 + 1 ≤ C → P {ω | ENNReal.ofReal C < D ω} ≤
      ENNReal.ofReal (M * C ^ (-(β * (1 - ζ)))) + ENNReal.ofReal (K * C ^ (-N)) := by
  intro C hC
  have hC1 : 1 < C := by linarith [le_max_right C₁ 1]
  have hCC₁ : C₁ ≤ C := by linarith [le_max_left C₁ 1]
  exact tail_le_of_split hβ (by linarith) hmom.1 (hcov C hC1) (hmom.2 C hC1) (hexc C hCC₁)

/-- **Tail-to-moment, layer-cake form** (with the premises named). From the covering on the events
`E_C`, the uniform β-moment `M`, and the inverse-polynomial exceptional bound `K C^{-N}`, with the exponent ranges
`1 ≤ p`, `p < β`, `ζ < 1 - p/β` and `p < N`, the `p`-th moment of `D` is finite. The only measurability premise is
`hD : AEMeasurable D P` (the measurability residual), used only through `lintegral_pow_le_of_tail`; the conclusion does not need
it (see `lintegral_pow_lt_top_of_outer`). No independence of `E_C` and `Y_C` is used. -/
theorem lintegral_pow_lt_top_of_split {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → ℝ≥0∞}
    (hD : AEMeasurable D P) {Y : ℝ → Ω → ℝ≥0∞} {E : ℝ → Set Ω} {β ζ M K N C₁ p : ℝ}
    (hp1 : 1 ≤ p) (hpβ : p < β) (hζ1 : ζ < 1 - p / β) (hpN : p < N)
    (hcov : CoverOnEvent P D Y E ζ) (hmom : UniformMassMoment P Y β M) (hK : 0 ≤ K)
    (hexc : ∀ C : ℝ, C₁ ≤ C → P (E C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N))) :
    ∫⁻ ω, D ω ^ p ∂P < ⊤ := by
  have hβ0 : 0 < β := by linarith
  have hq := exponent_gap hp1 hpβ hζ1
  have hC₀ : 0 < max C₁ 1 + 1 := by linarith [le_max_right C₁ 1]
  have hfin := lintegral_pow_le_of_tail hD hp1 hq hpN hC₀ hmom.1 hK
    (tail_bound_of_premises hβ0 hcov hmom hexc)
  refine lt_of_le_of_lt hfin ?_
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩, ENNReal.ofReal_lt_top⟩

/-- **Tail-to-moment, outer-expectation form** (no measurability of `D`): the same premises give
`E*[D^p] < ∞`, through the dyadic majorant `tail_moment_outer` of the staged file. -/
theorem outer_pow_lt_top_of_split {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → ℝ≥0∞}
    {Y : ℝ → Ω → ℝ≥0∞} {E : ℝ → Set Ω} {β ζ M K N C₁ p : ℝ}
    (hp1 : 1 ≤ p) (hpβ : p < β) (hζ1 : ζ < 1 - p / β) (hpN : p < N)
    (hcov : CoverOnEvent P D Y E ζ) (hmom : UniformMassMoment P Y β M) (hK : 0 ≤ K)
    (hexc : ∀ C : ℝ, C₁ ≤ C → P (E C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N))) :
    MatedCRT.outerLIntegral P (fun ω => D ω ^ p) < ⊤ := by
  have hβ0 : 0 < β := by linarith
  have hq := exponent_gap hp1 hpβ hζ1
  have hC₀ : 0 < max C₁ 1 + 1 := by linarith [le_max_right C₁ 1]
  exact tail_moment_outer P D (by linarith) hq hpN hC₀ hmom.1 hK
    (tail_bound_of_premises hβ0 hcov hmom hexc)

/-- **Outer expectation bounds the plain lower integral** (no measurability). For every `f : Ω → ℝ≥0∞`,
`∫⁻ f ∂P ≤ E*[f]`: each measurable majorant `g ≥ f` has `∫⁻ f ≤ ∫⁻ g` (`lintegral_mono`), and `E*[f]` is the infimum
of these integrals (`MatedCRT.outerLIntegral`, Defs/Notation.lean). So a finite outer expectation gives a finite plain
integral. This supplies neither measurability of `f` nor the layer-cake identity. -/
theorem lintegral_le_outerLIntegral {P : Measure Ω} (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂P ≤ MatedCRT.outerLIntegral P f := by
  unfold MatedCRT.outerLIntegral
  exact le_iInf fun g => le_iInf fun _ => le_iInf fun hfg => lintegral_mono hfg

/-- **Tail-to-moment, finiteness without measurability**. The premises of
`lintegral_pow_lt_top_of_split` without `hD : AEMeasurable D P`: `∫⁻ D^p ∂P < ∞` follows from
`outer_pow_lt_top_of_split` and `lintegral_le_outerLIntegral`. The measurability premise `hD` is needed for the layer-cake
bound `lintegral_pow_le_of_tail` and for the Tonelli identity, not for this conclusion. -/
theorem lintegral_pow_lt_top_of_outer {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → ℝ≥0∞}
    {Y : ℝ → Ω → ℝ≥0∞} {E : ℝ → Set Ω} {β ζ M K N C₁ p : ℝ}
    (hp1 : 1 ≤ p) (hpβ : p < β) (hζ1 : ζ < 1 - p / β) (hpN : p < N)
    (hcov : CoverOnEvent P D Y E ζ) (hmom : UniformMassMoment P Y β M) (hK : 0 ≤ K)
    (hexc : ∀ C : ℝ, C₁ ≤ C → P (E C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N))) :
    ∫⁻ ω, D ω ^ p ∂P < ⊤ :=
  (lintegral_le_outerLIntegral (fun ω => D ω ^ p)).trans_lt
    (outer_pow_lt_top_of_split hp1 hpβ hζ1 hpN hcov hmom hK hexc)

/-- **Lemma 4.3 (4.6) at the level `C^ζ`**. An inverse-polynomial bound for the events `A c` at every
level `c` gives `ExceptionalInversePoly` for `E C := A (C^ζ)`: with `c = C^ζ` and the exponent `N/ζ`, one has
`(C^ζ)^{-N/ζ} = C^{-N}`. The hypothesis `0 < ζ` is used only here. -/
theorem exceptional_of_eq46 {P : Measure Ω} {A : ℝ → Set Ω} {ζ : ℝ} (hζ0 : 0 < ζ)
    (h46 : ∀ N : ℝ, 0 < N → ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c → P (A c)ᶜ ≤ ENNReal.ofReal (K * c ^ (-N))) :
    ExceptionalInversePoly P (fun C => A (C ^ ζ)) := by
  intro N hN
  obtain ⟨K, C₀, hC₀, hbd⟩ := h46 (N / ζ) (div_pos hN hζ0)
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hζne : ζ ≠ 0 := hζ0.ne'
  refine ⟨max K 0, C₀ ^ (1 / ζ), le_max_right _ _, fun C hC => ?_⟩
  have hCpos : 0 < C := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hC
  have hCζ : C₀ ≤ C ^ ζ := by
    calc C₀ = (C₀ ^ (1 / ζ)) ^ ζ := by
          rw [← Real.rpow_mul hC₀0, show 1 / ζ * ζ = 1 by field_simp, Real.rpow_one]
      _ ≤ C ^ ζ := Real.rpow_le_rpow (Real.rpow_nonneg hC₀0 _) hC hζ0.le
  have key : (C ^ ζ) ^ (-(N / ζ)) = C ^ (-N) := by
    rw [← Real.rpow_mul hCpos.le]
    congr 1
    field_simp
  calc P (A (C ^ ζ))ᶜ ≤ ENNReal.ofReal (K * (C ^ ζ) ^ (-(N / ζ))) := hbd (C ^ ζ) hCζ
    _ ≤ ENNReal.ofReal (max K 0 * C ^ (-N)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← key]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (Real.rpow_nonneg hCpos.le _) _)

/-- **GMS p. 33 uniform mass β-moment** in the form `UniformMassMoment`: the printed
`sup_{C>1} E*[Y_C^β] < ∞` (`GMSMassBetaMomentStmt`) gives a real bound `M ≥ 0`. -/
theorem uniform_of_mass_beta {P : Measure Ω} {Y : ℝ → Ω → ℝ≥0∞} {β : ℝ}
    (h : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ C : ℝ, 1 < C → MatedCRT.outerLIntegral P (fun ω => Y C ω ^ β) ≤ M) :
    ∃ M : ℝ, UniformMassMoment P Y β M := by
  obtain ⟨M, hMt, hM⟩ := h
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun C hC => (hM C hC).trans ?_⟩
  exact (ENNReal.ofReal_toReal hMt.ne).symm.le

/-- **Covering on `E_C` from the printed inputs**. If `D ≤ μ_h(B̄₀)` almost surely ((4.20)), `η` is
almost surely continuous, and the coordinate change `μ_{h^{C^ζ}}(𝔻) = μ_h(B_{R_{C^ζ}}(0))` holds almost surely, then
on `E_C = {η([-1,1]) ⊂ B_{R_{C^ζ}/8}(0)}` one has `D ≤ C^ζ · Y_C` with `Y_C = C^{-ζ} μ_{h^{C^ζ}}(𝔻)`.
The inclusion `B̄₀ ⊂ B_{R_{C^ζ}}(0)` on `E_C` is `gmsB0_subset_ball`. -/
theorem cover_of_printed {P : Measure Ω} {γ ζ C : ℝ} (hC : 0 < C) {D : Ω → ℝ≥0∞}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μbC : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hX : ∀ᵐ ω ∂P, D ω ≤ μ ω (gmsB0 (η ω)))
    (hcont : ∀ᵐ ω ∂P, Continuous (η ω))
    (hcoord : ∀ᵐ ω ∂P, μbC ω (Metric.ball 0 1) =
      μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1)) :
    ∀ᵐ ω ∂P, ω ∈ {ω | η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)} →
      D ω ≤ ENNReal.ofReal (C ^ ζ) * (ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)) := by
  filter_upwards [hX, hcont, hcoord] with ω hXω hcω hcoω hE
  have hE' : η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8) := hE
  obtain ⟨hR, hsub⟩ := gmsB0_subset_ball hcω hE'
  calc D ω ≤ μ ω (gmsB0 (η ω)) := hXω
    _ ≤ μ ω (Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ))) := measure_mono hsub
    _ = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1) := by
        rw [image_mul_ball_one hR]
    _ = μbC ω (Metric.ball 0 1) := hcoω.symm
    _ = ENNReal.ofReal (C ^ ζ) * (ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _), ← Real.rpow_add hC]
        simp

end Generic

section Canonical

/-- **Canonical premises** (with the printed inputs). For a canonical zero-cone model, the printed GMS
inputs give, for the exceptional events `E_C = {η([-1,1]) ⊂ B_{R_{C^ζ}/8}(0)}` and the normalized masses
`Y_C = C^{-ζ} μ_{h^{C^ζ}}(𝔻)`: the covering `D ≤ C^ζ · Y_C` on `E_C` (from the printed (4.20), the coordinate change
and `gmsB0_subset_ball`), the uniform β-moment `M` (GMS p. 33), and the exceptional bound `K C^{-N}` (Lemma 4.3 (4.6)
read at the level `C^ζ`, for the printed range `N > 0`; here `N > p ≥ 1`, so `0 < N` is derived from `hp1` and `hpN`).
The almost sure continuity of `η` is part of `IsAreaParametrized` (`Defs/Setting.lean:125`). -/
theorem canonical_premises {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    {β ζ N p : ℝ} (hp1 : 1 ≤ p) (hpβ : p < β) (hβ2 : β < 4 / γ ^ 2) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1 - p / β) (hpN : p < N) :
    ∃ M K C₁ : ℝ,
      UniformMassMoment P (fun C ω => ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)) β M ∧
      0 ≤ K ∧
      CoverOnEvent P (fun ω => (gmsInnerDegree (η ω)).toENNReal)
        (fun C ω => ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1))
        (fun C => {ω | η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)}) ζ ∧
      ∀ C : ℝ, C₁ ≤ C → P ((fun C : ℝ => {ω | η ω '' Set.Icc (-1) 1 ⊆
        Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)}) C)ᶜ ≤ ENNReal.ofReal (K * C ^ (-N)) := by
  have hcont : ∀ᵐ ω ∂P, Continuous (η ω) := hM.isAreaParametrized.mono fun ω h => h.1
  have hβ0 : 0 < β := by linarith
  have hpos : 0 < p / β := div_pos (by linarith) hβ0
  have hζ1' : ζ < 1 := by linarith
  obtain ⟨M, hMt, hmomM⟩ :=
    hBeta γ hγ0 hγ2 Ω P hC hcirc μ η hM μb hμb ζ hζ0 hζ1' β hβ0 hβ2
  obtain ⟨M', hmom⟩ := uniform_of_mass_beta
    (Y := fun C ω => ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)) ⟨M, hMt, hmomM⟩
  have h46 : ∀ N : ℝ, 0 < N → ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c →
      P ((fun c : ℝ => {ω | η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) c / 8)}) c)ᶜ ≤
        ENNReal.ofReal (K * c ^ (-N)) :=
    fun N hN => hLem γ hγ0 hγ2 Ω P hC hcirc μ η hM N hN
  obtain ⟨K, C₁, hK, hexcK⟩ := exceptional_of_eq46 hζ0 h46 N (by linarith)
  have hcov : CoverOnEvent P (fun ω => (gmsInnerDegree (η ω)).toENNReal)
      (fun C ω => ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1))
      (fun C => {ω | η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)}) ζ := by
    intro C hC1
    have hC0 : 0 < C := by linarith
    have hcoordC := hCoord γ hγ0 hγ2 Ω P hC hcirc μ η hM μb hμb (C ^ ζ) (Real.rpow_pos_of_pos hC0 ζ)
    exact cover_of_printed (D := fun ω => (gmsInnerDegree (η ω)).toENNReal) hC0
      (hInner γ hγ0 hγ2 Ω P hC hcirc μ η hM) hcont (hcoordC.mono fun ω h => h _ measurableSet_ball)
  exact ⟨M', K, C₁, hmom, hK, hcov, hexcK⟩

/-- **Canonical inner-degree moment, layer-cake form** (with the printed inputs). Under the printed GMS
inputs and the exponent ranges `1 ≤ p < β < 4/γ²`, `0 < ζ < 1 - p/β`, `p < N`, the `p`-th moment of the canonical inner
degree is finite, given one named premise: the measurability `AEMeasurable (deg_in ∘ η) P` (the measurability residual).
The premise enters only through the layer-cake bound `lintegral_pow_le_of_tail`; the conclusion does not need it
(see `canonical_innerDegree_lintegral_lt_top_of_outer`). -/
theorem canonical_innerDegree_lintegral_lt_top {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    (hMeas : AEMeasurable (fun ω => (gmsInnerDegree (η ω)).toENNReal) P)
    {β ζ N p : ℝ} (hp1 : 1 ≤ p) (hpβ : p < β) (hβ2 : β < 4 / γ ^ 2) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1 - p / β) (hpN : p < N) :
    ∫⁻ ω, (gmsInnerDegree (η ω)).toENNReal ^ p ∂P < ⊤ := by
  have : IsProbabilityMeasure P := hM.isProbabilityMeasure
  obtain ⟨_M, K, C₁, hmom, hK, hcov, hexc⟩ :=
    canonical_premises hLem hBeta hCoord hInner hγ0 hγ2 hM μb hμb hp1 hpβ hβ2 hζ0 hζ1 hpN
  exact lintegral_pow_lt_top_of_split hMeas hp1 hpβ hζ1 hpN hcov hmom hK hexc

/-- **Canonical inner-degree moment, outer-expectation form** (no measurability): under the same printed inputs and
exponent ranges, `E*[deg_in^p] < ∞`, through `outer_pow_lt_top_of_split`. This is the inner-degree moment that
the tail-to-moment integration derives (it is not a printed (4.14) or (4.23)); it is the claim of `gms_innerDegree_moment` in the staged
file, obtained here through the generic component. -/
theorem canonical_innerDegree_outer_lt_top {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    {β ζ N p : ℝ} (hp1 : 1 ≤ p) (hpβ : p < β) (hβ2 : β < 4 / γ ^ 2) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1 - p / β) (hpN : p < N) :
    MatedCRT.outerLIntegral P (fun ω => (gmsInnerDegree (η ω)).toENNReal ^ p) < ⊤ := by
  have : IsProbabilityMeasure P := hM.isProbabilityMeasure
  obtain ⟨_M, K, C₁, hmom, hK, hcov, hexc⟩ :=
    canonical_premises hLem hBeta hCoord hInner hγ0 hγ2 hM μb hμb hp1 hpβ hβ2 hζ0 hζ1 hpN
  exact outer_pow_lt_top_of_split hp1 hpβ hζ1 hpN hcov hmom hK hexc

/-- **Canonical inner-degree moment, plain finiteness without measurability**. The conclusion of
`canonical_innerDegree_lintegral_lt_top` without its premise `AEMeasurable (deg_in ∘ η) P`, through
`lintegral_le_outerLIntegral` and `canonical_innerDegree_outer_lt_top`. -/
theorem canonical_innerDegree_lintegral_lt_top_of_outer {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    {β ζ N p : ℝ} (hp1 : 1 ≤ p) (hpβ : p < β) (hβ2 : β < 4 / γ ^ 2) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1 - p / β) (hpN : p < N) :
    ∫⁻ ω, (gmsInnerDegree (η ω)).toENNReal ^ p ∂P < ⊤ :=
  (lintegral_le_outerLIntegral (fun ω => (gmsInnerDegree (η ω)).toENNReal ^ p)).trans_lt
    (canonical_innerDegree_outer_lt_top hLem hBeta hCoord hInner hγ0 hγ2 hM μb hμb hp1 hpβ hβ2 hζ0 hζ1 hpN)

end Canonical

end MatedCRT.StoppedInnerDegreeMoments

namespace MatedCRT.StoppedCanonicalMoments

open MatedCRT

/-- **Inner-degree moment from the published inputs**. For the canonical zero-cone model, given the
staged Lemma 4.3 (4.6), the beta-moment paragraph, the coordinate change (2.3) and the inner-degree bound (4.20), the
outer `p`-th moment of `deg_in(H₀)` is finite for `1 ≤ p < 4/γ²`. The printed (4.22) range `[1, 4/γ)^2` is not used;
the conclusion is the range the written proof derives.

Assumptions, exactly as used: `hLem`, `hBeta`, `hCoord` and `hInner` are the staged printed Props (cited, not proved);
`hM` is the canonical zero-cone predicate; `hμb` supplies the rescaled-measure family `μb`: for every `b > 0`, `μb b` is
the `γ`-LQG measure of the rescaled circle averages `gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)`,
and it is the family on which `hBeta` and `hCoord` are stated. The conclusion is an outer moment; measurability of
`deg_in(H₀)` is neither assumed nor proved. -/
theorem gms_innerDegree_moment {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 4 / γ ^ 2) :
    MatedCRT.outerLIntegral P (fun ω => (gmsInnerDegree (η ω)).toENNReal ^ p) < ⊤ := by
  -- Corollary of `canonical_innerDegree_outer_lt_top`: the exponents are `β = (p + 4/γ²)/2`, `ζ = (1 - p/β)/2`
  -- and `N = p + 1`; `p < β < 4/γ²` and `0 < ζ < 1 - p/β` follow from `1 ≤ p < 4/γ²`.
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (p + 4 / γ ^ 2) / 2 := ⟨_, rfl⟩
  have hpβ : p < β := by rw [hβdef]; linarith
  have hβ2 : β < 4 / γ ^ 2 := by rw [hβdef]; linarith
  have hβ0 : 0 < β := by linarith
  have hpb : p / β < 1 := (div_lt_one hβ0).mpr hpβ
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = (1 - p / β) / 2 := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by rw [hζdef]; linarith
  have hζ1 : ζ < 1 - p / β := by rw [hζdef]; linarith
  exact MatedCRT.StoppedInnerDegreeMoments.canonical_innerDegree_outer_lt_top hLem hBeta hCoord hInner hγ0 hγ2 hM
    μb hμb hp1 hpβ hβ2 hζ0 hζ1 (show p < p + 1 by linarith)

end MatedCRT.StoppedCanonicalMoments
