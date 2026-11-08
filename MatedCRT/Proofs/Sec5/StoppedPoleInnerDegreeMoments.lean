import Mathlib
import MatedCRT.Proposed.StoppedPoleCanonicalMoments2026

/-!
# Inner-degree tail and moment component (steps2-r3, r3:2674-2753)

Internal component of the moment proof for the inner degree `D = deg_in(H₀)` of GMS arXiv:1705.11161v5,
Definition 4.5 (pp. 32-33). It formalizes the written Chebyshev split and tail-to-moment integration of
`steps2-r3.tex` lines 2690-2753 on a probability space, for `ℝ≥0∞`-valued `D` and normalized masses `Y_C`.
No independence between the exceptional events `E_C` and the masses `Y_C` is used.

Proved here (no tail bound and no moment bound is assumed):
* `chebyshev_split`: `P(D > C) ≤ P(E_C^c) + C^{-β(1-ζ)} · E*[Y_C^β]` when `D ≤ C^ζ · Y_C` on `E_C` almost surely;
* `tail_le_of_split`: with a uniform β-moment `M` and an exceptional bound `K C^{-N}`,
  `P(D > C) ≤ M C^{-β(1-ζ)} + K C^{-N}` at one level `C`;
* `lintegral_pow_le_of_tail`: tail-to-moment by the layer-cake formula (Mathlib
  `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul`) with `q = β(1-ζ) > p` and `N > p`:
  `E[D^p] ≤ C₀^p + p M C₀^{p-q}/(q-p) + p K C₀^{p-N}/(N-p)`. This needs `AEMeasurable D P`
  (the WPN-51 residual), used only for the Tonelli identity;
* `outer_pow_lt_top_of_split`: the same finiteness for the outer expectation `E*[D^p]`, with no measurability
  (through `tail_moment_outer` of the staged file);
* `lintegral_pow_lt_top_of_split`: the combined finiteness from the named premises below;
* `exceptional_of_eq46`, `uniform_of_mass_beta`, `cover_of_printed`: the consumers of the printed GMS inputs
  (Lemma 4.3 (4.6) read at the level `C^ζ`, the mass-β moment of GMS p. 33, the coordinate change (4.3) and the
  inner-degree bound (4.20));
* `canonical_premises`, `canonical_innerDegree_lintegral_lt_top`, `canonical_innerDegree_outer_lt_top`: the canonical
  zero-cone model. Continuity of `η` comes from `IsAreaParametrized`; the layer-cake form has the single premise
  `AEMeasurable (deg_in ∘ η) P` (WPN-51), the outer form has none.

Named premises, hypothesis shapes and not literature Props: `CoverOnEvent`, `UniformMassMoment`,
`ExceptionalInversePoly`. The printed inputs are the Props of `StoppedPoleCanonicalMoments2026.lean`
(read-only here). The malformed printed range (4.22) and the sign of the last bound in (4.25) are not used.
Exponent ranges (r3:2674-2690): `1 ≤ p`, `p < β < 4/γ²`, `ζ < 1 - p/β` (so `q = β(1-ζ) > p`), `N > p`.
The generic component uses no sign of `ζ`; `0 < ζ` enters only through the reparametrization `N ↦ N/ζ` of
Lemma 4.3 (4.6) and the printed mass-β range `0 < ζ < 1`.
-/

open MeasureTheory Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section

namespace MatedCRT.StoppedInnerDegreeMoments

open MatedCRT.StoppedCanonicalMoments

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Named covering premise (r3:2690-2741): for every level `C > 1`, almost surely, on the event `E C`,
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

/-- **Chebyshev split** (r3:2733-2741). With outer integrals, so no measurability of `D`, `Y` or `E` is needed,
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

/-- **Single-level tail bound** (r3:2741-2742): with the uniform β-moment `M` and the exceptional bound
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

/-- **Tail-to-moment by the layer-cake formula** (r3:2741-2753). If `P(D > C) ≤ M C^{-q} + K C^{-N}` for all
`C ≥ C₀`, with `p < q` and `p < N`, then `E[D^p] ≤ C₀^p + p M C₀^{p-q}/(q-p) + p K C₀^{p-N}/(N-p)`.
The premise `hD : AEMeasurable D P` is used only for the Tonelli identity (the WPN-51 residual). -/
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

/-- The exponent gap of r3:2674-2690: `ζ < 1 - p/β` gives `q = β(1-ζ) > p`. -/
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

/-- **Tail-to-moment, layer-cake form** (r3:2741-2753, with the premises named). From the covering on the events
`E_C`, the uniform β-moment `M`, and the inverse-polynomial exceptional bound `K C^{-N}`, with the exponent ranges
`1 ≤ p`, `p < β`, `ζ < 1 - p/β` and `p < N`, the `p`-th moment of `D` is finite. The only measurability premise is
`hD : AEMeasurable D P` (the WPN-51 residual). No independence of `E_C` and `Y_C` is used. -/
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

/-- **Lemma 4.3 (4.6) at the level `C^ζ`** (r3:2708-2716). An inverse-polynomial bound for the events `A c` at every
level `c` gives `ExceptionalInversePoly` for `E C := A (C^ζ)`: with `c = C^ζ` and the exponent `N/ζ`, one has
`(C^ζ)^{-N/ζ} = C^{-N}`. The hypothesis `0 < ζ` is used only here. -/
theorem exceptional_of_eq46 {P : Measure Ω} {A : ℝ → Set Ω} {ζ : ℝ} (hζ0 : 0 < ζ)
    (h46 : ∀ N : ℝ, ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c → P (A c)ᶜ ≤ ENNReal.ofReal (K * c ^ (-N))) :
    ExceptionalInversePoly P (fun C => A (C ^ ζ)) := by
  intro N _hN
  obtain ⟨K, C₀, hC₀, hbd⟩ := h46 (N / ζ)
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

/-- **Covering on `E_C` from the printed inputs** (r3:2690-2741). If `D ≤ μ_h(B̄₀)` almost surely ((4.20)), `η` is
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

/-- **Canonical premises** (r3:2690-2741 with the printed inputs). For a canonical zero-cone model, the printed GMS
inputs give, for the exceptional events `E_C = {η([-1,1]) ⊂ B_{R_{C^ζ}/8}(0)}` and the normalized masses
`Y_C = C^{-ζ} μ_{h^{C^ζ}}(𝔻)`: the covering `D ≤ C^ζ · Y_C` on `E_C` (from the printed (4.20), the coordinate change
and `gmsB0_subset_ball`), the uniform β-moment `M` (GMS p. 33), and the exceptional bound `K C^{-N}` (Lemma 4.3 (4.6)
read at the level `C^ζ`). The almost sure continuity of `η` is part of `IsAreaParametrized` (`Defs/Setting.lean:125`). -/
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
  have h46 : ∀ N : ℝ, ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c →
      P ((fun c : ℝ => {ω | η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) c / 8)}) c)ᶜ ≤
        ENNReal.ofReal (K * c ^ (-N)) :=
    fun N => hLem γ hγ0 hγ2 Ω P hC hcirc μ η hM N
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

/-- **Canonical inner-degree moment, layer-cake form** (r3:2741-2753 with the printed inputs). Under the printed GMS
inputs and the exponent ranges `1 ≤ p < β < 4/γ²`, `0 < ζ < 1 - p/β`, `p < N`, the `p`-th moment of the canonical inner
degree is finite, given one named premise: the measurability `AEMeasurable (deg_in ∘ η) P` (the WPN-51 residual),
used only for the Tonelli identity. -/
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
r3:2741-2753 derives (it is not a printed (4.14) or (4.23)); it is the claim of `gms_innerDegree_moment` in the staged
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

end Canonical

end MatedCRT.StoppedInnerDegreeMoments
