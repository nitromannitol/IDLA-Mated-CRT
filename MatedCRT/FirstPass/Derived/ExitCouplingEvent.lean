import MatedCRT.FirstPass.Derived.ExitCouplingParams
import MatedCRT.FirstPass.Derived.ExitCouplingNumerics
import MatedCRT.FirstPass.Derived.ExitCouplingEventInputs
import MatedCRT.FirstPass.Derived.CellDiameterEvent
import MatedCRT.FirstPass.Derived.HittingVertexTV
import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Proposition 6.12 of Berestycki-Gwynne: the event-level union

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.12.  The deterministic good-environment theorem with the scales of
the proof (`ExitCouplingParams.stoppedWalk_le_of_numerics`) needs five estimates in one environment: the cell
diameters, the total variation bound for the first exit vertex, Lemma 2.19, Lemma 6.11 and (6.36).  Each of
their failure events is negligible as `ε → 0` and then `δ → 0` (`LimLimSmall`), so is the union of the five.
Away from a null set the environment is regular (continuous, transient, locally finite, adjacent vertices have
intersecting cells, consecutive vertices adjacent), and for small `δ` and `ε ≤ δ^(a χ)/6` the failure of the
conclusion forces one of the five failure events.  This gives

* `LimLimSmall.mono_of_small_ae`: negligibility passes to a failure event contained, almost surely and for
  small `δ` and `ε`, in a negligible one;
* `ae_regular`: the almost sure regularity of a valid environment;
* `limLimSmall_levyProkhorovEDist_stoppedWalk`: for every `r > 0` the event that two walks started in
  `V^ε(B_δ(z))`, `z ∈ B_ρ`, stopped at the exit of the interior vertices of `B_{ρ₀}`, have laws at
  Lévy-Prokhorov distance `> r`, is negligible as `ε → 0` and then `δ → 0`.

The estimate (6.36) (Lemma 6.10) enters as an explicit hypothesis in event form.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric Filter LatticeProb LatticeProb.Gauss
open scoped ENNReal NNReal Topology
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue MatedCRT.ExitCouplingNoShortTravel MatedCRT.ExitCouplingMarkov
  MatedCRT.ExitCouplingHq
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace LimLimSmall

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F G : ℝ → ℝ → Set Ω}

/-- A failure event that is, almost surely and for all small `δ` and then all small `ε`, contained in a
negligible failure event, is negligible. -/
theorem mono_of_small_ae (hG : LimLimSmall P G)
    (h : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ᵐ ω ∂P, ω ∈ F δ ε → ω ∈ G δ ε) : LimLimSmall P F := by
  obtain ⟨δ₁, hδ₁, h⟩ := h
  intro θ hθ
  obtain ⟨δ₂, hδ₂, h2⟩ := hG θ hθ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδlt => ?_⟩
  obtain ⟨ε₁, hε₁, h1'⟩ := h δ hδ (lt_of_lt_of_le hδlt (min_le_left _ _))
  obtain ⟨ε₂, hε₂, h2'⟩ := h2 δ hδ (lt_of_lt_of_le hδlt (min_le_right _ _))
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεlt => ?_⟩
  have hle : F δ ε ≤ᵐ[P] G δ ε :=
    (h1' ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))).mono fun _ hω => hω
  exact (measure_mono_ae hle).trans (h2' ε hε (lt_of_lt_of_le hεlt (min_le_right _ _)))

end LimLimSmall

namespace ExitCouplingEvent

/-- **Almost sure regularity of a valid environment.**  Almost surely the curve is continuous and transient,
the mated-CRT maps `𝒢^ε` are locally finite for every `ε > 0`, adjacent vertices have intersecting cells, and
consecutive vertices are adjacent. -/
theorem ae_regular {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω k j ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      (∀ ε : ℝ, 0 < ε → ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    ae_isLocallyFiniteMult_of_isValid hS, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS]
    with ω hη hp hlf hadj
  refine ⟨hη, hp, hlf, fun ε hε j k hjk => ?_, fun ε hε k => S.mult_succ_ne_zero hε.le ω k⟩
  rw [inter_comm]
  exact hadj ε hε k j hjk

/-- **Proposition 6.12 of Berestycki-Gwynne at the event level.**  Fix `0 < ρ < ρ₀ < ρ₁ < 1` and `r > 0`.  Given
the cell size estimate, the corrected discrete Hölder estimate, the Green kernel lower bound, the exit time
upper bound, the expected exit time bound of Lemma 2.19, the estimate (6.32) of Lemma 6.9 and the estimate
(6.36) of Lemma 6.10 (in event form), for every valid environment the event that for some `z ∈ B_ρ` and
`x, y ∈ V^ε(B_δ(z))` the laws of the walks from `x` and from `y` stopped at the exit of the interior vertices
of `B_{ρ₀}` are at Lévy-Prokhorov distance `> r` is negligible as `ε → 0` and then `δ → 0`. -/
theorem limLimSmall_levyProkhorovEDist_stoppedWalk {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ρ ρ0 ρ1 : ℝ} (hρ : 0 < ρ) (hρρ0 : ρ < ρ0) (hρ0ρ1 : ρ0 < ρ1) (hρ1 : ρ1 < 1)
    (h632 : ∀ ℓ : ℝ, 1 < ℓ → ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ1 - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ)
    (h636 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun s ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X ≤
              succExit (fun w => interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) (2 * s)))
                ⌊(2 * s) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * s))}))
    {r : ℝ} (hr : 0 < r) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    LimLimSmall S.P (fun δ ε => {ω | ∃ z ∈ ball (0 : ℂ) ρ, ∃ x ∈ cellVertices ε (S.η ω) (ball z δ),
      ∃ y ∈ cellVertices ε (S.η ω) (ball z δ),
      ENNReal.ofReal r < levyProkhorovEDist
        ((srwLaw (S.mult ε ω) x).map
          (stoppedInterp (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal
            (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))))
        ((srwLaw (S.mult ε ω) y).map
          (stoppedInterp (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal
            (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))))}) := by
  have hρ1pos : 0 < ρ1 := by linarith
  -- exponents
  obtain ⟨q, hq, h219'⟩ := ExitCouplingEventInputs.limLimSmall_expectedExitTime h219 hγ hγ2
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ, χ = 2 * (2 + γ) / (2 - γ) + 1 := ⟨_, rfl⟩
  have hχ : 2 * (2 + γ) / (2 - γ) < χ := by rw [hχdef]; linarith
  have hχpos : 0 < χ := by
    have : 0 < 2 * (2 + γ) / (2 - γ) := div_pos (by linarith) (by linarith)
    rw [hχdef]; linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min (1 / 4) (q / (4 * χ)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; exact lt_min (by norm_num) (by positivity)
  have ha4 : a ≤ 1 / 4 := by rw [hadef]; exact min_le_left _ _
  have haχ : a * χ ≤ q / 4 := by
    have h1 : a ≤ q / (4 * χ) := by rw [hadef]; exact min_le_right _ _
    calc a * χ ≤ q / (4 * χ) * χ := mul_le_mul_of_nonneg_right h1 hχpos.le
      _ = q / 4 := by field_simp
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = q / 2 - a * χ := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; linarith
  -- the estimates of the proof
  obtain ⟨ψ, hψ, h611⟩ := ExitCouplingEventInputs.limLimSmall_exitTimeLower_611 h213 h214 hγ hγ2 hχ
    hρ1pos hρ1 h632
  obtain ⟨ψ₀, hψ₀, h636'⟩ := h636
  obtain ⟨ξ, A, hξ, hA, hTV⟩ := HittingVertexTV.hittingVertex_tv_le 𝒮 h28 h32 γ hγ hγ2 ρ hρ (by linarith)
  obtain ⟨T₀, δ₁, hδ₁, hnum⟩ := ExitCouplingNumerics.exists_small_parameters (A := A) ha0 ha4 he0 hξ
    hψ₀.2 hψ.2.2 (fun x hx => hψ.1 x hx.le) (κ := ρ1 - ρ0) (r := r) (by linarith) hr
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Real.continuous_sqrt.tendsto (0 : ℝ)
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨η', hae⟩ : ∃ η' : Ω → C(ℝ, ℂ), ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := by
    classical
    refine ⟨fun ω => if h : Continuous (S.η ω) then ⟨S.η ω, h⟩ else ⟨fun _ => 0, continuous_const⟩, ?_⟩
    filter_upwards [TraceInputs68.ae_continuous_eta hS] with ω hω
    simp [hω]
  have h1 := CellDiameterEvent.limLimSmall_cellDiam hS hae ρ1
    (d := fun δ => Real.sqrt δ / 4) (fun δ hδ => by positivity)
  have h2 := LimLimSmall.of_polyHighProb (P := S.P)
    (E := fun δ ε => {ω | ∀ z ∈ ball (0 : ℂ) ρ,
        ∀ x ∈ cellVertices ε (S.η ω) (ball z δ), ∀ y ∈ cellVertices ε (S.η ω) (ball z δ),
          ∀ T : Set ℤ,
          |(srwLaw (S.mult ε ω) x).real
              {X | vExitPosition (interiorCellVertices ε (S.η ω) (ball z (Real.sqrt δ))) X ∈ T} -
            (srwLaw (S.mult ε ω) y).real
              {X | vExitPosition (interiorCellVertices ε (S.η ω) (ball z (Real.sqrt δ))) X ∈ T}| ≤
            A * δ ^ ξ})
    (fun δ hδ hδ1 => hTV δ hδ hδ1 Ω S hS)
  have h3 := (h219' ρ0 (by linarith) (by linarith) Ω S hS).comp_delta (φ := Real.sqrt)
    (fun δ hδ => Real.sqrt_pos.2 hδ) hsqrt
  have h4 := (h611 Ω S hS).comp_delta (φ := fun δ : ℝ => δ ^ a)
    (fun δ hδ => Real.rpow_pos_of_pos hδ a) (ExitCouplingNumerics.tendsto_rpow_zero ha0)
  have h5 := (h636' Ω S hS).comp_delta (φ := fun δ : ℝ => δ ^ a)
    (fun δ hδ => Real.rpow_pos_of_pos hδ a) (ExitCouplingNumerics.tendsto_rpow_zero ha0)
  have hG := ((((h1.union h2).union h3).union h4).union h5)
  have hreg := ae_regular hγ hγ2 hS
  refine LimLimSmall.mono_of_small_ae hG ⟨min δ₁ ((ρ0 - ρ) ^ 2), lt_min hδ₁ (by nlinarith),
    fun δ hδ hδlt => ⟨δ ^ (a * χ) / 6, by positivity, fun ε hε hεlt => ?_⟩⟩
  filter_upwards [hreg, hae] with ω hω hηω hfail
  obtain ⟨hη, hp, hlf, hadj, hcons⟩ := hω
  by_contra hGω
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hGω
  obtain ⟨⟨⟨⟨hd1, hd2⟩, hd3⟩, hd4⟩, hd5⟩ := hGω
  rw [hηω] at hd1
  obtain ⟨hδ41, hδaκ, hd, hr0, hT0, hfin⟩ := hnum δ hδ (lt_of_lt_of_le hδlt (min_le_left _ _))
  have hδsq : δ < (ρ0 - ρ) ^ 2 := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hρ0' : ρ + Real.sqrt δ ≤ ρ0 := by
    have : Real.sqrt δ ≤ ρ0 - ρ := Real.sqrt_le_iff.2 ⟨by linarith, hδsq.le⟩
    linarith
  obtain ⟨z, hz, x, hx, y, hy, hlt⟩ := hfail
  have hle := ExitCouplingParams.stoppedWalk_le_of_numerics (mult := S.mult ε ω) (ε := ε)
    (η := S.η ω) hε hη hp (hlf ε hε) (hcons ε hε) (fun j k hkj => hadj ε hε j k hkj) hδ
    (by linarith) hedef hρ0' (by linarith) hd hr0 hA.le (hψ.1 _ (Real.rpow_nonneg hδ.le a))
    (hψ₀.1 _ (by positivity)) hT0 hfin hεlt.le hd1 hd2 hd3 hd4 hd5 z hz x hx y hy
  exact absurd hlt (not_lt.2 hle)

end ExitCouplingEvent
end MatedCRT

#print axioms MatedCRT.LimLimSmall.mono_of_small_ae
#print axioms MatedCRT.ExitCouplingEvent.ae_regular
#print axioms MatedCRT.ExitCouplingEvent.limLimSmall_levyProkhorovEDist_stoppedWalk
