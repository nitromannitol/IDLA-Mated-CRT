import MatedCRT.FirstPass.Derived.ExitCouplingEvent
import MatedCRT.FirstPass.Derived.ExitCouplingGoodEnv
import MatedCRT.FirstPass.Derived.StoppedWalkOscillation

/-!
# Oscillation of the stopped interpolated walk: the event-level union

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Proposition 6.5 (equicontinuity of the stopped paths), at the event level.

* `srwLaw_stoppedOscillation_le_of_goodEnv`: in one fixed environment, if the cells near `B_{ρ1}` have
  diameter at most `d < δ'`, adjacent vertices have intersecting cells, the walk leaves `B_{ρ0}` within `K`
  successive exits from the balls `B_{2 δ'}` outside probability `ψ₀` (the bound (6.36)) and leaves the vertices of
  every ball `B_{δ'}(η(x))` after time `T ≥ g` with probability at least `1 - ψ` (Lemma 6.11), then for every
  starting vertex in `V^ε(B_{ρ0})` the interpolated walk of speed `m` has oscillation more than `6 δ' + 2 d`
  over a window of length `ρt` before its exit time from the interior vertices of `B_{ρ0}` with probability at
  most `ψ₀ + K ψ`, when `m ρt + 2 ≤ g`;
* `limLimSmall_stoppedOscillation`: for every `r, θ > 0`, with the exponent `χ` of Lemma 6.11, the event that
  some walk from `V^ε(B_{ρ0})` has oscillation more than `r` over a window of length `s^χ / 2` before the exit
  time from the interior vertices of `B_{ρ0}` with probability more than `θ` is negligible as `ε → 0` and then
  `s → 0`.

The estimates (6.32) (Lemma 6.9) and (6.36) (Lemma 6.10, in event form) enter as explicit hypotheses.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue MatedCRT.ExitCouplingNoShortTravel MatedCRT.ExitCouplingMarkov
  MatedCRT.ExitCouplingHq MatedCRT.ExitCouplingEvents MatedCRT.ExitCouplingOscillation
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry

namespace ExitCouplingPathEvent

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **Oscillation of the stopped walk in a good environment (Proposition 6.5, quenched, from the standard
estimates).**  All hypotheses are deterministic statements about one environment. -/
theorem srwLaw_stoppedOscillation_le_of_goodEnv {mult : ℤ → ℤ → ℕ} (hε : 0 < ε)
    (hη : Continuous η) (hadj : ∀ j k, mult k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ0 ρ1 δ' d : ℝ} (hδ' : 0 < δ') (hd0 : 0 ≤ d) (hd : d < δ') (hρ1 : ρ0 + δ' ≤ ρ1)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ1).Nonempty → ∀ x ∈ cell ε η k,
      ∀ y ∈ cell ε η k, dist x y ≤ d)
    {m : ℝ≥0} (hm : 0 < m) (ρt : ℝ≥0) {g K : ℕ} (hg : (m : ℝ) * ρt + 2 ≤ g) {T ψ : ℝ}
    (hgT : (g : ℝ) ≤ T) {R₁ : ℝ} (hR₁ : ρ0 ≤ R₁)
    (h611 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) R₁),
      srwLaw mult x {X | (vExitTime (cellVertices ε η (ball (vertexPoint ε η x) δ')) X : ℝ≥0∞) <
        ENNReal.ofReal T} ≤ ENNReal.ofReal ψ)
    {ψ₀ : ℝ≥0∞}
    (h0 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult x {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
        succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) (2 * δ'))) K X} ≤ ψ₀) :
    ∀ x ∈ cellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult x {X | ∃ a b : ℝ≥0,
        a ≤ ((vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) / m ∧
        b ≤ ((vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) / m ∧
        dist a b ≤ ρt ∧ 3 * (2 * δ') + 2 * d < dist (interpPathFn (vertexPoint ε η) m X a)
          (interpPathFn (vertexPoint ε η) m X b)} ≤ ψ₀ + (K : ℝ≥0∞) * ENNReal.ofReal ψ := by
  intro x hx
  have hρ01 : ρ0 ≤ ρ1 := by linarith
  have hJ : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0), ∀ w' : ℤ, mult w w' ≠ 0 →
      dist (vertexPoint ε η w) (vertexPoint ε η w') ≤ 2 * d := by
    intro w hw w' hww'
    obtain ⟨p, hp', hp⟩ := hadj w' w hww'
    have hpb : p ∈ ball (0 : ℂ) ρ1 := by
      have := cell_subset_interior_of_mem_interiorCellVertices hη hw hp
      rw [isOpen_ball.interior_eq] at this
      exact ball_subset_ball hρ01 this
    have h1 := hdiam w ⟨p, hp, hpb⟩ _ (Lemma68C12Geom.vertexPoint_mem_cell hε.le w) p hp
    have h2 := hdiam w' ⟨p, hp', hpb⟩ _ (Lemma68C12Geom.vertexPoint_mem_cell hε.le w') p hp'
    calc dist (vertexPoint ε η w) (vertexPoint ε η w')
        ≤ dist (vertexPoint ε η w) p + dist p (vertexPoint ε η w') := dist_triangle _ _ _
      _ ≤ d + d := by rw [dist_comm p]; exact add_le_add h1 h2
      _ = 2 * d := by ring
  have hq := srwLaw_exitInterior_lt_le_of_exitTimeLower mult hε.le hη hδ' hd hdiam hρ1 hR₁ hgT h611
  exact srwLaw_stoppedOscillation_le (ρ0 := ρ0) (s := 2 * δ') (J := 2 * d) hε.le hη
    (by positivity) (by positivity) hm ρt hg x hJ (h0 x hx) hq

/-- Failure probabilities of the shape `ψ₀(2 s) + ⌊(2 s)⁻³⌋ ψ(s)` become small as `s → 0`: there is `s₀ > 0`
such that they are at most `θ` for all `0 < s < s₀`. -/
theorem exists_small_psi {ψ ψ₀ : ℝ → ℝ}
    (hψ₀ : ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hψ : ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hψ₀nn : ∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) (hψnn : ∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ENNReal.ofReal (ψ₀ (2 * s)) + ((⌊(2 * s) ^ (-3 : ℝ)⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ψ s) ≤
        ENNReal.ofReal θ := by
  have h2 : Tendsto (fun s : ℝ => 2 * s) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun s hs => ?_⟩
    · exact ((continuous_const.mul continuous_id : Continuous fun s : ℝ => 2 * s).tendsto' 0 0
        (by simp)).mono_left nhdsWithin_le_nhds
    · have hs' : (0 : ℝ) < s := hs
      exact mul_pos two_pos hs'
  have hA : Tendsto (fun s : ℝ => ψ₀ (2 * s)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (ExitCouplingNumerics.tendsto_of_superpoly hψ₀).comp h2
  have hB := hψ 3 (by norm_num)
  have hC := hA.add hB
  rw [add_zero] at hC
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ₀ (2 * s) + s ^ (-(3 : ℝ)) * ψ s < θ :=
    hC.eventually (gt_mem_nhds hθ)
  obtain ⟨s₀, hs₀, h⟩ := ExitCouplingNumerics.exists_delta0_of_eventually hev
  refine ⟨s₀, hs₀, fun s hs hslt => ?_⟩
  have hK : ((⌊(2 * s) ^ (-3 : ℝ)⌋₊ : ℕ) : ℝ) ≤ s ^ (-(3 : ℝ)) := by
    refine (Nat.floor_le (Real.rpow_nonneg (by positivity) _)).trans ?_
    exact Real.rpow_le_rpow_of_nonpos hs (by linarith) (by norm_num)
  have h1 := h s hs hslt
  have hψs := hψnn s hs.le
  have hψ0s := hψ₀nn (2 * s) (by positivity)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add hψ0s (mul_nonneg (Nat.cast_nonneg _) hψs)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_right hK hψs
  linarith

/-- **Proposition 6.5 of Berestycki-Gwynne at the event level.**  Fix `0 < ρ₀ < ρ₁ < 1`.  Given the Green
kernel lower bound, the exit time upper bound, the estimate (6.32) of Lemma 6.9 and the estimate (6.36) of
Lemma 6.10 (in event form), there is an exponent `χ > 0` such that for every `r, θ > 0` and every valid
environment the event that for some `x ∈ V^ε(B_{ρ₀})` the interpolated walk of speed `ε⁻¹` from `x` has
oscillation more than `r` over a window of length `s^χ / 2` before its exit time from the interior vertices of
`B_{ρ₀}` with probability more than `θ` is negligible as `ε → 0` and then `s → 0`. -/
theorem limLimSmall_stoppedOscillation {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ρ0 ρ1 : ℝ} (hρ0 : 0 < ρ0) (hρ0ρ1 : ρ0 < ρ1) (hρ1 : ρ1 < 1)
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
                ⌊(2 * s) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * s))})) :
    ∃ χ : ℝ, 0 < χ ∧ ∀ {r θ : ℝ}, 0 < r → 0 < θ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      LimLimSmall S.P (fun s ε => {ω | ∃ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0),
        ENNReal.ofReal θ < srwLaw (S.mult ε ω) x {X | ∃ a b : ℝ≥0,
          a ≤ ((vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) /
            (ε⁻¹).toNNReal ∧
          b ≤ ((vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) /
            (ε⁻¹).toNNReal ∧
          dist a b ≤ (s ^ χ / 2).toNNReal ∧
          r < dist (interpPathFn (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal X a)
            (interpPathFn (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal X b)}}) := by
  have hρ1pos : 0 < ρ1 := by linarith
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ, χ = 2 * (2 + γ) / (2 - γ) + 1 := ⟨_, rfl⟩
  have hχ : 2 * (2 + γ) / (2 - γ) < χ := by rw [hχdef]; linarith
  have hχpos : 0 < χ := by
    have : 0 < 2 * (2 + γ) / (2 - γ) := div_pos (by linarith) (by linarith)
    rw [hχdef]; linarith
  refine ⟨χ, hχpos, fun {r θ} hr hθ Ω _ S hS => ?_⟩
  obtain ⟨ψ, hψ, h611⟩ := ExitCouplingEventInputs.limLimSmall_exitTimeLower_611 h213 h214 hγ hγ2 hχ
    hρ1pos hρ1 h632
  obtain ⟨ψ₀, hψ₀, h636'⟩ := h636
  obtain ⟨s₁, hs₁, hsmall⟩ := exists_small_psi hψ₀.2 hψ.2.2 hψ₀.1 hψ.1 hθ
  obtain ⟨η', hae⟩ : ∃ η' : Ω → C(ℝ, ℂ), ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := by
    classical
    refine ⟨fun ω => if h : Continuous (S.η ω) then ⟨S.η ω, h⟩ else ⟨fun _ => 0, continuous_const⟩, ?_⟩
    filter_upwards [TraceInputs68.ae_continuous_eta hS] with ω hω
    simp [hω]
  have h1 := CellDiameterEvent.limLimSmall_cellDiam hS hae ρ1
    (d := fun s => s / 2) (fun s hs => by positivity)
  have hG := (h1.union (h611 Ω S hS)).union (h636' Ω S hS)
  have hreg := ExitCouplingEvent.ae_regular hγ hγ2 hS
  have hρ10 : 0 < ρ1 - ρ0 := by linarith
  refine LimLimSmall.mono_of_small_ae hG ⟨min (min s₁ (ρ1 - ρ0)) (min 1 (r / 7)), lt_min (lt_min hs₁ hρ10)
    (lt_min one_pos (by positivity)), fun s hs hslt => ⟨s ^ χ / 6, by positivity, fun ε hε hεlt => ?_⟩⟩
  filter_upwards [hreg, hae] with ω hω hηω hfail
  obtain ⟨hη, hp, hlf, hadj, hcons⟩ := hω
  by_contra hGω
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hGω
  obtain ⟨⟨hd1, hd4⟩, hd5⟩ := hGω
  rw [hηω] at hd1
  obtain ⟨x, hx, hlt⟩ := hfail
  have hss1 : s < s₁ := lt_of_lt_of_le hslt ((min_le_left _ _).trans (min_le_left _ _))
  have hssρ : s < ρ1 - ρ0 := lt_of_lt_of_le hslt ((min_le_left _ _).trans (min_le_right _ _))
  have hss7 : s < r / 7 := lt_of_lt_of_le hslt ((min_le_right _ _).trans (min_le_right _ _))
  have hsχ : 0 < s ^ χ := Real.rpow_pos_of_pos hs χ
  have hm : (0 : ℝ≥0) < (ε⁻¹).toNNReal := Real.toNNReal_pos.2 (inv_pos.2 hε)
  have hmc : (((ε⁻¹).toNNReal : ℝ≥0) : ℝ) = ε⁻¹ := Real.coe_toNNReal _ (inv_pos.2 hε).le
  have hρc : (((s ^ χ / 2).toNNReal : ℝ≥0) : ℝ) = s ^ χ / 2 := Real.coe_toNNReal _ (by positivity)
  have h6 : 6 ≤ ε⁻¹ * s ^ χ := by
    rw [inv_mul_eq_div, le_div_iff₀ hε]; linarith
  have hge : (((ε⁻¹).toNNReal : ℝ≥0) : ℝ) * (((s ^ χ / 2).toNNReal : ℝ≥0) : ℝ) = ε⁻¹ * s ^ χ / 2 := by
    rw [hmc, hρc]; ring
  have hgT : ((⌈(((ε⁻¹).toNNReal : ℝ≥0) : ℝ) * (((s ^ χ / 2).toNNReal : ℝ≥0) : ℝ) + 2⌉₊ : ℕ) : ℝ) ≤
      ε⁻¹ * s ^ χ := by
    have h := Nat.ceil_lt_add_one (a := (((ε⁻¹).toNNReal : ℝ≥0) : ℝ) *
      (((s ^ χ / 2).toNNReal : ℝ≥0) : ℝ) + 2) (by positivity)
    rw [hge] at h ⊢
    linarith
  have hle := srwLaw_stoppedOscillation_le_of_goodEnv (mult := S.mult ε ω) (η := S.η ω) hε hη
    (hadj ε hε) (ρ0 := ρ0) (ρ1 := ρ1) (δ' := s) (d := s / 2) hs (by positivity) (by linarith)
    (by linarith) hd1 hm (s ^ χ / 2).toNNReal (g := ⌈(((ε⁻¹).toNNReal : ℝ≥0) : ℝ) *
      (((s ^ χ / 2).toNNReal : ℝ≥0) : ℝ) + 2⌉₊) (K := ⌊(2 * s) ^ (-3 : ℝ)⌋₊) (Nat.le_ceil _)
    (T := ε⁻¹ * s ^ χ) (ψ := ψ s) hgT (R₁ := ρ1 - s) (by linarith) hd4
    (ψ₀ := ENNReal.ofReal (ψ₀ (2 * s))) hd5 x hx
  refine absurd hlt (not_lt.2 ((measure_mono ?_).trans (hle.trans (hsmall s hs hss1))))
  intro X hX
  obtain ⟨a, b, ha, hb, hab, hXr⟩ := hX
  refine ⟨a, b, ha, hb, hab, lt_of_le_of_lt ?_ hXr⟩
  linarith

end ExitCouplingPathEvent
end MatedCRT
