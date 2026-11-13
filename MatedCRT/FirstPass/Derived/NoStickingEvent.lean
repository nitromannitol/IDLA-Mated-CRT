import MatedCRT.FirstPass.Derived.ExitCouplingEvent
import MatedCRT.FirstPass.Derived.SuccessiveExitWindows
import MatedCRT.FirstPass.Derived.ExitTimeMomentKhasminskii
import MatedCRT.FirstPass.S4S6c.FiniteExitMomentHone68

/-!
# Proposition 6.14 of Berestycki-Gwynne at the event level: the walk does not get stuck

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Proposition 6.14.  Let `σ_k = σ_k^ε(δ)` be the successive exit times of the walk from
the vertices of `B_δ` around its own previous positions (Lemma 6.10).  Given the exit time moment bound
`E[τ^N] ≤ N! (ε⁻¹ δ^{q'})^N` of Corollary 5.2 and the estimate (6.50) that the walk leaves `B_ρ` before
`σ_{⌊δ⁻³⌋}`, a union bound over the first `⌊δ⁻³⌋ + 1` gaps (6.49) and the deterministic window argument of
(6.51) show that, with probability tending to `1` as `ε → 0` and then `δ → 0`, from every vertex of `V^ε(B_ρ)`
the walk travels Euclidean distance at least `δ` in every window of `2 ⌊ε⁻¹ δ^q⌋` steps that starts at least
`⌊ε⁻¹ δ^q⌋` steps before the exit time from `V^ε(B_ρ)`.

* `gapTail` is the superpolynomial function collecting the bounds `2 N! δ^{N c - 3}` over all `N`.
* `srwLaw_noSticking_le` is the quenched statement for one environment.
* `limLimSmall_noSticking` is the event-level statement; the exit time moment bound is Lemma 2.19 plus the
  Khasminskii estimate, and (6.50) is the explicit hypothesis `h610`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter MatedCRT.SuccessiveExitGaps
open scoped ENNReal Topology

namespace MatedCRT
namespace NoStickingEvent

/-- The superpolynomial tail `inf_N 2 N! δ^{N c - 3}` of the union bound (6.49). -/
noncomputable def gapTail (c δ : ℝ) : ℝ :=
  ⨅ N : ℕ, 2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * c - 3)

theorem gapTail_le {c δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    gapTail c δ ≤ 2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * c - 3) := by
  refine ciInf_le ⟨0, ?_⟩ N
  rintro _ ⟨M, rfl⟩
  positivity

theorem gapTail_nonneg {c δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ gapTail c δ :=
  Real.iInf_nonneg fun N => by positivity

/-- `δ ^ (-p) * gapTail c δ → 0` as `δ → 0+` for every `p`, when `c > 0`. -/
theorem tendsto_gapTail_mul {c : ℝ} (hc : 0 < c) (p : ℝ) :
    Tendsto (fun δ : ℝ => δ ^ (-p) * gapTail c δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((p + 3) / c)
  have hNc : p + 3 < (N : ℝ) * c := (div_lt_iff₀ hc).1 hN
  have hpos : 0 < (N : ℝ) * c - 3 - p := by linarith
  have hlim : Tendsto (fun δ : ℝ => 2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * c - 3 - p))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (ExitCouplingNumerics.tendsto_rpow_zero hpos).const_mul (2 * (N.factorial : ℝ))
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    exact mul_nonneg (Real.rpow_nonneg hδ'.le _) (gapTail_nonneg hδ'.le)
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    calc δ ^ (-p) * gapTail c δ
        ≤ δ ^ (-p) * (2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * c - 3)) :=
          mul_le_mul_of_nonneg_left (gapTail_le hδ'.le N) (Real.rpow_nonneg hδ'.le _)
      _ = 2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * c - 3 - p) := by
          rw [show (N : ℝ) * c - 3 - p = (N : ℝ) * c - 3 + (-p) by ring, Real.rpow_add hδ']
          ring

/-- `(2 δ)^q ≤ δ^(q/2)` for `0 < δ ≤ 1/4`. -/
theorem two_mul_rpow_le {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    (2 * δ) ^ q ≤ δ ^ (q / 2) := by
  have h2 : (2 : ℝ) ^ q = (4 : ℝ) ^ (q / 2) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have h1 : (2 : ℝ) ^ q * δ ^ (q / 2) ≤ 1 := by
    rw [h2, ← Real.mul_rpow (by norm_num) hδ.le]
    exact Real.rpow_le_one (by positivity) (by linarith) (by positivity)
  calc (2 * δ) ^ q = 2 ^ q * δ ^ q := Real.mul_rpow (by norm_num) hδ.le
    _ = (2 ^ q * δ ^ (q / 2)) * δ ^ (q / 2) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
    _ ≤ 1 * δ ^ (q / 2) := by gcongr
    _ = δ ^ (q / 2) := one_mul _

/-- From the first moment bound on the exit time to all moments (Khasminskii). -/
theorem exitTimeMoment_le_ofReal {m : ℤ → ℤ → ℕ} {A : Set ℤ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ a ∈ A, expectedExitTime m A a ≤ ENNReal.ofReal r) (N : ℕ) (a : ℤ) :
    exitTimeMoment m A a N ≤ ENNReal.ofReal ((N.factorial : ℝ) * r ^ N) := by
  refine (exitTimeMoment_le_factorial_mul_pow m A h N a).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr, ENNReal.ofReal_natCast]

/-- Cells meeting `B_δ(z)` are inside `B_{2δ}(z)` and miss its boundary when they have diameter `≤ δ/2`. -/
theorem cellVertices_ball_subset_interior {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball z δ).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ δ / 2) :
    cellVertices ε η (ball z δ) ⊆ interiorCellVertices ε η (ball z (2 * δ)) := by
  intro k hk
  obtain ⟨p, hpc, hpb⟩ := hk
  have hsub : cell ε η k ⊆ ball z (2 * δ) := by
    intro u hu
    have h1 := hdiam k ⟨p, hpc, hpb⟩ u hu p hpc
    rw [mem_ball] at hpb ⊢
    linarith [dist_triangle u p z]
  refine Set.mem_sdiff_of_mem
    (show (cell ε η k ∩ ball z (2 * δ)).Nonempty from ⟨p, hpc, ball_subset_ball (by linarith) hpb⟩) ?_
  rintro ⟨u, huc, hu⟩
  rw [frontier_ball _ (by positivity : (2 * δ) ≠ 0)] at hu
  have h1 := hsub huc
  rw [mem_ball] at h1
  rw [mem_sphere] at hu
  linarith

theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨by rw [mul_sub, mul_one]; linarith, le_rfl⟩, rfl⟩

/-- **Quenched form of (6.49)-(6.51).**  For one environment: if the exit time moments from the regions `A y`
are at most `N! (ε⁻¹ δ^{q'})^N` for `y ∈ Y`, and the walk from `x ∈ Y` leaves `Y` before `σ_{⌊δ⁻³⌋}`
except with probability `ψ₀`, then with probability at least `1 - ψ₀ - gapTail (q' - q) δ` every window
`[j, j + 2 b)` with `j + b ≤ τ_Y`, `b = ⌊ε⁻¹ δ^q⌋`, contains times `i₁ ≤ i₂` with the walk outside the region
`A (X_{i₁})` at time `i₂`. -/
theorem srwLaw_noSticking_le {m : ℤ → ℤ → ℕ} {ε δ q q' : ℝ} {Y : Set ℤ} {A : ℤ → Set ℤ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 1 ≤ ⌊ε⁻¹ * δ ^ q⌋₊)
    (hM : ∀ y ∈ Y, ∀ N : ℕ, exitTimeMoment m (A y) y N ≤
      ENNReal.ofReal ((N.factorial : ℝ) * (ε⁻¹ * δ ^ q') ^ N))
    {ψ₀ : ℝ} (hψ0 : 0 ≤ ψ₀)
    (hY : ∀ x ∈ Y, srwLaw m x {X | ¬ vExitTime Y X ≤ succExit A ⌊δ ^ (-3 : ℝ)⌋₊ X} ≤
      ENNReal.ofReal ψ₀) {x : ℤ} (hx : x ∈ Y) :
    srwLaw m x {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤ vExitTime Y X →
      ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧ X i₂ ∉ A (X i₁)} ≤
      ENNReal.ofReal (ψ₀ + gapTail (q' - q) δ) := by
  have hgap : ∀ N : ℕ, srwLaw m x {X | ∃ k < ⌊δ ^ (-3 : ℝ)⌋₊ + 1, X ∈ gapEvent A Y ⌊ε⁻¹ * δ ^ q⌋₊ k} ≤
      ENNReal.ofReal (2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * (q' - q) - 3)) := fun N =>
    srwLaw_exists_gapEvent_le_delta m x A Y N hε hδ hδ1 (fun y hy => hM y hy N)
  have hgapT : srwLaw m x {X | ∃ k < ⌊δ ^ (-3 : ℝ)⌋₊ + 1, X ∈ gapEvent A Y ⌊ε⁻¹ * δ ^ q⌋₊ k} ≤
      ENNReal.ofReal (gapTail (q' - q) δ) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (gapTail_nonneg hδ.le)]
    exact le_ciInf fun N => ENNReal.toReal_le_of_le_ofReal (by positivity) (hgap N)
  have hsub : {X : ℕ → ℤ | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤ vExitTime Y X →
        ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧ X i₂ ∉ A (X i₁)} ⊆
      {X | ¬ vExitTime Y X ≤ succExit A ⌊δ ^ (-3 : ℝ)⌋₊ X} ∪
        {X | ∃ k < ⌊δ ^ (-3 : ℝ)⌋₊ + 1, X ∈ gapEvent A Y ⌊ε⁻¹ * δ ^ q⌋₊ k} := by
    intro X hX
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine hX fun j hj => exists_window_travel A Y hb X (fun k hk hkX => h2 ⟨k, hk, hkX⟩)
      (not_not.1 h1) hj
  calc srwLaw m x _ ≤ srwLaw m x ({X | ¬ vExitTime Y X ≤ succExit A ⌊δ ^ (-3 : ℝ)⌋₊ X} ∪
        {X | ∃ k < ⌊δ ^ (-3 : ℝ)⌋₊ + 1, X ∈ gapEvent A Y ⌊ε⁻¹ * δ ^ q⌋₊ k}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ψ₀ + ENNReal.ofReal (gapTail (q' - q) δ) := add_le_add (hY x hx) hgapT
    _ = ENNReal.ofReal (ψ₀ + gapTail (q' - q) δ) :=
        (ENNReal.ofReal_add hψ0 (gapTail_nonneg hδ.le)).symm

/-- **Proposition 6.14 of Berestycki-Gwynne at the event level.**  Fix `0 < ρ < 1`.  There are `q > 0`
(depending only on `γ`) and a superpolynomial `ψ` such that for every valid environment, with probability
tending to `1` as `ε → 0` and then `δ → 0`, for every `x ∈ V^ε(B_ρ)` the walk from `x` satisfies with
probability at least `1 - ψ(δ)`: for every window `[j, j + 2 ⌊ε⁻¹ δ^q⌋)` with `j + ⌊ε⁻¹ δ^q⌋ ≤ τ_{B_ρ}` there are
times `j ≤ i₁ ≤ i₂` in it with `|η(X_{i₂}) - η(X_{i₁})| ≥ δ`.  (BG20 (6.47) is stated for all `j ≤ τ_{B_ρ}`,
but its proof (6.49)-(6.51) gives the gap bound only for the indices with `σ_{k-1} ≤ τ_{B_ρ}`, so a window
that sticks out of `[0, τ_{B_ρ}]` is not covered; the consumer, the last assertion of Proposition 6.2,
only needs the windows inside `[0, τ_{B_ρ}]`.)  The inputs are Lemma 2.19 (exit time moments through the
Khasminskii estimate, Corollary 5.2), the event that cells meeting `B_ρ` are small, and the explicit
hypothesis `h610`: the estimate (6.50) of Lemma 6.10 with `ζ = 1`, in event form. -/
theorem limLimSmall_noSticking {𝒮 : SpaceFillingSLEModel}
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h610 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X ≤
              succExit (fun w => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) δ))
                ⌊δ ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ δ)})) :
    ∃ q : ℝ, 0 < q ∧ ∃ ψ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x
            {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤
                vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧
                δ ≤ ‖vertexPoint ε (S.η ω) (X i₂) - vertexPoint ε (S.η ω) (X i₁)‖} ≤
            ENNReal.ofReal (ψ δ)}) := by
  obtain ⟨q0, hq0, h219'⟩ := ExitCouplingEventInputs.limLimSmall_expectedExitTime h219 hγ hγ2
  obtain ⟨ψ₀, hψ₀, h610'⟩ := h610
  obtain ⟨ρ1, hρρ1, hρ11⟩ : ∃ ρ1 : ℝ, ρ < ρ1 ∧ ρ1 < 1 := ⟨(ρ + 1) / 2, by linarith, by linarith⟩
  have hq4 : 0 < q0 / 4 := by positivity
  refine ⟨q0 / 4, hq4, fun δ => ψ₀ δ + gapTail (q0 / 4) δ,
    ⟨fun δ hδ => add_nonneg (hψ₀.1 δ hδ) (gapTail_nonneg hδ), fun p hp => ?_⟩, fun Ω _ S hS => ?_⟩
  · have h := (hψ₀.2 p hp).add (tendsto_gapTail_mul hq4 p)
    rw [add_zero] at h
    exact h.congr fun δ => (mul_add _ _ _).symm
  obtain ⟨η', hae⟩ : ∃ η' : Ω → C(ℝ, ℂ), ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := by
    classical
    refine ⟨fun ω => if h : Continuous (S.η ω) then ⟨S.η ω, h⟩ else ⟨fun _ => 0, continuous_const⟩, ?_⟩
    filter_upwards [TraceInputs68.ae_continuous_eta hS] with ω hω
    simp [hω]
  have h2d : Tendsto (fun δ : ℝ => 2 * δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  have h1 := CellDiameterEvent.limLimSmall_cellDiam hS hae ρ1 (d := fun δ => δ / 2)
    (fun δ hδ => by positivity)
  have h3 := (h219' ρ1 (by linarith) hρ11 Ω S hS).comp_delta (φ := fun δ : ℝ => 2 * δ)
    (fun δ hδ => by positivity) h2d
  have h5 := h610' Ω S hS
  have hG := (h1.union h3).union h5
  refine LimLimSmall.mono_of_small_ae hG ⟨min (1 / 4) ((ρ1 - ρ) / 3),
    lt_min (by norm_num) (by linarith), fun δ hδ hδlt => ⟨δ ^ (q0 / 4), by positivity,
      fun ε hε hεlt => ?_⟩⟩
  have hδ4 : δ ≤ 1 / 4 := (lt_of_lt_of_le hδlt (min_le_left _ _)).le
  have hδ3 : δ < (ρ1 - ρ) / 3 := lt_of_lt_of_le hδlt (min_le_right _ _)
  filter_upwards [hae] with ω hηω hfail
  by_contra hGω
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hGω
  obtain ⟨⟨hd1, hd3⟩, hd5⟩ := hGω
  rw [hηω] at hd1
  have hvp : ∀ y ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
      ‖vertexPoint ε (S.η ω) y‖ < ρ + δ / 2 := by
    intro y hy
    obtain ⟨u, huc, hub⟩ := hy
    have hy1 : (cell ε (S.η ω) y ∩ ball (0 : ℂ) ρ1).Nonempty :=
      ⟨u, huc, ball_subset_ball hρρ1.le hub⟩
    have h1' := hd1 y hy1 _ (vertexPoint_mem_cell hε _ y) u huc
    rw [mem_ball, dist_zero_right] at hub
    rw [dist_eq_norm] at h1'
    calc ‖vertexPoint ε (S.η ω) y‖
        = ‖(vertexPoint ε (S.η ω) y - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖vertexPoint ε (S.η ω) y - u‖ + ‖u‖ := norm_add_le _ _
      _ < ρ + δ / 2 := by linarith
  have hdiam_at : ∀ y ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ), ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ ball (vertexPoint ε (S.η ω) y) δ).Nonempty →
        ∀ u ∈ cell ε (S.η ω) k, ∀ v ∈ cell ε (S.η ω) k, dist u v ≤ δ / 2 := by
    intro y hy k hk
    obtain ⟨p, hpc, hpb⟩ := hk
    have hp1 : (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ1).Nonempty := by
      refine ⟨p, hpc, ?_⟩
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hpb
      have h1' := hvp y hy
      calc ‖p‖ = ‖(p - vertexPoint ε (S.η ω) y) + vertexPoint ε (S.η ω) y‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖p - vertexPoint ε (S.η ω) y‖ + ‖vertexPoint ε (S.η ω) y‖ := norm_add_le _ _
        _ < ρ1 := by linarith
    exact hd1 k hp1
  have hM : ∀ y ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ), ∀ N : ℕ,
      exitTimeMoment (S.mult ε ω) (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) δ)) y N ≤
        ENNReal.ofReal ((N.factorial : ℝ) * (ε⁻¹ * δ ^ (q0 / 2)) ^ N) := by
    intro y hy N
    refine exitTimeMoment_le_ofReal (by positivity) ?_ N y
    intro a _
    have hsub := cellVertices_ball_subset_interior hδ (hdiam_at y hy)
    have hball : ball (vertexPoint ε (S.η ω) y) (2 * δ) ⊆ ball (0 : ℂ) ρ1 := by
      intro w hw
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hw
      have h1' := hvp y hy
      calc ‖w‖ = ‖(w - vertexPoint ε (S.η ω) y) + vertexPoint ε (S.η ω) y‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖w - vertexPoint ε (S.η ω) y‖ + ‖vertexPoint ε (S.η ω) y‖ := norm_add_le _ _
        _ < ρ1 := by linarith
    calc expectedExitTime (S.mult ε ω)
          (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) δ)) a
        ≤ expectedExitTime (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (2 * δ))) a :=
          lintegral_mono fun X =>
            ENat.toENNReal_le.2 (FiniteExitMomentHone68.vExitTime_mono_set hsub X)
      _ ≤ ENNReal.ofReal (ε⁻¹ * (2 * δ) ^ q0) := hd3 _ hball a
      _ ≤ ENNReal.ofReal (ε⁻¹ * δ ^ (q0 / 2)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (two_mul_rpow_le hq0.le hδ hδ4) (inv_nonneg.2 hε.le))
  have hb : 1 ≤ ⌊ε⁻¹ * δ ^ (q0 / 4)⌋₊ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_one, inv_mul_eq_div, le_div_iff₀ hε, one_mul]
    exact hεlt.le
  refine hfail fun x hx => ?_
  have hδ1 : δ ≤ 1 := by linarith
  have hq : q0 / 2 - q0 / 4 = q0 / 4 := by ring
  have key := srwLaw_noSticking_le (q := q0 / 4) (q' := q0 / 2)
    (A := fun w => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) δ)) hε hδ hδ1 hb hM
    (hψ₀.1 δ hδ.le) hd5 hx
  rw [hq] at key
  refine (measure_mono ?_).trans key
  · intro X hX hcon
    refine hX fun j hj => ?_
    obtain ⟨i₁, i₂, h1', h2', h3', h4'⟩ := hcon j hj
    refine ⟨i₁, i₂, h1', h2', h3', ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact h4' (show (cell ε (S.η ω) (X i₂) ∩
        ball (vertexPoint ε (S.η ω) (X i₁)) δ).Nonempty from
      ⟨vertexPoint ε (S.η ω) (X i₂), vertexPoint_mem_cell hε _ _, by
        rw [mem_ball, dist_eq_norm]; exact hlt⟩)

end NoStickingEvent
end MatedCRT

#print axioms MatedCRT.NoStickingEvent.srwLaw_noSticking_le
#print axioms MatedCRT.NoStickingEvent.limLimSmall_noSticking
