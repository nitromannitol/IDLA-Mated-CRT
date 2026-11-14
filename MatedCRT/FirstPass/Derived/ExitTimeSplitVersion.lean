import MatedCRT.FirstPass.Derived.ExitTimeMeasurableVersion
import MatedCRT.FirstPass.Derived.ExitTimeTildeFieldIndependence

/-!
# A jointly measurable version of the exit time from `B_{1/2}` that factors through the field split

Let `T(ω, b) = lbmExitTime (S.clock ω) (ball 0 (1/2)) b` be the exit time of Liouville Brownian motion from the disc
of radius `1/2`, driven by a planar Brownian path `b` from `0`, in the environment `ω` of a valid mated-CRT setting,
and let `(X, B, …)` be a mating-of-trees coupling of the environment, linked to its field. On `B_{1/2}` the
circle-average field is `h_ε = B_{t₀} + h̃_ε` at the scales `ε < 1/10` (`ae_hcirc_eq_add_hTilde`, `t₀ = log (5/3)`),
and `h̃` is the measurable function `incrTilde γ X v` of the lateral field `X` and the increments
`v_u = B_{t₀ + u} - B_{t₀}` (`hTilde_eq_incrTilde`). Accordingly the approximating LQG clocks at the Brownian exit
time `τ` of `B_{1/2}` factor as `e^{γ B_{t₀}}` times the approximating clocks of `incrTilde γ X v`.

* `SplitVersion.exists_measurable_forall_eq_of_ae_continuous`: a real process with almost surely continuous paths and
  almost everywhere measurable marginals has a modification with measurable marginals that is indistinguishable from
  it (the grid regularization of the measurable modifications at the countably many grid times).
* `tildeClockApproxAtExit γ k ((x, v), b)`: the approximating LQG clock of `incrTilde γ x v` at the scale `2^{-k}`, at
  the exit time of `b` from `B_{1/2}`; it is jointly measurable (`measurable_tildeClockApproxAtExit`).
* `MatedCRTEnv.IsValid.exists_exitTime_version_eq_exp_mul`: for `0 < γ < 2` there are a measurable
  `T* : Ω × C([0, ∞), ℂ) → [0, ∞]` with `T*(ω, ·) = T(ω, ·)` `P^0`-almost surely for `P`-almost every `ω`, and a
  measurable `Ψ` of (lateral field, increments, path) with `T* = e^{γ B_{t₀}} Ψ(X, (B_{t₀ + u} - B_{t₀})_u, b)`
  `P ⊗ P^0`-almost surely. `Ψ` is the `limsup` of the approximating clocks of `h̃` along a deterministic subsequence
  of scales, along which they converge almost surely to `e^{-γ B_{t₀}}` times the LQG clock at `τ`
  (Garban-Rhodes-Vargas 2016, Theorem 2.7 (2); Berestycki 2015, Theorem 1.2).
* `MatedCRTEnv.IsValid.exists_matingOfTrees_exitTime_version_eq_exp_mul`: the same with the coupling of
  `S.IsValid`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

namespace SplitVersion

/-- **A measurable indistinguishable modification.** A real process `B` with almost everywhere measurable marginals
and almost surely continuous paths has a modification `B̂` with measurable marginals such that almost surely
`B̂_s = B_s` for all `s`. -/
theorem exists_measurable_forall_eq_of_ae_continuous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : ∀ s, AEMeasurable (B s) P) (hc : ∀ᵐ ω ∂P, Continuous fun s => B s ω) :
    ∃ Bh : ℝ≥0 → Ω → ℝ, (∀ s, Measurable (Bh s)) ∧ ∀ᵐ ω ∂P, ∀ s, Bh s ω = B s ω := by
  refine ⟨fun s ω => TildeField.gridRegularization (fun r => (hB r).mk (B r) ω) s, fun s => ?_, ?_⟩
  · show Measurable fun ω =>
      limsup (fun n : ℕ => (hB (TildeField.gridTime n s)).mk (B (TildeField.gridTime n s)) ω) atTop
    exact Measurable.limsup fun n => (hB (TildeField.gridTime n s)).measurable_mk
  · have hgrid : ∀ᵐ ω ∂P, ∀ m n : ℕ,
        (hB (Real.toNNReal ((m : ℝ) / ((n : ℝ) + 1)))).mk (B (Real.toNNReal ((m : ℝ) / ((n : ℝ) + 1)))) ω =
          B (Real.toNNReal ((m : ℝ) / ((n : ℝ) + 1))) ω := by
      refine ae_all_iff.2 fun m => ae_all_iff.2 fun n => ?_
      filter_upwards [(hB (Real.toNNReal ((m : ℝ) / ((n : ℝ) + 1)))).ae_eq_mk] with ω hω
      exact hω.symm
    filter_upwards [hgrid, hc] with ω hω hcω s
    have hseq : (fun n : ℕ => (hB (TildeField.gridTime n s)).mk (B (TildeField.gridTime n s)) ω) =
        fun n => B (TildeField.gridTime n s) ω :=
      funext fun n => hω ⌊(s : ℝ) * ((n : ℝ) + 1)⌋₊ n
    show limsup (fun n : ℕ => (hB (TildeField.gridTime n s)).mk (B (TildeField.gridTime n s)) ω) atTop =
      B s ω
    rw [hseq]
    exact TildeField.gridRegularization_of_continuous hcω s

/-- Before its exit time from `B_{1/2}` (truncated to `0` when infinite) a path stays in `B_{1/2}`. -/
theorem mem_ball_of_lt_toNNReal_pathExitTime {b : ContinuousPath ℂ} {s : ℝ≥0}
    (hs : s < (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal) : b s ∈ ball (0 : ℂ) (1 / 2) := by
  by_contra hn
  have h1 : pathExitTime (ball (0 : ℂ) (1 / 2)) b ≤ (s : ℝ≥0∞) := sInf_le ⟨s, rfl, hn⟩
  have h2 : (s : ℝ≥0∞) < pathExitTime (ball (0 : ℂ) (1 / 2)) b :=
    (ENNReal.coe_lt_coe.2 hs).trans_le ENNReal.coe_toNNReal_le_self
  exact absurd h1 (not_le.2 h2)

/-- For a continuous radial path `b`, at a scale `ε ∈ (0, 1/10)`, along a planar path that stays in `B_{1/2}` before
`t`, the approximating LQG clock of `h̃` is that of `incrTilde γ X (u ↦ b_{t₀ + u} - b_{t₀})`. -/
theorem lqgClockApprox_hTilde_eq_incrTilde {γ : ℝ} (X : LQGMetric.DistC) {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 10)) {w : ContinuousPath ℂ} {t : ℝ≥0}
    (hw : ∀ s : ℝ≥0, s < t → w s ∈ ball (0 : ℂ) (1 / 2)) :
    lqgClockApprox γ (hTilde γ X b) ε w t =
      lqgClockApprox γ (incrTilde γ X (fun u => b (splitTime + u) - b splitTime)) ε w t := by
  have h := lqgClockApprox_eq_exp_mul_of_eq_add (γ := γ) (c := 0) (ε := ε) (h := hTilde γ X b)
    (hT := incrTilde γ X (fun u => b (splitTime + u) - b splitTime)) (D := ball (0 : ℂ) (1 / 2))
    (fun z hz => by rw [zero_add]; exact hTilde_eq_incrTilde γ X hb hε hz) hw
  rw [h, mul_zero, Real.exp_zero, one_mul]

end SplitVersion

open SplitVersion

/-- The approximating LQG clock `∫_0^τ ε^{γ²/2} e^{γ h̃_ε(b_s)} ds` of the field `h̃ = incrTilde γ x v` at the scale
`ε = 2^{-k}`, at the exit time `τ` of the path `b` from `B_{1/2}` (set to `0` if `b` never exits), as a function of
the lateral field `x`, the increments `v` and the path `b`. -/
noncomputable def tildeClockApproxAtExit (γ : ℝ) (k : ℕ)
    (q : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ) : ℝ :=
  lqgClockApprox γ (incrTilde γ q.1.1 q.1.2) (dyadicScale k) q.2
    (pathExitTime (ball (0 : ℂ) (1 / 2)) q.2).toNNReal

/-- The approximating clocks of `h̃` at the exit time are jointly measurable in the lateral field, the increments
(product σ-algebra) and the path. -/
theorem measurable_tildeClockApproxAtExit (γ : ℝ) (k : ℕ) : Measurable (tildeClockApproxAtExit γ k) :=
  ExitTimeVersion.measurable_lqgClockApprox_comp_time
    (φ := fun z : MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ) => incrTilde γ z.1 z.2) γ
    (measurable_incrTilde_scale γ (dyadicScale k))
    (KilledOccupation.measurable_pathExitTime_ball 0 (1 / 2)).ennreal_toNNReal

/-- **The exit time from `B_{1/2}` factors through the field split.** Let `S` be valid, `0 < γ < 2`, and let
`(X, B, B', …)` be a mating-of-trees coupling of the environment linked to its field. There are a measurable
`T* : Ω × C([0, ∞), ℂ) → [0, ∞]` with `T*(ω, ·) = lbmExitTime (S.clock ω) (ball 0 (1/2))` `P^0`-almost surely for
`S.P`-almost every `ω`, and a measurable real `Ψ` of the lateral field, the increments and the Brownian path, such
that `S.P ⊗ P^0`-almost surely `T*(ω, b) = e^{γ B_{t₀}(ω)} Ψ((X ω, (B_{t₀ + u}(ω) - B_{t₀}(ω))_u), b)`,
`t₀ = log (5/3)`. -/
theorem MatedCRTEnv.IsValid.exists_exitTime_version_eq_exp_mul {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    (hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∃ (Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞)
      (Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ),
      Measurable Tstar ∧
      (∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
        Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) ∧
      Measurable Ψ ∧
      ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
        Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
          Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball (0 : ℂ) (1 / 2)) b :=
    KilledOccupation.measurable_pathExitTime_ball 0 (1 / 2)
  have hfin : ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion 0,
      pathExitTime (ball (0 : ℂ) (1 / 2)) b < ⊤ :=
    ae_lt_top hσ (KilledOccupation.lintegral_pathExitTime_planar_ne_top 0 0 (1 / 2))
  have hB := hcpl.bm_B
  -- measurable versions `Y'` of `B_{t₀}` and `Z'` of `(X, (B_{t₀ + u} - B_{t₀})_u)`
  obtain ⟨Y', Z', hY'm, hZ'm, hYZ⟩ : ∃ (Y' : Ω → ℝ) (Z' : Ω → MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)),
      Measurable Y' ∧ Measurable Z' ∧ ∀ᵐ ω ∂S.P, Y' ω = B splitTime ω ∧
        Z' ω = (X ω, fun u : ℝ≥0 => B (splitTime + u) ω - B splitTime ω) := by
    obtain ⟨Bh, hBhm, hBh⟩ :=
      exists_measurable_forall_eq_of_ae_continuous hB.toIsPreBrownianReal.aemeasurable hB.cont
    refine ⟨Bh splitTime, fun ω => (X ω, fun u => Bh (splitTime + u) ω - Bh splitTime ω), hBhm splitTime,
      hcpl.gff.measurable.prodMk
        (Measurable.of_eval fun u => (hBhm (splitTime + u)).sub (hBhm splitTime)), ?_⟩
    filter_upwards [hBh] with ω hω
    exact ⟨hω splitTime, by simp only [hω]⟩
  -- the approximating clocks of `h̃` at the exit time, read through `Z'`
  have hA : ∀ k : ℕ, Measurable fun p : Ω × ContinuousPath ℂ => tildeClockApproxAtExit γ k (Z' p.1, p.2) :=
    fun k => (measurable_tildeClockApproxAtExit γ k).comp ((hZ'm.comp measurable_fst).prodMk measurable_snd)
  have hevent : ∀ᶠ k : ℕ in atTop, dyadicScale k ∈ Ioo (0 : ℝ) (1 / 10) := by
    have h0 : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
      show Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0)
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [(tendsto_order.1 h0).2 (1 / 10) (by norm_num)] with k hk
    exact Set.mem_Ioo.2 ⟨pow_pos (by norm_num) k, hk⟩
  -- quenched convergence in probability to `e^{-γ B_{t₀}}` times the LQG clock at the exit time
  have hY : ∀ᵐ ω ∂S.P, ∀ η : ℝ, 0 < η → Tendsto (fun k : ℕ => planarBrownianMotion 0
      {b | η ≤ |tildeClockApproxAtExit γ k (Z' ω, b) - Real.exp (-(γ * B splitTime ω)) *
        S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal|}) atTop (𝓝 0) := by
    filter_upwards [hYZ, hB.cont, ae_lqgClockApprox_dyadic_hcirc_eq_exp_mul hS hγ hγ2 hcpl hlink,
      hS.isLQGClock] with ω hωYZ hωB hωL2 hωclock η hη
    have hc : 0 < Real.exp (-(γ * B splitTime ω)) := Real.exp_pos _
    have hconv := ExitTimeVersion.tendsto_measure_lqgClockApprox_exitTime_sub_clock hσ hfin
      (hωclock 0).1 (div_pos hη hc)
    refine hconv.congr' ?_
    filter_upwards [hevent] with k hk
    congr 1
    ext b
    simp only [mem_ofPred_eq]
    have hw : ∀ s : ℝ≥0, s < (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal →
        b s ∈ ball (0 : ℂ) (1 / 2) := fun s hs => mem_ball_of_lt_toNNReal_pathExitTime hs
    have hfac : tildeClockApproxAtExit γ k (Z' ω, b) = Real.exp (-(γ * B splitTime ω)) *
        lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal := by
      rw [hωL2 k hk.2 b _ hw, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      show lqgClockApprox γ (incrTilde γ (Z' ω).1 (Z' ω).2) (dyadicScale k) b
        (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal = _
      rw [hωYZ.2]
      exact (lqgClockApprox_hTilde_eq_incrTilde (X ω) hωB hk hw).symm
    rw [hfac, ← mul_sub, abs_mul, abs_of_pos hc, div_le_iff₀ hc, mul_comm (Real.exp (-(γ * B splitTime ω)))]
  -- a deterministic subsequence along which the clocks converge almost surely
  have hcauchy : ∀ᵐ ω ∂S.P, ∀ η : ℝ, 0 < η → Tendsto (fun kl : ℕ × ℕ => planarBrownianMotion 0
      {b | η ≤ |tildeClockApproxAtExit γ kl.1 (Z' ω, b) - tildeClockApproxAtExit γ kl.2 (Z' ω, b)|})
      atTop (𝓝 0) := by
    filter_upwards [hY] with ω hω η hη
    exact ExitTimeVersion.tendsto_measure_gap_of_tendsto_measure (planarBrownianMotion 0)
      (a := fun k b => tildeClockApproxAtExit γ k (Z' ω, b)) hω hη
  obtain ⟨κ, hκ, hlim⟩ := ExitTimeVersion.exists_strictMono_ae_tendsto_of_ae_cauchy S.P
    (planarBrownianMotion 0) (A := fun k p => tildeClockApproxAtExit γ k (Z' p.1, p.2)) hA hcauchy
  have hlimsup : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      limsup (fun j => tildeClockApproxAtExit γ (κ j) (Z' ω, b)) atTop =
        Real.exp (-(γ * B splitTime ω)) * S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal :=
    ExitTimeVersion.ae_ae_limsup_eq_of_ae_tendstoInMeasure S.P (planarBrownianMotion 0)
      (A := fun k p => tildeClockApproxAtExit γ k (Z' p.1, p.2)) hA hκ hlim
      (fun ω b => Real.exp (-(γ * B splitTime ω)) *
        S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal) hY
  refine ⟨fun p => ENNReal.ofReal (Real.exp (γ * Y' p.1) *
      limsup (fun j => tildeClockApproxAtExit γ (κ j) (Z' p.1, p.2)) atTop),
    fun q => limsup (fun j => tildeClockApproxAtExit γ (κ j) q) atTop, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp ((hY'm.comp measurable_fst).const_mul γ)).mul
        (Measurable.limsup fun j => hA (κ j)))
  · filter_upwards [hYZ, hlimsup, hS.ae_lbmExitTime_ball_half_eq_clock] with ω hωYZ hωlim hωlbm
    filter_upwards [hωlim, hωlbm] with b hb1 hb2
    obtain ⟨τ, -, hτ, hlbm⟩ := hb2
    show ENNReal.ofReal (Real.exp (γ * Y' ω) *
      limsup (fun j => tildeClockApproxAtExit γ (κ j) (Z' ω, b)) atTop) = _
    rw [hb1, hωYZ.1, hlbm, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, hτ,
      ENNReal.toNNReal_coe]
  · exact Measurable.limsup fun j => measurable_tildeClockApproxAtExit γ (κ j)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hYZ] with p hp
    show ENNReal.ofReal (Real.exp (γ * Y' p.1) *
      limsup (fun j => tildeClockApproxAtExit γ (κ j) (Z' p.1, p.2)) atTop) = _
    simp only [hp.1, hp.2]

/-- **The exit time from `B_{1/2}` factors through the field split, with the coupling of `S.IsValid`.** For a valid
environment and `0 < γ < 2` the mating-of-trees coupling `(X, B, B', …)` can be chosen so that the conclusion of
`MatedCRTEnv.IsValid.exists_exitTime_version_eq_exp_mul` holds. -/
theorem MatedCRTEnv.IsValid.exists_matingOfTrees_exitTime_version_eq_exp_mul {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      ∃ (Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞)
        (Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ),
        Measurable Tstar ∧
        (∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
          Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) ∧
        Measurable Ψ ∧
        ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
          Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
            Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hae] with ω hω
    exact hω.2
  exact ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcpl,
    hS.exists_exitTime_version_eq_exp_mul hγ hγ2 hcpl hlink⟩

end MatedCRT
