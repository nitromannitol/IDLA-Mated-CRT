import MatedCRT.FirstPass.S4S6c.ShellCoreR68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S6n
import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HoneElAe68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68
import MatedCRT.FirstPass.S4S6c.ShellTestPw68
import MatedCRT.FirstPass.S4S6c.WindowRfGlobal68
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68
import MatedCRT.FirstPass.S4S6c.B1EnvPw68

/-!
# Pointwise, radius-uniform inputs for the one-test order

Corrected draft (paper/idla_mated_crt-corrected.tex): dyadic Borel-Cantelli over the scales
`d = dyadicD r` (l.2866-2945); the intersection of the `ε`-events with `r² ≤ d < 2r²`, "uniform over `r`" (l.2995-3016);
one good-annulus test, pointwise (l.3033-3036).

* `ae_forall_dyadicD`: a binder `P (dyadicD r) ω` that holds almost surely at each dyadic scale holds almost surely at
  all radii at once (countable swap over `k : ℕ`; `dyadicD r = (1/2)^k` for `k = Nat.log 2 ⌊1/r²⌋₊`, by definition).
* `cellDiam_ae_dyadicD`: the cell-diameter bound at all radii, through that swap.
  Its dyadic a.s. premise is a named input here: the bound is stated with `Set.univ`, stronger than the paper's `h_ε`
  (corrected l.2995-2996, the supremum over cells meeting `B_ρ`).
* `eps_pow_le_of_small`: the deterministic binder `hεcell` of the one-radius assembly (B1Assembly68.lean) for every
  `r ≥ 10 ε^{ω₀}`, for `ε` below a threshold `e0` (the Eps chain: `2 ω₀ < 2/(2+γ)² - ζ`, `ε ≤ e0`).
* `ae_null_singleton_of_valid`, `ae_finite_on_compacts_of_valid`: the r-free environment facts (μ atomless, μ finite on
  compacts) almost surely for a valid environment; `ae_continuous_eta` (TraceInputs68) gives continuity of `η`.
* `ShellOneTestPointwiseEnvStmt`: `ShellOneTestPointwiseStmt` (ShellCoreR68.lean) with those facts pointwise at `ω`.
  It is weaker than the old input, and `shellOneTestOrderAeStmt_of_pointwiseEnv` discharges them a.s. in the swap.

Terminology: Armstrong-Kuusi-Mourrat (one-test bound, shells), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68ShellCorePw

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- Every dyadic radius is one of the scales `(1/2)^k`, `k : ℕ`. -/
theorem dyadicD_eq_pow (r : ℝ) : ∃ k : ℕ, dyadicD r = (1 / 2 : ℝ) ^ k :=
  ⟨Nat.log 2 ⌊1 / r ^ 2⌋₊, rfl⟩

/-- **Countable swap over the dyadic scales.** A binder `P (dyadicD r) ω` that is almost surely true at each scale
`(1/2)^k` is almost surely true at all radii at once: `ae_all_iff` over `k : ℕ`, then the scale of each `r`. -/
theorem ae_forall_dyadicD {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {Ew : ℝ → Set Ω} {P : ℝ → Ω → Prop}
    (h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → P ((1 / 2 : ℝ) ^ k) ω) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, ω ∈ Ew (dyadicD r) → P (dyadicD r) ω := by
  filter_upwards [ae_all_iff.mpr h] with ω hω r hr
  exact hω (Nat.log 2 ⌊1 / r ^ 2⌋₊) hr

/-- **The mesh bound through the dyadic swap.** The bound
`CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ` is almost surely true at all radii with `ω ∈ Ew (dyadicD r)` once its
dyadic form holds almost surely at each scale `(1/2)^k`. The dyadic premise `h` is NOT derived here (report). -/
theorem cellDiam_ae_dyadicD {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {Ew : ℝ → Set Ω} (ε : ℝ)
    (η : Ω → ℝ → ℂ)
    (h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → CellDiamLe ε (η ω) ((1 / 2 : ℝ) ^ k / 100) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, ω ∈ Ew (dyadicD r) → CellDiamLe ε (η ω) (dyadicD r / 100) Set.univ :=
  ae_forall_dyadicD (P := fun d ω => CellDiamLe ε (η ω) (d / 100) Set.univ) h

/-- **The deterministic binder `hεcell` for all radii at once.** If `2 ω₀ < A` (the Eps chain condition
`2 ω₀ < 2/(2+γ)² - ζ` with `A = 2/(2+γ)² - ζ`), there is a threshold `e0 > 0` such that for `0 < ε ≤ e0` and every
`r ≥ 10 ε^{ω₀}`: `ε^A ≤ c0 r² / 100`. Here `c0 = K.c0` in the one-radius assembly. -/
theorem eps_pow_le_of_small {c0 A ω₀ : ℝ} (hc0 : 0 < c0) (hA : 2 * ω₀ < A) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e0 → ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r →
      ε ^ A ≤ c0 * r ^ 2 / 100 := by
  have hp : 0 < A - 2 * ω₀ := by linarith
  refine ⟨min 1 (c0 ^ (1 / (A - 2 * ω₀))), lt_min one_pos (Real.rpow_pos_of_pos hc0 _), ?_⟩
  intro ε hε hεe r hr
  have hεc : ε ≤ c0 ^ (1 / (A - 2 * ω₀)) := le_trans hεe (min_le_right _ _)
  have hpc : ε ^ (A - 2 * ω₀) ≤ c0 := by
    calc ε ^ (A - 2 * ω₀) ≤ (c0 ^ (1 / (A - 2 * ω₀))) ^ (A - 2 * ω₀) :=
          Real.rpow_le_rpow hε.le hεc hp.le
      _ = c0 := by rw [one_div, Real.rpow_inv_rpow hc0.le hp.ne']
  have hsplit : ε ^ A = ε ^ (A - 2 * ω₀) * (ε ^ ω₀) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]
    congr 1
    ring
  have hx0 : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε _
  have h10 : (10 * ε ^ ω₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by linarith) hr 2
  have hx : (ε ^ ω₀) ^ 2 ≤ r ^ 2 / 100 := by nlinarith [h10]
  rw [hsplit, Real.rpow_two]
  calc ε ^ (A - 2 * ω₀) * (ε ^ ω₀) ^ 2 ≤ c0 * (ε ^ ω₀) ^ 2 :=
        mul_le_mul_of_nonneg_right hpc (by positivity)
    _ ≤ c0 * (r ^ 2 / 100) := mul_le_mul_of_nonneg_left hx hc0.le
    _ = c0 * r ^ 2 / 100 := by ring

/-- **μ has no atoms, almost surely.** From the area parametrization `μ(η[a,b]) = b - a` and the surjectivity of `η`:
each point `η t` lies in `η[t-δ, t+δ]`, of mass `2δ` for every `δ > 0`. -/
theorem ae_null_singleton_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, ∀ v : ℂ, S.μ ω {v} = 0 :=
  hS.isAreaParametrized.mono fun ω hap v => by
    obtain ⟨-, -, hsurj, hmeas⟩ := hap
    obtain ⟨t, rfl⟩ := hsurj v
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hδ : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
    have key : S.μ ω {S.η ω t} ≤ ENNReal.ofReal (2 * ((ε : ℝ) / 2)) := by
      calc S.μ ω {S.η ω t} ≤ S.μ ω (S.η ω '' Icc (t - (ε : ℝ) / 2) (t + (ε : ℝ) / 2)) :=
            measure_mono (singleton_subset_iff.mpr ⟨t, ⟨by linarith, by linarith⟩, rfl⟩)
        _ = ENNReal.ofReal ((t + (ε : ℝ) / 2) - (t - (ε : ℝ) / 2)) := hmeas _ _ (by linarith)
        _ = ENNReal.ofReal (2 * ((ε : ℝ) / 2)) := by ring_nf
    rw [show 2 * ((ε : ℝ) / 2) = (ε : ℝ) by ring, ENNReal.ofReal_coe_nnreal] at key
    simpa using key

/-- **μ is finite on compacts, almost surely.** The LQG measure is a.s. a limit of the locally finite measures
`IsLQGLimit` (Harmonic-Balls-LQG, HarmonicBalls/Defs/LQG.lean:53, field `isLocallyFiniteMeasure`), and
`S.isLQGMeasure` is the a.s. statement of that limit for every `ω`. -/
theorem ae_finite_on_compacts_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, IsFiniteMeasureOnCompacts (S.μ ω) :=
  Filter.Eventually.mono hS.isLQGMeasure fun ω hω => by
    have := hω.isLocallyFiniteMeasure
    infer_instance

/-- **The pointwise one-test input with the r-free environment facts pointwise**.
Weaker than `ShellOneTestPointwiseStmt` (ShellCoreR68.lean): at `ω` it also assumes that `η ω` is continuous, that
`μ ω` has no atoms and that `μ ω` is finite on compacts (the environment facts `hηc`, `hμNull`, `hμFin`,
taken pointwise). They hold almost surely for a valid environment
(`ae_continuous_eta`, `ae_null_singleton_of_valid`, `ae_finite_on_compacts_of_valid`), so the swap below discharges them.
Named input, not frozen. -/
def ShellOneTestPointwiseEnvStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      ∀ ε : ℝ, 0 < ε → ∀ ω : Ω, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        Continuous (S.η ω) → (∀ v : ℂ, S.μ ω {v} = 0) → IsFiniteMeasureOnCompacts (S.μ ω) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The countable swap for the environment-pointwise input.** The window avoidance is almost surely at the dyadic
scales (`ae_all_iff` over `ℕ`, from `hav`), and the r-free environment facts are almost surely true (from `hS`); so the
pointwise input gives `ShellOneTestOrderAeStmt` with all radii inside `∀ᵐ ω`. -/
theorem shellOneTestOrderAeStmt_of_pointwiseEnv {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestPointwiseEnvStmt 𝒮) :
    ShellOneTestOrderAeStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, ae_null_singleton_of_valid hS,
    ae_finite_on_compacts_of_valid hS] with ω hω hηc hμN hμF hmesh hcurve hmult
  exact hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp ε hε ω hmesh hcurve hmult
    hηc hμN hμF hω

/-! ### The start cell meets the frontier of the thickened fill (`hstart`), from admissibility

The start binder `hstart` of `shellOrderAe_window` (ShellOrderWindow68.lean) follows from the first conjunct of
`Admissible` (`2 dd ≤ r ≤ 2 ddMax`, S6e/Admissible.lean:46): `dd`, `ddMax` are the infimum and supremum of
`dist(η q, K)` over the rational parameters of the start cell (S6e/Geometry.lean:33-42), and `K` is the fill. -/

/-- The rational-sample distance is the distance to the filled set: `pointDist ε η Θ q = Metric.infEDist (η q) (fillCells …)`.
The samples `η q'` (rational `q'` in the cells `w ∈ Θ`) are dense in the fill, by continuity of `η`. -/
theorem pointDist_eq_infEdist {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (q : ℚ) :
    Lemma68Geometry.pointDist ε η Θ q = Metric.infEDist (η q) (fillCells ε η ↑Θ) := by
  set T : Set ℂ := ⋃ w : Θ, ⋃ t : Lemma68Geometry.ratInt ε w.1, {η ((t : ℚ) : ℝ)} with hT
  have hTK : T ⊆ fillCells ε η ↑Θ := by
    intro y hy
    simp only [hT, mem_iUnion, mem_singleton_iff] at hy
    obtain ⟨w, t, rfl⟩ := hy
    refine mem_iUnion₂.mpr ⟨w.1, Finset.mem_coe.mpr w.2, ?_⟩
    exact ⟨((t : ℚ) : ℝ), t.2, rfl⟩
  -- density of the rational parameters in each closed cell interval
  have hD : ∀ w : ℤ, ∀ x ∈ Icc (ε * ((w : ℝ) - 1)) (ε * w),
      x ∈ closure (Ioo (ε * ((w : ℝ) - 1)) (ε * w) ∩ range (Rat.cast : ℚ → ℝ)) := by
    intro w x hx
    have hab : ε * ((w : ℝ) - 1) ≠ ε * w := by
      have : ε * ((w : ℝ) - 1) < ε * w := mul_lt_mul_of_pos_left (by linarith) hε
      exact this.ne
    have h1 : Ioo (ε * ((w : ℝ) - 1)) (ε * w) ⊆
        closure (Ioo (ε * ((w : ℝ) - 1)) (ε * w) ∩ range (Rat.cast : ℚ → ℝ)) :=
      Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
    have hx' : x ∈ closure (Ioo (ε * ((w : ℝ) - 1)) (ε * w)) := by
      rw [closure_Ioo hab]
      exact hx
    exact closure_minimal h1 isClosed_closure hx'
  have hTcl : ∀ w : ℤ, w ∈ Θ → ∀ x ∈ Icc (ε * ((w : ℝ) - 1)) (ε * w), η x ∈ closure T := by
    intro w hw x hx
    refine map_mem_closure hη (hD w x hx) ?_
    intro y hy
    obtain ⟨hyI, q', rfl⟩ := hy
    simp only [hT, mem_iUnion, mem_singleton_iff]
    refine ⟨⟨w, hw⟩, ⟨q', ⟨hyI.1.le, hyI.2.le⟩⟩, rfl⟩
  have hKcl : fillCells ε η ↑Θ ⊆ closure T := by
    intro y hy
    obtain ⟨w, hw, hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact hTcl w (Finset.mem_coe.mp hw) s hs
  have hpd : Lemma68Geometry.pointDist ε η Θ q = Metric.infEDist (η q) T := by
    simp only [Lemma68Geometry.pointDist, hT, Metric.infEDist_iUnion, Metric.infEDist_singleton]
  rw [hpd]
  apply le_antisymm
  · calc Metric.infEDist (η q) T = Metric.infEDist (η q) (closure T) := (Metric.infEDist_closure).symm
      _ ≤ Metric.infEDist (η q) (fillCells ε η ↑Θ) := Metric.infEDist_anti hKcl
  · exact Metric.infEDist_anti hTK

/-- **The start cell meets the frontier of the thickened fill, from admissibility.** At a fixed radius `r > 0` with
`2 dd(a) ≤ r ≤ 2 ddMax(a)` (the first conjunct of `Admissible`), the continuous function `t ↦ dist(η t, K)` (with
`K = fillCells`) takes the value `r/2` on the start cell `η[ε(a-1), εa]`: the infimum and supremum over the cell are
attained (compactness), and the intermediate value theorem applies on the connected cell interval. The frontier of
`thickening (r/2) K` is `{dist(·, K) = r/2}` (`frontier_thickening_eq`, S6n.lean:56), `K` being compact and nonempty. -/
theorem start_frontier_of_admissible {η : ℝ → ℂ} (hη : Continuous η) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (Θ : Finset ℤ) (a : ℤ) (hK : (fillCells ε η ↑Θ).Nonempty)
    (h1 : 2 * Lemma68Admissible.dd ε η Θ a ≤ r) (h2 : r ≤ 2 * Lemma68Admissible.ddMax ε η Θ a) :
    (cell ε η a ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty := by
  set K := fillCells ε η ↑Θ with hKdef
  have hKc : IsCompact K :=
    (Finset.finite_toSet Θ).isCompact_biUnion fun w _ => isCompact_Icc.image hη
  have hfr := Lemma68C12Geom.frontier_thickening_eq hKc hK (half_pos hr)
  have hIle : ε * ((a : ℝ) - 1) ≤ ε * a := mul_le_mul_of_nonneg_left (by linarith) hε.le
  set I : Set ℝ := Icc (ε * ((a : ℝ) - 1)) (ε * a) with hIdef
  have hIne : I.Nonempty := nonempty_Icc.mpr hIle
  set g : ℝ → ℝ := fun t => Metric.infDist (η t) K with hgdef
  have hg : Continuous g := (Metric.continuous_infDist_pt K).comp hη
  obtain ⟨t0, ht0I, ht0⟩ := isCompact_Icc.exists_isMinOn hIne hg.continuousOn
  obtain ⟨t1, ht1I, ht1⟩ := isCompact_Icc.exists_isMaxOn hIne hg.continuousOn
  have hfin : ∀ x : ℂ, Metric.infEDist x K ≠ ⊤ := fun x => by obtain ⟨y, hy⟩ := hK; exact ne_top_of_le_ne_top (edist_ne_top x y) (Metric.infEDist_le_edist_of_mem hy)
  have hgeq : ∀ x : ℂ, ENNReal.ofReal (Metric.infDist x K) = Metric.infEDist x K :=
    fun x => ENNReal.ofReal_toReal (hfin x)
  have hgnn : ∀ t : ℝ, 0 ≤ g t := fun t => Metric.infDist_nonneg
  have hpdq : ∀ q : ℚ, Lemma68Geometry.pointDist ε η Θ q = Metric.infEDist (η q) K :=
    fun q => pointDist_eq_infEdist hη hε Θ q
  -- (i) some cell point is at distance at most r/2 from K
  have hlo : ∃ t ∈ I, g t ≤ r / 2 := by
    by_contra hcon
    push Not at hcon
    have hgt0 : r / 2 < g t0 := hcon t0 ht0I
    have hlb : ∀ q ∈ Lemma68Geometry.ratInt ε a,
        ENNReal.ofReal (g t0) ≤ Lemma68Geometry.pointDist ε η Θ q := by
      intro q hq
      rw [hpdq q, ← hgeq (η q)]
      exact ENNReal.ofReal_le_ofReal (isMinOn_iff.mp ht0 (q : ℝ) hq)
    obtain ⟨q0, hq0a, hq0b⟩ := exists_rat_btwn (show ε * ((a : ℝ) - 1) < ε * a by linarith)
    have hne : Lemma68Geometry.cellDist ε η Θ a ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (iInf_le (fun q : Lemma68Geometry.ratInt ε a =>
        Lemma68Geometry.pointDist ε η Θ (q : ℚ)) ⟨q0, ⟨hq0a.le, hq0b.le⟩⟩)
      rw [hpdq q0]
      exact hfin _
    have hle : ENNReal.ofReal (g t0) ≤ Lemma68Geometry.cellDist ε η Θ a := by
      unfold Lemma68Geometry.cellDist
      exact le_iInf fun q => hlb (q : ℚ) q.2
    have hdd : g t0 ≤ Lemma68Admissible.dd ε η Θ a := by
      unfold Lemma68Admissible.dd
      have := ENNReal.toReal_mono hne hle
      rwa [ENNReal.toReal_ofReal (hgnn t0)] at this
    linarith
  -- (ii) some cell point is at distance at least r/2 from K
  have hhi : ∃ t ∈ I, r / 2 ≤ g t := by
    by_contra hcon
    push Not at hcon
    have hlt : g t1 < r / 2 := hcon t1 ht1I
    have hub : ∀ q ∈ Lemma68Geometry.ratInt ε a,
        Lemma68Geometry.pointDist ε η Θ q ≤ ENNReal.ofReal (g t1) := by
      intro q hq
      rw [hpdq q, ← hgeq (η q)]
      exact ENNReal.ofReal_le_ofReal (isMaxOn_iff.mp ht1 (q : ℝ) hq)
    have hsup : Lemma68Geometry.cellDistMax ε η Θ a ≤ ENNReal.ofReal (g t1) := by
      unfold Lemma68Geometry.cellDistMax
      exact iSup_le fun q => hub (q : ℚ) q.2
    have hmax : Lemma68Admissible.ddMax ε η Θ a ≤ g t1 := by
      unfold Lemma68Admissible.ddMax
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
      rwa [ENNReal.toReal_ofReal (hgnn t1)] at this
    linarith
  -- (iii) the intermediate value theorem on the cell interval
  obtain ⟨tlo, htloI, htlo⟩ := hlo
  obtain ⟨thi, lthiI, hthi⟩ := hhi
  have hmem : r / 2 ∈ g '' uIcc tlo thi :=
    intermediate_value_uIcc hg.continuousOn (Set.mem_uIcc.mpr (Or.inl ⟨htlo, hthi⟩))
  obtain ⟨s, hs, hgs⟩ := hmem
  have hsI : s ∈ I := uIcc_subset_Icc htloI lthiI hs
  refine ⟨η s, ⟨s, hsI, rfl⟩, ?_⟩
  rw [hfr]
  exact hgs

/-- **`hstart` at one environment, from the full admissibility guard.** For a continuous curve `η ω` (the a.s. fact
`TraceInputs68.ae_continuous_eta`), `ε > 0`, `r > 0`, `s₀ > 0`: `FullAdmAt` at `ω` gives the start-cell condition `hstart` of
`shellOrderAe_window` (ShellOrderWindow68.lean). The fill is nonempty since `ball 0 s₀ ⊆ fillCells` (ConfigOK). -/
theorem hstart_of_fullAdmAt {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ρ s₀ γ ε r s1 : ℝ} (ω : Ω)
    (i : Lemma68Config.Config68) (hη : Continuous (S.η ω)) (hε : 0 < ε) (hr : 0 < r) (hs₀ : 0 < s₀)
    (h : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i) :
    (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty := by
  obtain ⟨hcfg, hadm⟩ := h
  have hK : (fillCells ε (S.η ω) ↑i.Θ).Nonempty :=
    ⟨0, hcfg.2.2 (Metric.mem_ball_self hs₀)⟩
  exact start_frontier_of_admissible hη hε hr i.Θ i.a hK hadm.1.1 hadm.1.2

/-- **`hstart` almost surely, for every radius** (the binder `hstart` of `shellOrderAe_window`, ShellOrderWindow68.lean): for a valid
environment the start-cell condition holds almost surely on the event `FullAdmAt`, with no further hypothesis. -/
theorem hstart_ae_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ρ s₀ ε r s1 : ℝ} (i : Lemma68Config.Config68)
    (hε : 0 < ε) (hr : 0 < r) (hs₀ : 0 < s₀) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
  (TraceInputs68.ae_continuous_eta hS).mono fun ω hω h => hstart_of_fullAdmAt S ω i hω hε hr hs₀ h

/-! ### The Eps pointwise input and its assembly to `ShellChainCoreEpsStmt`

Eps analogue of `ShellOneTestPointwiseEnvStmt`: the premises and conclusion of `ShellOneTestOrderAeEpsStmt`
(ShellHoneInst68.lean:233), with the window avoidance at the dyadic scales `(1/2)^k` (pointwise in `ω`), the r-free
environment facts pointwise at `ω`, and `ε ≤ shellEps0Z γ α ω₀ ζ` for the ε-clause. Named input, not frozen. -/

/-- **The Eps pointwise one-test input** (named). -/
def ShellOneTestPointwiseEpsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0Z γ α ω₀ ζ → ∀ ω : Ω, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        Continuous (S.η ω) → (∀ v : ℂ, S.μ ω {v} = 0) → IsFiniteMeasureOnCompacts (S.μ ω) →
        (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) →
        (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) →
        (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The countable swap for the Eps pointwise input.** The dyadic window avoidance is almost surely at all scales
(`ae_all_iff` over `ℕ`, from `hav`), and the r-free environment facts are almost surely true (from `hS`). -/
theorem shellOneTestOrderAeEpsStmt_of_pointwiseEps {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestPointwiseEpsStmt 𝒮) :
    ShellOneTestOrderAeEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hεe
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, ae_null_singleton_of_valid hS,
    ae_finite_on_compacts_of_valid hS, MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hmesh hcurve hmult
  exact hcl R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp ε hε hεe ω hmesh hcurve hmult
    hηc hμN hμF hdg hadjA hadjAll hω

/-- **`ShellChainCoreEpsStmt` from the Eps pointwise input** (through `shellOneTestOrderAeEpsStmt_of_pointwiseEps` and
`shellChainCoreEpsStmt_of_oneTestOrderEps`, ShellHoneInst68.lean:275). -/
theorem shellChainCoreEpsStmt_of_pointwiseEps {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestPointwiseEpsStmt 𝒮) :
    ShellChainCoreEpsStmt 𝒮 :=
  shellChainCoreEpsStmt_of_oneTestOrderEps (shellOneTestOrderAeEpsStmt_of_pointwiseEps h)

/-! ### Radius-uniform binder statements of the one-radius assembly

The one-radius assembly (B1Assembly68.lean) is the body at one environment `ω` and one radius `r`. Its binders `hεcell`,
`hmesh`, `hEl`, ... are statements at fixed `(ω, r, i)`. The `ShellRes…` below state such binders in r-uniform form: they
quantify over all parameters of `ShellOneTestPointwiseEpsStmt` and assume `ShellPtPrem`, which is exactly the premise
list of that Stmt at `(ω, r)`. -/

section GoodEnvReduction

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly

/-- The premises of `ShellOneTestPointwiseEpsStmt` at one scale `ε`, one radius `r` with `10 ε^ω₀ ≤ r ≤ R`, and one
environment `ω` (`RegularEnvAt68`). The residual binders may use all of them. -/
def ShellPtPrem (𝒮 : SpaceFillingSLEModel) (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Ew : ℝ → Set Ω) (ω : Ω) : Prop :=
  0 < γ ∧ γ < 2 ∧ 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    2 * ω₀ * chosenBetaMinus γ < α ∧ 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    0 < CG ∧ 0 < CE ∧ 0 < ζ ∧ ζ < 1 / 2 ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < C ∧
    0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ∧
    0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧
    (∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) ∧
    0 < s₀ ∧ s₀ < 1 ∧ S.IsValid 𝒮 γ ∧ 0 < ε ∧ ε ≤ shellEps0Z γ α ω₀ ζ ∧
    10 * ε ^ ω₀ ≤ r ∧ r ≤ R ∧ ω ∈ Ew (dyadicD r) ∧ RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω

/-- Residual `hmesh` (GAP 2): the cell-diameter bound at the scale `dyadicD r` over ALL cells
(`Set.univ`). The paper's `h_ε` (corrected l.2995-2996) is a supremum over cells meeting `B_ρ` only. -/
def ShellResMesh (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (_i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ

/-- Residual `hRbd`: the window radius is bounded on the shell exits. -/
def ShellResRbd (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s'

/-- Residual `hRr` (`hRr_ae_setup_final` gives the almost-sure form, which needs `hmesh` almost surely,
hence GAP 2). -/
def ShellResRr (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1

/-- Residual `hVolC` (`HVolFullPw68`, uncommitted): the volume lower bound on the shell exits (constants `c₀`, `β⁻`). -/
def ShellResVolC (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((shellC068 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ chosenBetaMinus γ)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (shellC068 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))

/-- Residual `hVolY` (`HVolFullPw68`, uncommitted): the volume lower bound on the balls of the eligible annulus. -/
def ShellResVolY (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ chosenBetaMinus γ)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4))

/-- Residual `hGreen` (`B1EnvPw68`; uncommitted; the fixed-`η` lower Green bound; Lemma 2.16).
The constant `K.C` must be `CG` (GAP 3; `shellK68` still has `C := 1`). -/
def ShellResGreen (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r' : ℝ, ε ^ ω₀ ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          (1 : ℝ)⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b

/-- Residual `hCountGood` (`B1EnvPw68`; uncommitted; the lower half of the counting bound; Lemma 2.9 at `f ≡ 1`). -/
def ShellResCountGood (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ)

/-- Residual `hCellGood` (`HoneCellGoodSelPw68.hCellGood_fixedOmega`, waits for
the `meshEventR` at `rhoCell68 ρ`). Its radius is `rhoCell68 ρ`, which exceeds `ρ`, so it is not the
`cellSizeEvent68 S γ ζ ρ` of the Stmt (`ball 0 ρ`): a radius mismatch to report. -/
def ShellResCellGood (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)

/-- Residual `hRcell` (`B1EnvPw68`, uncommitted): the shell centres lie in the cell-good annulus. -/
def ShellResRcell (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ

/-- Residual `hx1` (`HoneMomSPw68.hx1_fixedOmega`; committed 483b650; at `rhoMom`; waits for goodEnv_loc): the exit vertex lies inside the ball of radius `1 - (window)/4`. -/
def ShellResX1 (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4

/-- Residual `hmomS` (`HoneMomSPw68.hmomS_pointwise`; committed: ball `0 ρ`; not `0 1`; F4 / goodEnv_loc):
the exit-time moment bound on the sub-balls of `B_1` (constant `C_E`). -/
def ShellResMomS (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N

/-- Residual `hWalk` (`B1EnvPw68`, uncommitted): the walk exits in the cell-vertex set of `B_{ρ - ε^ω₀}`
with the window-radius bounds. GAP 4: the second conjunct becomes `ε ^ (2/(2+γ)^2 - ζ) ≤ R / 8`. -/
def ShellResWalk (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) ∧
            ε ^ ω₀ ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ)

/-- Residual `hsel` (`HoneCellGoodSelPw68.hsel_fixedOmega`; committed 18d7880; F1: needs `C ≤ CG`): the good-annulus event at each short-eligible centre (constant `c₀`, `C_G`). -/
def ShellResSel (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) shellC068 CG (winRf S ρ ζ C r ω z) z

/-- Residual `hfull` (`HVolFullPw68`, uncommitted): every ball has positive `μ`-mass. -/
def ShellResFull (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPrem 𝒮 γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)

end GoodEnvReduction


#print axioms MatedCRT.Lemma68ShellCorePw.shellOneTestOrderAeEpsStmt_of_pointwiseEps
#print axioms MatedCRT.Lemma68ShellCorePw.shellChainCoreEpsStmt_of_pointwiseEps

end Lemma68ShellCorePw
end MatedCRT

#print axioms MatedCRT.Lemma68ShellCorePw.ae_forall_dyadicD
#print axioms MatedCRT.Lemma68ShellCorePw.cellDiam_ae_dyadicD
#print axioms MatedCRT.Lemma68ShellCorePw.eps_pow_le_of_small
#print axioms MatedCRT.Lemma68ShellCorePw.ae_null_singleton_of_valid
#print axioms MatedCRT.Lemma68ShellCorePw.ae_finite_on_compacts_of_valid
#print axioms MatedCRT.Lemma68ShellCorePw.shellOneTestOrderAeStmt_of_pointwiseEnv
#print axioms MatedCRT.Lemma68ShellCorePw.pointDist_eq_infEdist
#print axioms MatedCRT.Lemma68ShellCorePw.start_frontier_of_admissible
#print axioms MatedCRT.Lemma68ShellCorePw.hstart_of_fullAdmAt
#print axioms MatedCRT.Lemma68ShellCorePw.hstart_ae_of_valid
