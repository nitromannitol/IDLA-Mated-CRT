import MatedCRT.FirstPass.S4S6c.ShellCoreR68
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Pointwise, radius-uniform inputs for the one-test order (fp-S4S6c-pointwise-r-uniform, z5)

Written argument (corrected draft, paper/idla_mated_crt-corrected.tex): dyadic Borel-Cantelli over the scales
`d = dyadicD r` (l.2866-2945); the intersection of the `ε`-events with `r² ≤ d < 2r²`, "uniform over `r`" (l.2995-3016);
one good-annulus test, pointwise (l.3033-3036).

* `ae_forall_dyadicD`: a binder `P (dyadicD r) ω` that holds almost surely at each dyadic scale holds almost surely at
  all radii at once (countable swap over `k : ℕ`; `dyadicD r = (1/2)^k` for `k = Nat.log 2 ⌊1/r²⌋₊`, by definition).
* `cellDiam_ae_dyadicD`: the mesh binder `hmesh` of `shellOneTest_ae_fixedR` (B1Assembly68.lean:81) through that swap.
  Its dyadic a.s. premise is a named input here: the binder is stated with `Set.univ`, stronger than the paper's `h_ε`
  (corrected l.2995-2996, the supremum over cells meeting `B_ρ`).
* `eps_pow_le_of_small`: the deterministic binder `hεcell` of `shellOneTest_ae_fixedR` (B1Assembly68.lean:86) for every
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

/-- **The mesh binder through the dyadic swap.** `hmesh` of `shellOneTest_ae_fixedR` (B1Assembly68.lean:81), i.e.
`CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ`, is almost surely true at all radii with `ω ∈ Ew (dyadicD r)` once its
dyadic form holds almost surely at each scale `(1/2)^k`. The dyadic premise `h` is NOT derived here (report). -/
theorem cellDiam_ae_dyadicD {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {Ew : ℝ → Set Ω} (ε : ℝ)
    (η : Ω → ℝ → ℂ)
    (h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → CellDiamLe ε (η ω) ((1 / 2 : ℝ) ^ k / 100) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ, ω ∈ Ew (dyadicD r) → CellDiamLe ε (η ω) (dyadicD r / 100) Set.univ :=
  ae_forall_dyadicD (P := fun d ω => CellDiamLe ε (η ω) (d / 100) Set.univ) h

/-- **The deterministic binder `hεcell` for all radii at once.** If `2 ω₀ < A` (the Eps chain condition
`2 ω₀ < 2/(2+γ)² - ζ` with `A = 2/(2+γ)² - ζ`), there is a threshold `e0 > 0` such that for `0 < ε ≤ e0` and every
`r ≥ 10 ε^{ω₀}`: `ε^A ≤ c0 r² / 100`. Here `c0 = K.c0` in `shellOneTest_ae_fixedR`. -/
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

/-- **The pointwise one-test input with the r-free environment facts pointwise** (fp-S4S6c-pointwise-r-uniform).
Weaker than `ShellOneTestPointwiseStmt` (ShellCoreR68.lean): at `ω` it also assumes that `η ω` is continuous, that
`μ ω` has no atoms and that `μ ω` is finite on compacts (the binders `hηc`, `hμNull`, `hμFin` of
`shellOneTest_ae_fixedR`, B1Assembly68.lean:88-93, taken pointwise). They hold almost surely for a valid environment
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

end Lemma68ShellCorePw
end MatedCRT

#print axioms MatedCRT.Lemma68ShellCorePw.ae_forall_dyadicD
#print axioms MatedCRT.Lemma68ShellCorePw.cellDiam_ae_dyadicD
#print axioms MatedCRT.Lemma68ShellCorePw.eps_pow_le_of_small
#print axioms MatedCRT.Lemma68ShellCorePw.ae_null_singleton_of_valid
#print axioms MatedCRT.Lemma68ShellCorePw.ae_finite_on_compacts_of_valid
#print axioms MatedCRT.Lemma68ShellCorePw.shellOneTestOrderAeStmt_of_pointwiseEnv
