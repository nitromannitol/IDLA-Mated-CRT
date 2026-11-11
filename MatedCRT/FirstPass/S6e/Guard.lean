import Mathlib
import MatedCRT.FirstPass.S6h
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6e.Final
import MatedCRT.FirstPass.S4S6c.Uniform68Env

/-!
# FIRST PASS: the guarded exit bound of Lemma 6.8 from the concrete configuration lemma

`Lemma68Concrete.configuration_le_pow_concrete` (`FirstPass/S6h/Schedule.lean`) gives the configuration bound
`∃ N, r^(-ζ)/200 ≤ N ∧ exitQ ≤ (1 - q₀/(1+log(1/r))²)^N` on the admissible configurations, from the per-state
inputs `StateTestInputs` (write-up C4) and the containment `ConcreteC12` (write-up C12), both on `E ε ∩ G`.
This file turns that bound into the probability statement `probTendsToOne_guard_concrete` (write-up (17)), with
`probTendsToOne_uniform_half_guarded` (`S6e/Final.lean`). The hypothesis `hsch` of `probTendsToOne_lemma68_guarded`
is therefore no longer needed.

Named inputs (Props, not proved here): `ConcreteGuardInputStmt 𝒮` only, namely the per-state test inputs
`StateTestInputs` (C4) and the cell-size mesh condition `hmesh` (cells meeting `B_ρ` have diameter at most
`Delta p r / 100` for `r ≥ 10 ε^ω₀`), each on events `E ε ∩ G` with `P(E ε)ᶜ → 0` and `P(Gᶜ) = 0`.
Derived here: the containment C12 (`Lemma68Config.probTendsToOne_lemma68_concrete`, which proves C12 from
`Lemma68Concrete.concreteC12_killed`), the environment regularity (`Uniform68Env.ae_envInputs`: continuity and
properness of `η`, adjacency of cells), the local finiteness and consecutive adjacency of the multiplicities
(`Uniform68Env.envAt`), and the cap `R ≤ ρ/100` (by replacing `R` and `dd` with their minima with `ρ/100`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Guard

open Lemma68Config Lemma68Concrete Lemma68Final

/-- The guarded probability bound (write-up (17)) from the concrete configuration lemma. -/
theorem probTendsToOne_guard_concrete {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ : ℝ)
    {E : ℝ → Set Ω} (hE : ProbTendsToOne S.P E) {G : Set Ω} (hG : S.P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε) {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R)
    {ζ p qStar q0 c0 : ℝ} (good : ℝ → Ω → ℂ → ℕ → Prop)
    (hq0def : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq1s : qStar ≤ 1) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hpζ : p = 2 * ζ + 2) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1)
    (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hR1000 : R ≤ (1000 : ℝ) ^ (-1 / ζ)) (hc0 : c0 < 1 / 8)
    (hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hstate : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good)
    (hC12 : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}) :=
  probTendsToOne_uniform_half_guarded hE hG hα hdd hq0 hq1 hζ hζ' hR
    (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S)
    (configuration_le_pow_concrete S ρ s₀ γ E G α dd R ζ p qStar q0 c0 good hq0def hq hq1s hq9 hp hpζ hζ hα hdd hR
      hR1000 hc0 hEnv hlf hstate hC12)

/-- The environment regularity used by the walk-level inputs, for one `ω`: `η` is continuous and proper, and for
every `ε > 0` adjacent vertices of the mated-CRT map have meeting cells (Duplantier-Sheffield mating of trees). -/
abbrev EnvRegular {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : Prop :=
  Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty

/-- `EnvRegular` holds almost surely (`Uniform68Env.ae_envInputs`, proved in the repository). -/
theorem ae_envRegular {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    S.P {ω | ¬ EnvRegular S ω} = 0 :=
  ae_iff.1 (Uniform68Env.ae_envInputs hγ0 hγ2 hS)

/-- Named input (probabilistic content of write-up C4 and of the cell-size mesh, for each valid environment): there
are a radius `dd` and events `E`, `G` with `P(E)` tending to one and `P(Gᶜ) = 0`, on which the per-state inputs
`StateTestInputs` (C4) and the mesh condition `hmesh` (cells meeting `B_ρ` have diameter at most
`min (Delta p r / 100) (c0 * Delta p r)` for `r ≥ 10 ε^ω₀`, the form of `Lemma68Config.probTendsToOne_lemma68_concrete`)
hold, with the guard radius `α ε = 10 ε^ω₀`. Not proved here. The regularity of `η`, the local
finiteness of the multiplicities and the containment C12 are derived (see `guardProb_of_concrete`). -/
def ConcreteGuardInputStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ R ζ p qStar q0 c0 : ℝ, 0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧ R ≤ (1000 : ℝ) ^ (-1 / ζ) ∧
    0 < ζ ∧ ζ < 1 / 2 ∧ 0 < q0 ∧ q0 ≤ 1 ∧ q0 = qStar / 9 ∧ 0 ≤ qStar ∧ qStar ≤ 1 ∧ qStar ≤ 9 ∧
    p ≤ 3 ∧ p = 2 * ζ + 2 ∧ c0 < 1 / 8 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ R) ∧
  ∃ (E : ℝ → Set Ω) (G : Set Ω) (good : ℝ → Ω → ℂ → ℕ → Prop),
    ProbTendsToOne S.P E ∧ S.P Gᶜ = 0 ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ Metric.ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) k) ≤ min (Lemma68Scales.Delta p r / 100) (c0 * Lemma68Scales.Delta p r)) ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good)

/-- The guarded exit bound as a probability statement, for every valid environment (write-up (17)); the form used by
`Lemma68Uniform.uniform_of_guard` (S6e/Uniform.lean). -/
def GuardProbStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ R ζ p qStar q0 : ℝ, 0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧
    0 < ζ ∧ ζ < 1 / 2 ∧ 0 < q0 ∧ q0 ≤ 1 ∧ q0 = qStar / 9 ∧ 0 ≤ qStar ∧ qStar ≤ 9 ∧ p ≤ 3 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ R) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}

/-- The concrete input gives the guard probability statement `GuardProbStmt`. The cap `R ≤ ρ/100` required by the
configuration lemma is obtained by replacing `R` and `dd` with `min R (ρ/100)` and `min dd (min R (ρ/100))`. -/
theorem guardProb_of_concrete (𝒮 : SpaceFillingSLEModel) (hC : ConcreteGuardInputStmt 𝒮) :
    GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hc⟩ := hC γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨R, ζ, p, qStar, q0, c0, hR0, hRρ4, hRz, hR1000, hζ0, hζ1, hq00, hq01, hq0d, hq0', hq1s, hq9, hp3,
    hpζ, hc0, hc2⟩ := hc ρ hρ0 hρ1
  refine ⟨min R (ρ / 100), ζ, p, qStar, q0, lt_min hR0 (by positivity), (min_le_right _ _).trans (by linarith),
    (min_le_left _ _).trans hRz, hζ0, hζ1, hq00, hq01, hq0d, hq0', hq9, hp3, ?_⟩
  intro s₀ hs₀0 hs₀1 Ω _ S hS
  obtain ⟨dd, hdm, hdpos, hddR, E, G, good, hE, hG, hmesh, hstate⟩ := hc2 s₀ hs₀0 hs₀1 Ω S hS
  have hG' : S.P (G ∩ {ω | EnvRegular S ω})ᶜ = 0 := by
    rw [Set.compl_inter]
    exact measure_union_null hG (ae_envRegular hγ0 hγ2 hS)
  have hsub : ∀ ε : ℝ, ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}), ω ∈ E ε ∩ G ∧ EnvRegular S ω :=
    fun ε ω hω => ⟨⟨hω.1, hω.2.1⟩, hω.2.2⟩
  refine ⟨fun ω => min (dd ω) (min R (ρ / 100)), hdm.min measurable_const,
    fun ω => lt_min (hdpos ω) (lt_min hR0 (by positivity)), fun ω => min_le_right _ _, ?_⟩
  have hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}),
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ) :=
    fun ε _ ω hω => ⟨(hsub ε ω hω).2.1, (hsub ε ω hω).2.2.1⟩
  have hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}),
      IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
    intro ε hε ω hω
    obtain ⟨h1, h2, -⟩ := Uniform68Env.envAt S hε ω (hsub ε ω hω).2.1 (hsub ε ω hω).2.2.1
      (fun ε' hε' j k hjk => (hsub ε ω hω).2.2.2 ε' hε' j k hjk)
    exact ⟨h1, h2⟩
  have hadj : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}), ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun ε hε ω hω j k hjk => (hsub ε ω hω).2.2.2 ε hε j k hjk
  have hmesh' : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}), ∀ r : ℝ,
      10 * ε ^ ω₀ ≤ r → r ≤ min (dd ω) (min R (ρ / 100)) → ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ Metric.ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) k) ≤ min (Lemma68Scales.Delta p r / 100) (c0 * Lemma68Scales.Delta p r) :=
    fun ε hε ω hω r h1 h2 => hmesh ε hε ω (hsub ε ω hω).1 r h1 (h2.trans (min_le_left _ _))
  have hstate' : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ (G ∩ {ω | EnvRegular S ω}), ∀ r : ℝ,
      10 * ε ^ ω₀ ≤ r → r ≤ min (dd ω) (min R (ρ / 100)) → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
        ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good :=
    fun ε hε ω hω r h1 h2 i hi => hstate ε hε ω (hsub ε ω hω).1 r h1 (h2.trans (min_le_left _ _)) i hi
  exact Lemma68Config.probTendsToOne_lemma68_concrete (P := S.P) S ρ s₀ γ (E := E) hE
    (G := G ∩ {ω | EnvRegular S ω}) hG' (α := fun ε => 10 * ε ^ ω₀) (fun ε hε => by positivity)
    (dd := fun ω => min (dd ω) (min R (ρ / 100))) (R := min R (ρ / 100)) (fun ω => min_le_right _ _) good hρ0
    hs₀0 (min_le_right _ _) hq00 hq01 hζ0 hζ1 ((min_le_left _ _).trans hRz) ((min_le_left _ _).trans hR1000) hc0
    hq0d hq0' hq1s hq9 hp3 hpζ hEnv hlf hadj hmesh' hstate'

/-- Converse of `Geometry.tendsto_cocompact_of_escapes`: a curve that is proper for the cocompact filters escapes both
ends (`Lemma68Inputs.CurveEscapesBothEnds`, `S6e/Inputs.lean`). -/
theorem escapes_of_tendsto_cocompact {η : ℝ → ℂ}
    (h : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ)) :
    Lemma68Inputs.CurveEscapesBothEnds η := by
  intro R hR
  have hK : (Metric.closedBall (0 : ℂ) R)ᶜ ∈ Filter.cocompact ℂ :=
    (isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact
  have hev : ∀ᶠ t in Filter.cocompact ℝ, η t ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := h hK
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup, Filter.eventually_atBot, Filter.eventually_atTop] at hev
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hev
  refine ⟨max 1 (max (-a) b), lt_of_lt_of_le one_pos (le_max_left _ _), fun t ht => ?_⟩
  have hT1 : -a ≤ max 1 (max (-a) b) := (le_max_left _ _).trans (le_max_right _ _)
  have hTb : b ≤ max 1 (max (-a) b) := (le_max_right _ _).trans (le_max_right _ _)
  have hmem : η t ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht
      exact hb t (by linarith)
    · rw [abs_of_nonpos h0] at ht
      exact ha t (by linarith)
  simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hmem

/-- Almost surely `η` escapes both ends: the body of `EscapeAeStmt` (`S6e/Uniform.lean:143`), from the properness of
`η` almost surely (`IsValid.ae_tendsto_cocompact`). -/
theorem ae_escapes_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, Lemma68Inputs.CurveEscapesBothEnds (S.η ω) := by
  filter_upwards [hS.ae_tendsto_cocompact] with ω hω using escapes_of_tendsto_cocompact hω

/-- Almost surely, for every `ε > 0`, the multiplicities `S.mult ε ω` are locally finite with consecutive adjacency:
the body of `FiniteExitAeStmt` (`S6e/Uniform.lean:149`), from `Uniform68Env.ae_envInputs` and `Uniform68Env.envAt`. -/
theorem ae_finiteExit_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ0 hγ2 hS] with ω hω
  intro ε hε
  obtain ⟨h1, h2, -⟩ := Uniform68Env.envAt S hε ω hω.1 hω.2.1 hω.2.2
  exact ⟨h1, h2⟩

end Lemma68Guard

#print axioms MatedCRT.Lemma68Guard.guardProb_of_concrete
#print axioms MatedCRT.Lemma68Guard.ae_escapes_of_valid
#print axioms MatedCRT.Lemma68Guard.ae_finiteExit_of_valid

end MatedCRT
