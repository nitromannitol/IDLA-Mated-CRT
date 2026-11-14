import Mathlib
import LatticeProb.Prob.MarkovStepShiftedPath
import HarmonicBalls.Defs.Brownian

/-!
# Literature inputs: Revuz measures of additive functionals of planar Brownian motion and time changes

Berestycki–Gwynne (2020), Section 7 (Proposition 7.10, proof :3446–3622 of `2003.10320`) identifies the time change
of a Markovian time-changed planar Brownian motion through the Revuz measure of its positive continuous additive
functional (PCAF).  This file types the objects (`IsPCAF`, `revuz`, `clockInverse`, `GoodClock`, `IsInvTC`) for the
canonical planar Brownian motion `HarmonicBalls.planarBrownianMotion` and the three literature inputs used by the
assembly.

* `IsPCAF W A`: `A t ω` is a family of measurable `ℝ≥0`-valued functionals of the canonical path, adapted to the
  natural filtration up to `W z`-null sets, almost surely continuous, nondecreasing, vanishing at `0`, and additive
  `A (t + s) = A t + A s ∘ θ_t` (raw form, for every starting point `z` and every `s, t`, up to a null set).
* `revuz W A`: the explicit Revuz measure of `A` with respect to Lebesgue measure,
  `S ↦ ∫ dz E_z ∫_{(0,1]} 1_S(B_s) dA_s` (Revuz–Yor (1999), Chapter X, §2 with `m` = Lebesgue measure;
  Fukushima–Oshima–Takeda (2011), (5.1.13) with `h ≡ 1`).  It is built from the right-continuous rational-time
  regularization `regularize A` of `A`, which is a measurable functional for every path and equals `A` on the path
  set where `A` is continuous and nondecreasing (a set of full `W z` measure for every `z`).
* `clockInverse A u ω = inf {t | u < A t ω}`: the right inverse `τ_u` of the clock (the paper writes
  `inf {t : A_t = u}`, which agrees for a strictly increasing clock).
* `IsInvTC W A ν`: the time change `B ∘ τ` of `W` by `A` leaves `ν` invariant (Definition 7.3 for `P^A`).

The three Props are the literature inputs of the assembly of Proposition 7.10; they are TRUE as typed (desk answer
MQ-ft-6, verified by an independent check) and hold for the canonical planar Brownian motion, not for arbitrary
families `W`.  They take the place of the printed statements at :3452–3459 (a Revuz measure determines its PCAF),
which are false as printed.

* `RevuzUniquenessInput`: Fukushima–Oshima–Takeda (2011), 2nd ed., Theorem 5.1.4 (uniqueness part of the
  correspondence between PCAF classes and smooth measures), after perfection of the raw additive functional
  (Theorem 5.1.7; Revuz–Yor, Chapter X, remark after 2.9) and identification quasi-everywhere, which is
  Lebesgue-almost everywhere for planar Brownian motion.  The perfection step is part of the literature input.
* `RevuzInvariantInput`: Fukushima–Oshima–Takeda, Theorems 5.1.3 and 5.1.4 (the Revuz measure is smooth) and
  Theorem 6.2.1(i) (the time-changed process is symmetric with respect to the Revuz measure), with conservativeness
  of the good clock; Azéma–Duflo–Revuz (1969, Séminaire de Probabilités III, `numdam SPS_1969__3__24_0`),
  Proposition 3.2 (p. 31) for the invariant measure of the time change of a continuous `σ`-integrable additive
  functional, and Proposition 1.3 (p. 25) for the divergence dichotomy of additive functionals.  Scope: Fukushima–
  Oshima–Takeda §6.2 fixes a positive Radon measure; for a smooth, nowhere-Radon measure the Azéma–Duflo–Revuz
  route is the one that applies.
* `TimeChangeInvariantUniqueInput`: Azéma–Duflo–Revuz (1969), Proposition 3.2 (invariant measures of the time change
  are unique among excessive measures up to scale) and Theorem 2.5 (Harris uniqueness); Revuz–Yor (1999), Chapter X,
  Proposition 3.9 (p. 425, Harris criterion), Proposition 3.11 (p. 426, `μ_A ≠ 0 ⇒ A_∞ = ∞`), Theorem 3.12
  (pp. 427–428, ratio ergodic theorem) and Exercise 3.14 (p. 428, uniqueness up to scale); the strong Feller
  hypothesis of Revuz–Yor X §3 is used for planar Brownian motion only, not for the time change.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The planar Brownian laws `z ↦ P_z` on the canonical path space (generator `Δ / 2`). -/
noncomputable def planarLaw (z : ℂ) : Measure (ContinuousPath ℂ) :=
  HarmonicBalls.planarBrownianMotion z

/-- The natural `σ`-field `F⁰_t` of the canonical planar path up to time `t`. -/
noncomputable abbrev pathFiltration (t : ℝ≥0) : MeasurableSpace (ContinuousPath ℂ) :=
  ⨆ s ≤ t, MeasurableSpace.comap (fun ω : ContinuousPath ℂ => ω s) inferInstance

/-- **Positive continuous additive functional** of the canonical planar path under the laws `W z`
(Revuz–Yor (1999), X.1.1, raw form): measurable, adapted up to `W z`-null sets, almost surely continuous and
nondecreasing from `0`, and additive `A (t + s) = A t + A s ∘ θ_t` almost surely for every `z, s, t`, where
`θ_t ω = ω (t + ·)` is the time shift (`LatticeProb.pathShift`). -/
structure IsPCAF (W : ℂ → Measure (ContinuousPath ℂ)) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Prop where
  meas : ∀ t, Measurable (A t)
  adapted : ∀ z t, ∃ g : ContinuousPath ℂ → ℝ≥0, Measurable[pathFiltration t] g ∧ A t =ᵐ[W z] g
  path : ∀ z, ∀ᵐ ω ∂W z, A 0 ω = 0 ∧ Continuous (fun t => A t ω) ∧ Monotone (fun t => A t ω)
  add : ∀ z s t, ∀ᵐ ω ∂W z, A (t + s) ω = A t ω + A s (LatticeProb.pathShift ω t)

open scoped Classical in
/-- The right-continuous rational-time regularization of a functional `A`: for a path along which `A` is
nondecreasing on the nonnegative rationals, `t ↦ inf {A q ω : q ∈ ℚ≥0, q > t}`; for every other path, `0`.  It is a
countable infimum of measurable functionals, hence measurable in the path, and nondecreasing in `t` for every path. -/
noncomputable def regularize (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (t : ℝ≥0) (ω : ContinuousPath ℂ) : ℝ≥0 :=
  if ∀ p q : ℚ≥0, p ≤ q → A p ω ≤ A q ω then ⨅ q : {q : ℚ≥0 // t < (q : ℝ≥0)}, A (q.1 : ℝ≥0) ω else 0

open scoped Classical in
/-- The Lebesgue–Stieltjes function of a nondecreasing function `a : ℝ≥0 → ℝ≥0` (extended by `a 0` to the
negative half-line), and a default for non-monotone `a`. -/
noncomputable def stieltjesOfNNReal (a : ℝ≥0 → ℝ≥0) : StieltjesFunction ℝ :=
  if h : Monotone a then
    (show Monotone (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) from
      fun x y hxy => by exact_mod_cast h (Real.toNNReal_mono hxy)).stieltjesFunction
  else default

/-- The occupation measure of the path `ω` against the Stieltjes measure of the clock `a`, on `(0, 1]`:
`S ↦ ∫_{(0,1]} 1_S(ω_s) da_s`. -/
noncomputable def occupationMeasure (a : ℝ≥0 → ℝ≥0) (ω : ContinuousPath ℂ) : Measure ℂ :=
  (((stieltjesOfNNReal a).measure).restrict (Ioc (0 : ℝ) 1)).map (fun s : ℝ => ω s.toNNReal)

/-- **The Revuz measure of `A` with respect to Lebesgue measure** (Revuz–Yor (1999), X §2; Fukushima–Oshima–Takeda
(2011), (5.1.13) with `h ≡ 1`): `S ↦ ∫ dz E_z ∫_{(0,1]} 1_S(B_s) dA_s`, computed on the rational-time
regularization of `A`. -/
noncomputable def revuz (W : ℂ → Measure (ContinuousPath ℂ)) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Measure ℂ :=
  (volume : Measure ℂ).bind fun z =>
    (W z).bind fun ω => occupationMeasure (fun t => regularize A t ω) ω

/-- The right inverse of the clock: `τ_u ω = inf {t | u < A t ω}` (`sInf ∅ = 0` in `ℝ≥0`). -/
noncomputable def clockInverse (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) (ω : ContinuousPath ℂ) : ℝ≥0 :=
  sInf {t | u < A t ω}

/-- A good clock: almost surely, for every starting point, strictly increasing and unbounded. -/
def GoodClock (W : ℂ → Measure (ContinuousPath ℂ)) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Prop :=
  ∀ z, ∀ᵐ ω ∂W z, StrictMono (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop atTop

/-- The time change `B ∘ τ` of `W` by the clock `A` leaves the measure `ν` invariant (Definition 7.3 for `P^A`):
for every `u` and Borel set `S`, `∫ P_z[B_{τ_u} ∈ S] dν(z) = ν(S)`. -/
def IsInvTC (W : ℂ → Measure (ContinuousPath ℂ)) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (ν : Measure ℂ) : Prop :=
  ∀ (u : ℝ≥0) (S : Set ℂ), MeasurableSet S →
    ∫⁻ z, W z {ω | ω (clockInverse A u ω) ∈ S} ∂ν = ν S

/-- **Uniqueness of a PCAF with a given σ-finite Revuz measure** (Fukushima–Oshima–Takeda (2011), Theorem 5.1.4,
uniqueness part, after perfection of the raw additive functional; see the module docstring).  Two PCAFs of planar
Brownian motion whose Revuz measures with respect to Lebesgue measure agree and are `σ`-finite are
indistinguishable, for Lebesgue-almost every starting point. -/
def RevuzUniquenessInput : Prop :=
  ∀ A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw A → IsPCAF planarLaw A' →
    SigmaFinite (revuz planarLaw A) → revuz planarLaw A = revuz planarLaw A' →
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂planarLaw z, ∀ t, A t ω = A' t ω

/-- **The Revuz measure of a PCAF with a good clock is σ-finite and invariant for its time change**
(Fukushima–Oshima–Takeda (2011), Theorems 5.1.3–5.1.4 and 6.2.1(i); Azéma–Duflo–Revuz (1969), Proposition 3.2;
see the module docstring). -/
def RevuzInvariantInput : Prop :=
  ∀ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw A → GoodClock planarLaw A →
    SigmaFinite (revuz planarLaw A) ∧ IsInvTC planarLaw A (revuz planarLaw A)

/-- **Uniqueness of the invariant measure of the time change up to a constant** (Azéma–Duflo–Revuz (1969),
Proposition 3.2 and Theorem 2.5; Revuz–Yor (1999), Chapter X, Proposition 3.9, Theorem 3.12, Exercise 3.14; see the
module docstring): every `σ`-finite measure invariant for the time change of planar Brownian motion by a PCAF with a
good clock is a constant multiple of the Revuz measure of the PCAF. -/
def TimeChangeInvariantUniqueInput : Prop :=
  ∀ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw A → GoodClock planarLaw A →
    ∀ ν : Measure ℂ, SigmaFinite ν → IsInvTC planarLaw A ν →
      ∃ c : ℝ≥0, ν = (c : ℝ≥0∞) • revuz planarLaw A

/-- Sanity check: the deterministic clock `A t = t` is a PCAF under any family of laws. -/
theorem isPCAF_time (W : ℂ → Measure (ContinuousPath ℂ)) : IsPCAF W (fun t _ => t) where
  meas _ := measurable_const
  adapted _ t := ⟨fun _ => t, measurable_const, Filter.EventuallyEq.rfl⟩
  path _ := Filter.Eventually.of_forall fun _ => ⟨rfl, continuous_id, monotone_id⟩
  add _ s t := Filter.Eventually.of_forall fun _ => by simp [add_comm]

/-- Sanity check: the deterministic clock `A t = t` is a good clock. -/
theorem goodClock_time (W : ℂ → Measure (ContinuousPath ℂ)) : GoodClock W (fun t _ => t) :=
  fun _ => Filter.Eventually.of_forall fun _ => ⟨strictMono_id, tendsto_id⟩

/-- Sanity check: the rational-time regularization leaves the deterministic clock `A t = t` unchanged. -/
theorem regularize_time (t : ℝ≥0) (ω : ContinuousPath ℂ) : regularize (fun s _ => s) t ω = t := by
  have hmono : ∀ p q : ℚ≥0, p ≤ q → (p : ℝ≥0) ≤ (q : ℝ≥0) := fun p q hpq => by exact_mod_cast hpq
  have key : ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : {q : ℚ≥0 // t < (q : ℝ≥0)}, ((q.1 : ℚ≥0) : ℝ≥0) ≤ t + ε := by
    intro ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) < t + ε by simpa using hε)
    have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast (t.coe_nonneg.trans hr1.le)
    have hc : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (r : ℝ) := by
      rw [show (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (((r.toNNRat : ℚ≥0) : ℚ) : ℝ) from rfl,
        Rat.coe_toNNRat _ hr0]
    refine ⟨⟨r.toNNRat, ?_⟩, ?_⟩
    · rw [← NNReal.coe_lt_coe, hc]; exact hr1
    · rw [← NNReal.coe_le_coe, hc]; exact_mod_cast hr2.le
  have hne : Nonempty {q : ℚ≥0 // t < (q : ℝ≥0)} := ⟨(key 1 one_pos).choose⟩
  unfold regularize
  split_ifs with h
  · refine le_antisymm ?_ (le_ciInf fun q => q.2.le)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq⟩ := key ε hε
    exact (ciInf_le (OrderBot.bddBelow _) q).trans hq
  · exact absurd hmono h

end MatedCRT
