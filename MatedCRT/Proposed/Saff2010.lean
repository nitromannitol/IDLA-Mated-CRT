import Mathlib

/-!
# Staged literature inputs: logarithmic potential theory (E. B. Saff, arXiv:1010.3760v1)

Staged for independent source audit. These Props are promoted to `MatedCRT/External` only after the source check. Each Prop here is an explicit hypothesis, not a proof of the
cited statement. Nothing in this file is assumed by a numbered result.

Source: E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*, arXiv:1010.3760v1
(12 October 2010), Surveys in Approximation Theory 5 (2010), pp. 165-200. Printed page = PDF page + 164 in the arXiv file.
Locators, read from the arXiv PDF: Definition 2.3 and (2.6) on printed p. 179 (PDF p. 15); Theorem 2.4 and (2.7)-(2.8) on
p. 180 (PDF p. 16); (2.9)-(2.10) on p. 181 (PDF p. 17); domain assumptions on p. 186 (PDF p. 22); (a')-(c') and (3.7)-(3.8)
on p. 187 (PDF p. 23).

Printed texts (verbatim, LaTeX as printed):

* Definition 2.3, p. 179: "An extended real-valued function $f$ on an open set $D\subset\mathbb C$ is called
  superharmonic in $D$ if $f$ is not the constant function $+\infty$ and satisfies (i) $f$ is lower semi-continuous on
  $D$; (ii) the value of $f$ at any point $z_0\in D$ is not less than its average over any circle in $D$ centered at
  $z_0$; that is $f(z_0)\ge\frac1{2\pi}\int_0^{2\pi}f(z_0+re^{i\theta})\,d\theta$." (2.6)

* Theorem 2.4 (Riesz Decomposition), p. 180: "If $f$ is superharmonic in a domain $D$, then there exists a positive
  measure $\lambda$ supported on $D$ such that for every subdomain $D^*\subset D$ for which $\overline{D^*}\subset D$, we
  have $f(z)=h(z)+\int_D\log\frac1{|z-t|}\,d\lambda(t)$, $z\in D^*$, (2.7) where $h$ is harmonic in $D^*$." The positive
  measure in the smooth case is $d\lambda(t):=-\frac1{2\pi}\Delta f(t)\,dm_2(t)$, $t\in D$. (2.8)

* Equations (2.9)-(2.10), p. 181: "we identify $-\Delta f\,dm_2$ as the unique positive measure that satisfies
  $\int_D\phi(-\Delta f\,dm_2):=-\int_D f\,\Delta\phi\,dm_2$ (2.9) for all $C^\infty$ functions $\phi$ whose support is a
  compact subset of $D$." "... for any finite Borel measure $\mu$ with compact support there holds
  $\mu=-\frac1{2\pi}\Delta U^\mu$." (2.10), with $U^\mu(z)=\int\log\frac1{|z-t|}\,d\mu(t)$ (p. 180).

* Domain assumptions, p. 186: "It is useful to consider Green functions with poles at finite points of the plane. If $D$
  is a domain with $\operatorname{cap}(\partial D)>0$, $\partial D\subset\mathbb C$ compact, the Green function
  $g_D(z,\zeta)$ for $D$ with pole at $\zeta\in D$ is the unique real-valued function of $z$ satisfying"

* Conditions (a')-(c'), p. 187: "(a') $g_D(z,\zeta)$ is harmonic in $D\setminus\{\zeta\}$ and bounded outside any
  neighborhood of $\zeta$. (b') $g_D(z,\zeta)-\log\frac1{|z-\zeta|}=O(1)$ as $z\to\zeta$. (c') $\lim_{z\to w,\,z\in D}
  g_D(z,\zeta)=0$ for q.e. $w\in\partial D$." The pole-at-infinity relation is (3.7) on p. 187.

* Green potential, (3.8), p. 187: "If $\nu$ is a finite positive measure on $D$ with compact support in $\mathbb C$, we
  define $U^\nu_D(z):=\int g_D(z,\zeta)\,d\nu(\zeta)$, $z\in D$, (3.8) and note that $U^\nu_D\ge0$ in $D$ and $U^\nu_D$ is
  superharmonic in $D$ and harmonic in $D\setminus\operatorname{supp}(\nu)$. Furthermore, if $\nu$ has compact support in
  $D$, then $\lim_{z\to w,\,z\in D}U^\nu_D(z)=0$ for q.e. $w\in\partial D$."

Conventions of this staging, all recorded explicitly:
* Saff's kernel is `log(1/|z-t|)`, with the classical value `+∞` at the pole `t = z`. Lean's `Real.log 0 = 0` is not used:
  `saffLogPotential` is `EReal`-valued and has the pole convention. This differs from HB's `newtonKernelEReal` only by the
  normalisation `N = (2π)⁻¹ log(1/|x-y|)`, and by the Riesz measure identification `λ = ν/(2π)`.
* "q.e." (quasi-everywhere) means outside a set of logarithmic capacity zero. Capacity is not formalized in this
  repository, so the notion is a parameter `IsPolar : Set ℂ → Prop` of the Green characterization. A caller must
  instantiate it with the capacity-zero predicate. The Props below are not usable without that instantiation.
* Theorem 2.4 as printed quantifies over all superharmonic `f`, with `λ` any positive measure on `D`. Staged here is the
  special case used here: `λ` finite with compact support in `D`, and `λ` the Riesz measure of `f`
  through the distributional identity (2.9). The general printed form is not staged: for `D` bounded and `λ` of infinite
  mass, the integral in (2.7) need not converge. Example: `f(z) = -(1-|z|²)⁻¹` on the unit disc is superharmonic,
  with `-Δf` of infinite mass. This is a suspected printed-statement issue, not a Lean claim.
-/

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

namespace MatedCRT.Proposed

/-- Saff's logarithmic potential `U^μ(z) = ∫ log(1/|z-t|) dμ(t)` (p. 180), in `EReal`. The integrand is `+∞` at the pole
`t = z` (classical convention, not Lean's diagonal zero). The positive and negative parts are integrated separately.
For a finite measure with compact support the negative part is finite. -/
noncomputable def saffLogPotential (μ : Measure ℂ) (z : ℂ) : EReal :=
  (∫⁻ t, (if t = z then ⊤ else ENNReal.ofReal (Real.log (1 / ‖z - t‖))) ∂μ).toEReal -
    (∫⁻ t, (if t = z then 0 else ENNReal.ofReal (Real.log ‖z - t‖)) ∂μ).toEReal

/-- The circle average `(2π)⁻¹ ∫₀^{2π} f(z₀ + r e^{iθ}) dθ` of an extended real-valued function, as an element of `EReal`.
The positive and negative parts are integrated separately (Definition 2.3(ii), p. 179). -/
noncomputable def saffCircleAverage (f : ℂ → EReal) (z₀ : ℂ) (r : ℝ) : EReal :=
  (ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
      (f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).toENNReal).toEReal -
    (ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
      (-f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).toENNReal).toEReal

/-- Saff Definition 2.3 (p. 179): `f` is superharmonic in the open set `D` if `f` is not the constant `+∞`, is lower
semicontinuous on `D`, and `f(z₀)` is not less than its average over every circle in `D` centred at `z₀`. -/
def SaffSuperharmonicOn (D : Set ℂ) (f : ℂ → EReal) : Prop :=
  (¬ ∀ z ∈ D, f z = ⊤) ∧ LowerSemicontinuousOn f D ∧
    ∀ z₀ ∈ D, ∀ r : ℝ, 0 < r → sphere z₀ r ⊆ D → saffCircleAverage f z₀ r ≤ f z₀

/-- **Staged input: Saff Theorem 2.4 (Riesz decomposition), printed p. 180, (2.7)-(2.8), in the special case used here.** Let `D` be a bounded domain, `f` superharmonic in `D`, and `m` a finite positive measure with compact
support in `D`. Suppose `m` is the Riesz measure of `f` through the distributional identity (2.9) and (2.8):
`∫ φ dm = -(2π)⁻¹ ∫ f Δφ dm₂` for every smooth `φ` with compact support in `D`. Then for every subdomain `D'` with
`closure D' ⊆ D` there is a function `h`, harmonic on `D'`, with `f = h + U^m` on `D'`.
Source locators: Theorem 2.4 (p. 180), (2.7)-(2.8) (p. 180), (2.9) (p. 181). Uses: the representative
lemma `BoundedJensenRepresentativesStep` (`Proofs/Sec4/Prop42Closure/BoundedRepresentatives.lean`). -/
def SaffRieszDecompositionLocalStmt : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → EReal) (m : Measure ℂ), IsOpen D → IsConnected D → Bornology.IsBounded D →
    SaffSuperharmonicOn D f → IsFiniteMeasure m → (∃ K ⊆ D, IsCompact K ∧ m Kᶜ = 0) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
        ∫ t, φ t ∂m = -(1 / (2 * Real.pi)) * ∫ z, (f z).toReal * Laplacian.laplacian φ z) →
    ∀ D' : Set ℂ, IsOpen D' → IsConnected D' → closure D' ⊆ D →
      ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h D' ∧
        ∀ z ∈ D', f z = (h z : EReal) + saffLogPotential m z

/-- **Staged input: the potential identity (2.10), printed p. 181.** For a finite Borel measure `m` with compact support,
`m = -(2π)⁻¹ Δ U^m` in the distributional sense: `∫ φ dm = -(2π)⁻¹ ∫ U^m Δφ dm₂` for every smooth `φ` with compact support.
Source locator: (2.10), printed p. 181 (PDF p. 17). -/
def SaffLogPotentialLaplacianStmt : Prop :=
  ∀ (m : Measure ℂ), IsFiniteMeasure m → (∃ K : Set ℂ, IsCompact K ∧ m Kᶜ = 0) →
    ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ t, φ t ∂m = -(1 / (2 * Real.pi)) * ∫ z, (saffLogPotential m z).toReal * Laplacian.laplacian φ z

/-- The Green conditions (a')-(c') of Saff p. 187 for a real function `g` on `ℂ` with pole `ζ` in the domain `D`.
`IsPolar` is the capacity-zero notion behind "q.e." (a parameter; see the module docstring). Only the values of `g` on `D`
are constrained. -/
def SaffGreenConditions (IsPolar : Set ℂ → Prop) (D : Set ℂ) (ζ : ℂ) (g : ℂ → ℝ) : Prop :=
  (InnerProductSpace.HarmonicOnNhd g (D \ {ζ}) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ z ∈ D, ε ≤ dist z ζ → |g z| ≤ M) ∧
    Asymptotics.IsBigO (𝓝 ζ) (fun z => g z - Real.log (1 / ‖z - ζ‖)) (fun _ => (1 : ℝ)) ∧
    ∃ E : Set ℂ, IsPolar E ∧ ∀ w ∈ frontier D \ E, Tendsto g (𝓝[D] w) (𝓝 0)

/-- **Staged input: the Green characterization, printed pp. 186-187 with the domain assumptions of p. 186.** For a domain
`D` with `∂D` compact and non-polar (`cap(∂D) > 0`, printed p. 186) and a pole `ζ ∈ D`, there is a function satisfying
(a')-(c'), and any two such functions agree on `D`. The uniqueness is the printed "unique real-valued function of `z`".
Source locators: p. 186 (domain assumptions and definition), p. 187 (a')-(c'). Not used by a numbered result. -/
def SaffGreenCharacterizationStmt (IsPolar : Set ℂ → Prop) : Prop :=
  ∀ (D : Set ℂ) (ζ : ℂ), IsOpen D → IsConnected D → Bornology.IsBounded D → ζ ∈ D → ¬ IsPolar (frontier D) →
    (∃ g : ℂ → ℝ, SaffGreenConditions IsPolar D ζ g) ∧
      ∀ g₁ g₂ : ℂ → ℝ, SaffGreenConditions IsPolar D ζ g₁ → SaffGreenConditions IsPolar D ζ g₂ →
        ∀ z ∈ D, g₁ z = g₂ z

end MatedCRT.Proposed
