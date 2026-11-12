import MatedCRT.FirstPass.Derived.ConeScaleRadiusLateral

/-!
# The rescaled radial process of a quantum cone is a function of the radial process

For a `γ`-quantum cone the radial pair `S = (t ↦ h_{e^{-t}}(0), s ↦ h_{e^s}(0))` determines almost surely the
cone scale radius `R_b` (`radScale`), and the radial pair of the rescaled field
`h(R_b ·) + Q log R_b - γ⁻¹ log b` reads `S` at the random radii `R_b e^{∓t}`.  Evaluation at a random radius is
not a measurable operation on arbitrary paths, but it is on continuous ones, as the limit of the evaluations at the
dyadic radii `⌈2^n x⌉ / 2^n`.  This gives a *measurable* map `radialRescale` of radial pairs with
`radialProcess (rescaled field) = radialRescale (radialProcess h)` almost surely, which is the form in which the
radial invariance of the cone enters the assembly of the scaling theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- The radial pair read at a random radius `x(p)`: the limit (in `EReal`, then `toReal`) of the readings at the
dyadic radii `⌈2^n x(p)⌉ / 2^n`. -/
noncomputable def radRead (x : RadialPair → ℝ) (p : RadialPair) : ℝ :=
  (Filter.limsup (fun n : ℕ => (radLevel p (dyadicRadius n ⌈(2 : ℝ) ^ n * x p⌉) : EReal)) atTop).toReal

lemma measurable_radRead {x : RadialPair → ℝ} (hx : Measurable x) : Measurable (radRead x) := by
  have hn : ∀ n : ℕ, Measurable fun p : RadialPair => radLevel p (dyadicRadius n ⌈(2 : ℝ) ^ n * x p⌉) := by
    intro n
    have hF : Measurable fun z : RadialPair × ℤ => radLevel z.1 (dyadicRadius n z.2) :=
      measurable_from_prod_countable_left fun i => measurable_radLevel (dyadicRadius n i)
    have hk : Measurable fun p : RadialPair => ⌈(2 : ℝ) ^ n * x p⌉ :=
      Int.measurable_ceil.comp (measurable_const.mul hx)
    have hg : Measurable fun p : RadialPair => (p, ⌈(2 : ℝ) ^ n * x p⌉) := measurable_id.prodMk hk
    have hc := hF.comp hg
    exact hc
  have hl : Measurable fun p : RadialPair =>
      Filter.limsup (fun n : ℕ => ((radLevel p (dyadicRadius n ⌈(2 : ℝ) ^ n * x p⌉) : ℝ) : EReal)) atTop :=
    Measurable.limsup (f := fun (n : ℕ) (p : RadialPair) =>
      ((radLevel p (dyadicRadius n ⌈(2 : ℝ) ^ n * x p⌉) : ℝ) : EReal)) fun n => (hn n).coe_real_ereal
  exact hl.ereal_toReal

/-- If the reading of `p` is continuous at the positive radius `x`, then `radRead` at the constant radius `x`
is the reading of `p` at `x`. -/
lemma radRead_const_of_continuousAt {p : RadialPair} {x : ℝ} (hx : 0 < x)
    (hc : ContinuousAt (radLevel p) x) : radRead (fun _ => x) p = radLevel p x := by
  have ht := (hc.tendsto.comp (tendsto_dyadicRadius_ceil hx))
  have ht' : Tendsto (fun n : ℕ => (radLevel p (dyadicRadius n ⌈(2 : ℝ) ^ n * x⌉) : EReal)) atTop
      (𝓝 (radLevel p x : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp ht
  simp only [radRead, ht'.limsup_eq, EReal.toReal_coe]

/-- The map on radial pairs which sends the radial pair of a cone to that of its rescaling at the scale radius
`R_b`: `(t, s) ↦ h(R_b e^{∓·}) + Q log R_b - γ⁻¹ log b`. -/
noncomputable def radialRescale (γ b : ℝ) (p : RadialPair) : RadialPair :=
  (fun t => radRead (fun p' => radScale γ b p' * Real.exp (-(t : ℝ))) p + lqgQ γ * Real.log (radScale γ b p)
      - γ⁻¹ * Real.log b,
   fun s => radRead (fun p' => radScale γ b p' * Real.exp (s : ℝ)) p + lqgQ γ * Real.log (radScale γ b p)
      - γ⁻¹ * Real.log b)

lemma measurable_radialRescale (γ b : ℝ) : Measurable (radialRescale γ b) := by
  have hR := measurable_radScale γ b
  have hc : Measurable fun p : RadialPair => lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b :=
    (measurable_const.mul (Real.measurable_log.comp hR)).sub measurable_const
  refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) (measurable_pi_iff.2 fun s => ?_)
  · have := (measurable_radRead (x := fun p' => radScale γ b p' * Real.exp (-(t : ℝ)))
      (hR.mul measurable_const)).add hc
    convert this using 1
    funext p
    simp only [Pi.add_apply]
    ring
  · have := (measurable_radRead (x := fun p' => radScale γ b p' * Real.exp (s : ℝ))
      (hR.mul measurable_const)).add hc
    convert this using 1
    funext p
    simp only [Pi.add_apply]
    ring

/-- The reading of the radial pair of a field with continuous circle averages is continuous at positive radii. -/
lemma continuousAt_radLevel_radialProcess {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (radLevel (radialProcess hc)) r := by
  have h1 : ContinuousOn (fun s : ℝ => hc s 0) (Set.Ioi 0) :=
    hcont.comp (by fun_prop : Continuous fun s : ℝ => (s, (0 : ℂ))).continuousOn
      (fun s hs => ⟨hs, Set.mem_univ _⟩)
  have h2 : ContinuousAt (fun s : ℝ => hc s 0) r := h1.continuousAt (Ioi_mem_nhds hr)
  refine h2.congr ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact (radLevel_radialProcess hc hs).symm

/-- **The radial process of the rescaled cone is a measurable function of the radial process of the cone.**  Almost
surely, the radial pair of `h(R_b ·) + Q log R_b - γ⁻¹ log b` is `radialRescale γ b` of the radial pair of `h`. -/
theorem radialProcess_rescaled_ae {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    ∀ᵐ ω ∂P, radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) =
      radialRescale γ b (radialProcess (hcirc ω)) := by
  filter_upwards [h.ae_continuousOn_circle, ae_coneScaleRadius_spec hγ0 hγ2 h b,
    radScale_radialProcess_ae hγ0 hγ2 h b] with ω hcont hspec hrs
  obtain ⟨hR, -, -⟩ := hspec
  set R := coneScaleRadius γ (hcirc ω) b with hRdef
  have key : ∀ y : ℝ, 0 < y → radRead (fun _ => R * y) (radialProcess (hcirc ω)) = hcirc ω (R * y) 0 := by
    intro y hy
    have hpos : 0 < R * y := mul_pos hR hy
    rw [radRead_const_of_continuousAt hpos (continuousAt_radLevel_radialProcess hcont hpos),
      radLevel_radialProcess _ hpos]
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have e : radRead (fun p' => radScale γ b p' * Real.exp (-(t : ℝ))) (radialProcess (hcirc ω)) =
        radRead (fun _ => R * Real.exp (-(t : ℝ))) (radialProcess (hcirc ω)) := by
      simp only [radRead, hrs]
    have lhs : (radialProcess (rescaledCircle γ (hcirc ω) R b)).1 t =
        hcirc ω (R * Real.exp (-(t : ℝ))) 0 + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      simp [radialProcess, rescaledCircle]
    rw [lhs]
    simp only [radialRescale, hrs, e, key _ (Real.exp_pos (-(t : ℝ)))]
  · have e : radRead (fun p' => radScale γ b p' * Real.exp (s : ℝ)) (radialProcess (hcirc ω)) =
        radRead (fun _ => R * Real.exp (s : ℝ)) (radialProcess (hcirc ω)) := by
      simp only [radRead, hrs]
    have lhs : (radialProcess (rescaledCircle γ (hcirc ω) R b)).2 s =
        hcirc ω (R * Real.exp (s : ℝ)) 0 + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      simp [radialProcess, rescaledCircle]
    rw [lhs]
    simp only [radialRescale, hrs, e, key _ (Real.exp_pos (s : ℝ))]

end MatedCRT.FirstPass.Derived
