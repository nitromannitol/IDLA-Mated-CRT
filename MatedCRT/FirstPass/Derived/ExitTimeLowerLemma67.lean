import MatedCRT.FirstPass.Derived.ExitTimeLowerCore
import MatedCRT.FirstPass.Derived.ExitTimeLowerBound
import MatedCRT.FirstPass.Derived.ConeLogIntegralBound
import MatedCRT.FirstPass.Derived.HBBallMassHolds
import MatedCRT.Proofs.Infra.Setting

/-!
# Lower tail of the exit time from a small ball (Berestycki-Gwynne, Lemma 6.7)

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Lemma 6.7: for `ℓ > 0`, `a > ℓγ²/2` and `b > (2 + γ)²ℓ/2`, with probability tending
to `1` as `ε → 0` and then `δ → 0`, every vertex `x ∈ V^ε(B_{ρ - δ^ℓ})` satisfies
`P_x[τ ≥ ε⁻¹ δ^b] ≥ δ^a`, where `τ` is the exit time of the simple random walk on the mated-CRT map from
the interior vertices of `B_{δ^ℓ}(η(x))`.

The proof combines, at `r = δ^ℓ` and the centre `z = η(x)`:
* the lower bound for the expected exit time `ε⁻¹ μ_h(B_{cr}(z)) ≤ E_x[τ]` (Proposition 4.1,
  `ExitTimeLowerBound.exitTimeLowerBound_of_greenLower`, from the Green kernel lower bound);
* the moment bound `E_x[τ^N] ≤ N! C^N ε^{-N} (sup_{z'} ∫ (log (1/|z' - w|) + 1) dμ_h(w))^N` (the first
  conjunct of `ExitTimeUpperBoundStmt`);
* the logarithmic-kernel bound (6.17) (`polyHighProb_iSup_setLIntegral_log_le_cone`);
* the ratio bound (6.18), `μ_h(B_{cr}(z)) ≥ (2r)^{γ²/2 + ζ} μ_h(B_{2r}(z))` (Appendix A, Lemma A.2 for the
  quantum cone, taken here as the hypothesis `h618`);
* the mass bounds (6.20) (Lemma A.1 for the quantum cone, `frozenBerestyckiGwynneConeBallMass_holds`);
* the deterministic Paley-Zygmund step `ofReal_rpow_le_srwLaw_exitTime_of_ratio`.

The quantifier order is the one of the printed lemma: the threshold `δ₀` may depend on the environment.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- An event of polynomially high probability fails with probability at most `θ` at all small scales. -/
theorem polyHighProb_eventually_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : PolyHighProb P E) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), P (E r)ᶜ ≤ ENNReal.ofReal θ := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  have hK : 0 < θ / (|C| + 1) := div_pos hθ (by positivity)
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr₀,
    LatticeProb.LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul hK hp] with r hr hrr hpow
  refine (hE r hr hrr.2).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.rpow_zero, mul_one] at hpow
  have h0 : 0 ≤ r ^ p := Real.rpow_nonneg (le_of_lt hr) _
  have hC1 : 0 < |C| + 1 := by positivity
  calc C * r ^ p ≤ (|C| + 1) * r ^ p := by nlinarith [le_abs_self C]
    _ ≤ (|C| + 1) * (θ / (|C| + 1)) := mul_le_mul_of_nonneg_left hpow hC1.le
    _ = θ := by field_simp

/-- A positive power of a small positive number is below any positive constant. -/
theorem eventually_rpow_le_const {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), r ^ x ≤ y := by
  filter_upwards [LatticeProb.LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul hy hx] with r hr
  rwa [Real.rpow_zero, mul_one] at hr

/-- Union bound for complements: if `A ∩ B ⊆ G` then `P(Gᶜ) ≤ P(Aᶜ) + P(Bᶜ)`. -/
theorem measure_compl_le_of_inter_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A B G : Set Ω} (h : A ∩ B ⊆ G) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : P Aᶜ ≤ ENNReal.ofReal x) (hB : P Bᶜ ≤ ENNReal.ofReal y) :
    P Gᶜ ≤ ENNReal.ofReal (x + y) := by
  rw [ENNReal.ofReal_add hx hy]
  calc P Gᶜ ≤ P (Aᶜ ∪ Bᶜ) := measure_mono (by rw [← compl_inter]; exact compl_subset_compl.2 h)
    _ ≤ P Aᶜ + P Bᶜ := measure_union_le _ _
    _ ≤ _ := add_le_add hA hB

/-- **Berestycki-Gwynne, Lemma 6.7** (arXiv:2003.10320, p. 37), in the quantifier order of the printed
statement. Let `0 < γ < 2`, `ℓ > 0`, `a > ℓγ²/2`, `b > (2 + γ)²ℓ/2` and `ρ ∈ (0, 1)`. For a valid environment
and every `θ > 0` there is `δ₀ > 0` such that for each `δ ∈ (0, δ₀)` there is `ε₀ > 0` with: for `ε ∈ (0, ε₀)`,
outside an event of probability at most `θ`, every vertex `x ∈ V^ε(B_{ρ - δ^ℓ})` satisfies
`δ^a ≤ P_x[ε⁻¹ δ^b ≤ τ]`, where `τ` is the exit time from the interior vertices of `B_{δ^ℓ}(η(x))`.

Inputs: the Green kernel lower bound `h213` (Lemma 2.13), the exit time moment bound `h214` (Lemma 2.14, first
conjunct) and the ratio bound `h618` for the quantum cone (BG20 Lemma A.2, used in (6.18)). -/
theorem exitTimeLowerTail_weak {𝒮 : SpaceFillingSLEModel} (h213 : GreenKernelLowerBoundStmt 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ℓ a b : ℝ} (hℓ : 0 < ℓ)
    (ha : ℓ * γ ^ 2 / 2 < a) (hb : (2 + γ) ^ 2 * ℓ / 2 < b) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h618 : ∀ c : ℝ, 0 < c → c < 1 → ∀ ζ : ℝ, 0 < ζ →
      PolyHighProb S.P (fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * S.μ ω (ball z δ) ≤ S.μ ω (ball z (c * δ))}))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ ^ ℓ)),
        ENNReal.ofReal (δ ^ a) ≤ srwLaw (S.mult ε ω) x {y | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
          (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) (δ ^ ℓ))) y :
            ℝ≥0∞)}}ᶜ ≤ ENNReal.ofReal θ := by
  classical
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := hS.isConeField
  -- the radius at which the inputs are applied
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  -- the inputs
  obtain ⟨ω₁, hω₁, hL1⟩ := ExitTimeLowerBound.exitTimeLowerBound_of_greenLower h213 γ hγ hγ2
  obtain ⟨c, hc, hc3, hL1'⟩ := hL1 ρ' hρ'0 hρ'1
  obtain ⟨α, hα, hU⟩ := h214 γ hγ hγ2
  obtain ⟨C, hC, hU'⟩ := hU ρ' hρ'0 hρ'1
  set ζc : ℝ := 1 / (2 + γ) ^ 2 with hζc
  have h2γ : 4 < (2 + γ) ^ 2 := by nlinarith
  have hζc0 : 0 < ζc := by positivity
  have hζc1 : ζc < 1 := by rw [hζc, div_lt_one (by positivity)]; linarith
  have hβc : 2 / (2 + γ) ^ 2 - ζc = ζc := by rw [hζc]; ring
  -- the exponents
  set e : ℝ := ℓ * γ ^ 2 / 2 with he
  have he0 : 0 < e := by positivity
  set g : ℝ := a - e with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set ζ₂ : ℝ := g / (8 * ℓ) with hζ₂
  have hζ₂0 : 0 < ζ₂ := div_pos hg0 (by positivity)
  set ζb : ℝ := g / 8 with hζb
  have hζb0 : 0 < ζb := div_pos hg0 (by norm_num)
  set E2 : ℝ := γ ^ 2 / 2 + ζ₂ with hE2
  have hlE2 : ℓ * E2 + ζb = e + g / 4 := by
    rw [hE2, hζ₂, hζb, he]; field_simp; ring
  have heg : 0 < e + g / 4 := by positivity
  set p : ℝ := (e + g / 2) / (e + g / 4) with hp
  have hp1 : 1 < p := by rw [hp, one_lt_div heg]; linarith
  have hpe : (e + g / 4) * p < a := by
    have : (e + g / 4) * p = e + g / 2 := by rw [hp]; field_simp
    rw [this, hg]; linarith
  set q : ℝ := p.conjExponent with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := by
    rw [hq]; unfold Real.conjExponent; exact div_pos (by linarith) (by linarith)
  set N : ℕ := ⌈q⌉₊ with hN
  have hqN : q ≤ N := Nat.le_ceil q
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hq0).ne'
  set ζ₁ : ℝ := min (1 / 2) ((b - (2 + γ) ^ 2 * ℓ / 2) / (2 * ℓ)) with hζ₁
  have hζ₁0 : 0 < ζ₁ := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hζ₁1 : ζ₁ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  set E1 : ℝ := (2 + γ) ^ 2 / 2 + ζ₁ with hE1
  have hlE1 : ℓ * E1 < b := by
    have h1 : ζ₁ ≤ (b - (2 + γ) ^ 2 * ℓ / 2) / (2 * ℓ) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    rw [hE1]; nlinarith
  -- the events
  have EL1 := hL1' Ω S hS
  have EU := hU' Ω S hS
  have ECs := cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 ζc ρ' hζc0 hζc1 hρ'0 hρ'1 Ω S hS
  have EB := polyHighProb_iSup_setLIntegral_log_le_cone hγ hγ2 hℓ hζb0 hρ'1 hcone
  have E2' := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_rpow
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_mul
      (h618 (c / 2) (by positivity) (by linarith) ζ₂ hζ₂0) two_pos) hℓ
  have hA1all : BerestyckiGwynneConeBallMassStmt := frozenBerestyckiGwynneConeBallMass_holds
  have E1' := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_rpow
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_mul
      (hA1all Ω S.P γ S.hC S.hcirc S.μ hγ hγ2 hcone ζ₁ hζ₁0 hζ₁1) hc) hℓ
  have EG := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_inter
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_inter EB E2') E1'
  have EH := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_inter
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_inter EL1 EU) ECs
  -- the thresholds in `δ`
  have hNC : (0 : ℝ) < N.factorial * C := mul_pos (Nat.cast_pos.2 (Nat.factorial_pos N)) hC
  set K : ℝ := 2 ^ E2 / (2 * (N.factorial * C)) with hK
  have hK0 : 0 < K := div_pos (Real.rpow_pos_of_pos two_pos _) (mul_pos two_pos hNC)
  have hd1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ a ≤ K ^ p * δ ^ ((e + g / 4) * p) :=
    LatticeProb.LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul (Real.rpow_pos_of_pos hK0 p) hpe
  have hd2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ b ≤ c ^ E1 / 2 * δ ^ (ℓ * E1) :=
    LatticeProb.LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul
      (div_pos (Real.rpow_pos_of_pos hc _) two_pos) hlE1
  have hd3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ ℓ ≤ (1 - ρ) / 2 :=
    eventually_rpow_le_const hℓ (by linarith)
  have hd4 := polyHighProb_eventually_compl_le EG (half_pos hθ)
  obtain ⟨δ₀, hδ₀, hδall⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    (hd1.and (hd2.and (hd3.and hd4)))
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
  obtain ⟨hδa, hδb, hδρ, hPG⟩ := hδall δ hδ hδδ₀
  have hr : 0 < δ ^ ℓ := Real.rpow_pos_of_pos hδ ℓ
  -- the final exponent bounds at this `δ`
  have hfin : δ ^ a ≤ ((2 * δ ^ ℓ) ^ E2 / (2 * (N.factorial * C * δ ^ (-ζb)))) ^ p := by
    have hal : (2 * δ ^ ℓ) ^ E2 / (2 * (N.factorial * C * δ ^ (-ζb))) = K * δ ^ (e + g / 4) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le, ← hlE2,
        Real.rpow_add hδ, Real.rpow_neg hδ.le, hK]
      have h1 : (0 : ℝ) < δ ^ ζb := Real.rpow_pos_of_pos hδ _
      field_simp
    rw [hal, Real.mul_rpow hK0.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
    exact hδa
  have htb : δ ^ b ≤ (c * δ ^ ℓ) ^ E1 / 2 := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
    linarith
  set r : ℝ := δ ^ ℓ with hr_def
  set T : ℝ := (c * r) ^ E1 with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos (mul_pos hc hr) _
  -- the thresholds in `ε`
  have he1 := eventually_rpow_le_const hω₁ hr
  have he2 := eventually_rpow_le_const hα hr
  have he3 := eventually_rpow_le_const hα hT0
  have he4 := eventually_rpow_le_const hζc0 (half_pos hr)
  have he5 := polyHighProb_eventually_compl_le EH (half_pos hθ)
  obtain ⟨ε₀, hε₀, hεall⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    (he1.and (he2.and (he3.and (he4.and he5))))
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hεω₁, hεα, hεT, hεc, hPH⟩ := hεall ε hε hεε₀
  refine (measure_compl_le_of_inter_subset ?_ (half_pos hθ).le (half_pos hθ).le hPG hPH).trans_eq
    (by rw [add_halves])
  rintro ω ⟨⟨⟨hB, h2⟩, h1⟩, ⟨⟨hl1, hu1, -⟩, hcs⟩⟩ x ⟨w, hwcell, hwball⟩
  -- the position of the vertex
  set z := vertexPoint ε (S.η ω) x with hz_def
  have hzcell : z ∈ cell ε (S.η ω) x :=
    ⟨ε * x, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hwn : ‖w‖ < ρ - r := mem_ball_zero_iff.1 hwball
  have hwρ' : w ∈ ball (0 : ℂ) ρ' := mem_ball_zero_iff.2 (by linarith)
  obtain ⟨hlo, hup⟩ := hcs x ⟨w, hwcell, hwρ'⟩
  rw [hβc] at hup
  have hzw : dist z w ≤ ε ^ ζc :=
    ExitTimeLowerBound.dist_le_of_diam_le (Real.rpow_pos_of_pos hε _) hlo hup hzcell hwcell
  have hzn : ‖z‖ < ρ - r / 2 := by
    have := norm_sub_norm_le z w
    rw [dist_eq_norm] at hzw
    linarith
  have hcr : c * r ≤ r / 3 := by
    have := mul_le_mul_of_nonneg_right hc3 hr.le
    linarith
  have hz1 : z ∈ ball (0 : ℂ) (1 - c * r) := mem_ball_zero_iff.2 (by linarith)
  have hz2 : z ∈ ball (0 : ℂ) (1 - 2 * r) := mem_ball_zero_iff.2 (by linarith)
  have hzB : z ∈ ball (0 : ℂ) ρ' := mem_ball_zero_iff.2 (by linarith)
  have hD : ball z r ⊆ ball (0 : ℂ) ρ' := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have := norm_sub_norm_le y z
    exact mem_ball_zero_iff.2 (by linarith)
  -- (6.20): the mass of the small ball
  obtain ⟨hA1lo, hA1hi⟩ := h1 z hz1
  have hMc : S.μ ω (ball z (c * r)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA1hi
  -- Proposition 4.1: the expected exit time
  have hx1 : x ∈ cellVertices ε (S.η ω) (ball 0 (ρ' - ε ^ ω₁)) :=
    ⟨w, hwcell, mem_ball_zero_iff.2 (by linarith)⟩
  have hinf : r ≤ infDist z (sphere (0 : ℂ) ρ') := by
    rw [Metric.le_infDist ⟨(ρ' : ℂ), by simp [abs_of_pos hρ'0]⟩]
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    rw [dist_comm, dist_eq_norm]
    have := norm_sub_norm_le y z
    linarith
  have hLE := hl1 x hx1 r hεω₁ hinf
  -- the moment bound
  have hmass : ENNReal.ofReal (ε ^ α) ≤ S.μ ω (ball z r) :=
    (ENNReal.ofReal_le_ofReal hεT).trans
      (hA1lo.trans (measure_mono (ball_subset_ball (by linarith))))
  have hxD : x ∈ cellVertices ε (S.η ω) (ball z r) := ⟨z, hzcell, mem_ball_self hr⟩
  have hmom := hu1 (ball z r) measurableSet_ball hD hmass x hxD N
  -- (6.17): the logarithmic kernel
  have hthick : thickening (ε ^ α) (ball z r) ⊆ ball z (2 * r) := by
    intro y hy
    obtain ⟨w', hw', hyw⟩ := mem_thickening_iff.1 hy
    rw [mem_ball] at hw' ⊢
    linarith [dist_triangle y w' z]
  have hI : (⨆ z' ∈ ball z r, ∫⁻ v in thickening (ε ^ α) (ball z r),
        ENNReal.ofReal (Real.log (1 / ‖z' - v‖) + 1) ∂S.μ ω) ≤
      ENNReal.ofReal (δ ^ (-ζb)) * S.μ ω (ball z (2 * r)) :=
    le_trans (iSup₂_mono fun z' _ => lintegral_mono_set hthick) (hB z hzB)
  -- (6.18): the ratio of the masses
  have hR := h2 z hz2
  rw [show c / 2 * (2 * r) = c * r by ring] at hR
  -- the Paley-Zygmund step
  have hcore := ofReal_rpow_le_srwLaw_exitTime_of_ratio (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) (ball z r)) x hpq hN1 hqN hε hC
    (Real.rpow_pos_of_pos hδ (-ζb)) (Real.rpow_nonneg (mul_pos two_pos hr).le E2) (half_pos hT0)
    hMc hLE hmom hI hR (by rw [show 2 * (T / 2) = T by ring]; exact hA1lo)
  have hX0 : 0 ≤ (2 * r) ^ E2 / (2 * (N.factorial * C * δ ^ (-ζb))) :=
    div_nonneg (Real.rpow_nonneg (mul_pos two_pos hr).le _)
      (mul_pos two_pos (mul_pos hNC (Real.rpow_pos_of_pos hδ _))).le
  refine (ENNReal.ofReal_le_ofReal hfin).trans ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg hX0 (by linarith)]
  refine hcore.trans (measure_mono fun y hy => ?_)
  exact le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htb (inv_pos.2 hε).le))
    (le_of_lt hy)

end MatedCRT.FirstPass.Derived
