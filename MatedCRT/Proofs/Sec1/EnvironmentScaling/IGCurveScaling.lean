import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Deterministic no-period and integer-rotation component of the IG curve scaling

The frozen interface is Leonardo Bonanno's
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`, with its
`MatedCRTAffineReroot`, `MatedCRTIgPullback`, `MatedCRTFirstHit`, `MatedCRTIgChi`,
`MatedCRTField` and `MatedCRTPath2` modules, used unchanged. The only inputs are its
`igMap` witness `Φ` (representation, identity-affine and rotated covariance clauses)
and the transience clause of `spaceFilling`.

Proved here:
* `no_nonzero_period_of_tendsto_cocompact`: a proper continuous curve has no nonzero
  translation period.
* `igMap_period_identity`: `q₀(L) = firstHit L 0` vanishes almost surely, and
  simultaneously for every `k : ℤ`, `Φ (K + k p) = Φ K` almost surely, where
  `p = 2π χ`, `χ = igChi γ`. The same for the witness of a coupling: `igMap_witness_period`.
* `igMap_scale_identity`, `igMap_scale_normalized_identity` and
  `igMap_witness_scale_normalized`: the deterministic positive-scale identity
  `Φ (A − a + V) = s⁻¹ L(s² ·)` almost surely, with `V = U + a − k p ∈ [0, p)`,
  `k = ⌊(U + a)/p⌋`; the random integer is removed by the simultaneous identity.

Not proved here (exact residuals in the report): the law of `(I^{(s)}, V)`, i.e. the
normalized whole-plane affine-GFF law of `I^{(s)} = I(s·) − a` and the independence and
uniformity of `V`, which would give `s⁻¹ L(s² ·) =_d L`. Random-radius conditioning, area
parametrization and `mainlaw` are separate components. No independence beyond the
frozen clauses and no law of the arbitrary SLE model is used.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal

noncomputable section

namespace MatedCRT.Sec1

open MatedCRTHarmonic.MatedCRT (affineReroot igPullback firstHit igChi)

/-- A continuous curve that is proper, `Tendsto c (cocompact ℝ) (cocompact ℂ)` (the
transience clause of `spaceFilling`), has no nonzero translation period. -/
theorem no_nonzero_period_of_tendsto_cocompact (c : C(ℝ, ℂ))
    (hc : Tendsto c (cocompact ℝ) (cocompact ℂ)) (τ : ℝ) (hper : ∀ t, c (τ + t) = c t) :
    τ = 0 := by
  by_contra hτ
  have hS : ({c 0}ᶜ : Set ℂ) ∈ cocompact ℂ :=
    mem_cocompact.2 ⟨{c 0}, isCompact_singleton, subset_rfl⟩
  obtain ⟨T, hT, hTsub⟩ := mem_cocompact.1 (hc hS)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hT.isBounded
  have hrep : ∀ n : ℕ, c ((n : ℝ) * τ) = c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℝ) * τ = τ + (m : ℝ) * τ by push_cast; ring, hper, ih]
  obtain ⟨n, hn⟩ := exists_nat_gt (R / |τ|)
  have hmem : (n : ℝ) * τ ∈ T := by
    by_contra hnT
    have h1 : c ((n : ℝ) * τ) ∈ ({c 0}ᶜ : Set ℂ) := hTsub hnT
    exact (Set.mem_compl_iff _ _).1 h1 (Set.mem_singleton_iff.2 (hrep n))
  have hle : ‖(n : ℝ) * τ‖ ≤ R := hR _ hmem
  have habs : ‖(n : ℝ) * τ‖ = (n : ℝ) * |τ| := by
    rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
  have hlt : R < (n : ℝ) * |τ| := (div_lt_iff₀ (abs_pos.2 hτ)).1 hn
  linarith

/-- At the affine map `(z₀, s, φ) = (0, 1, φ)`, `affineReroot` returns the curve itself
once its first hit of `0` is `0` and `e^{iφ} = 1`. -/
theorem affineReroot_zero_one_eq (c : C(ℝ, ℂ)) (φ : ℝ) (hfh : firstHit c 0 = 0)
    (hφ : Complex.exp (φ * Complex.I) = 1) : affineReroot 0 1 φ c = c := by
  ext t
  simp [affineReroot, hfh, hφ]

/-- At the identity affine map with `φ = 0`, `affineReroot` is the translation of the curve by
its first hit of `0`: `R_{0,1,0} c (t) = c (q₀(c) + t)`. -/
theorem affineReroot_zero_one_zero_apply (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot 0 1 0 c t = c (firstHit c 0 + t) := by
  simp [affineReroot]

/-- The pullback `igPullback` at the identity affine map is the identity on arrays. -/
theorem igPullback_zero_one_zero (γ : ℝ) (H : ℝ → ℂ → ℝ) : igPullback γ 0 1 0 H = H := by
  funext ρ w
  simp [igPullback]

/-- `e^{-2π i k} = 1` for every integer `k`. -/
theorem exp_neg_two_pi_int_mul_I (k : ℤ) :
    Complex.exp (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [show (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I)
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The pullback at the integer rotation `φ = -2πk` shifts the array by `k p`, where
`p = 2π χ` and `χ = igChi γ`. -/
theorem igPullback_rotation (γ : ℝ) (k : ℤ) (H : ℝ → ℂ → ℝ) :
    igPullback γ 0 1 (-(2 * Real.pi * k)) H
      = fun ρ w => H ρ w + k * (2 * Real.pi * igChi γ) := by
  have hexp := exp_neg_two_pi_int_mul_I k
  funext ρ w
  simp only [igPullback, Complex.ofReal_one, one_mul, zero_add, hexp]
  ring

/-- The affine rerooting at an integer rotation fixes a curve whose first hit of `0` is `0`. -/
theorem affineReroot_rotation_eq (c : C(ℝ, ℂ)) (k : ℤ) (hfh : firstHit c 0 = 0) :
    affineReroot 0 1 (-(2 * Real.pi * k)) c = c :=
  affineReroot_zero_one_eq c _ hfh (exp_neg_two_pi_int_mul_I k)

/-- **Deterministic core of the first component of `lem:mainlaw`** (`env-steps.tex`
774–799). `K ω` is the raw circle array, `Φ` is a witness with `L ω = Φ (K ω)` almost
surely, the covariance clause holds at every deterministic `(z₀, s, φ)` with `s > 0`,
and `L ω` is transient almost surely. Then `q₀(L) = firstHit (L ω) 0` vanishes almost
surely, and simultaneously for every `k : ℤ`, `Φ (K + k p) = Φ K` almost surely,
where `p = 2π χ`. -/
theorem igMap_period_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (igPullback γ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ)) :
    (∀ᵐ ω ∂P, firstHit (L ω) 0 = 0) ∧
      ∀ᵐ ω ∂P, ∀ k : ℤ,
        Φ (fun ρ w => K ω ρ w + k * (2 * Real.pi * igChi γ)) = Φ (K ω) := by
  have hid : ∀ᵐ ω ∂P, L ω = affineReroot 0 1 0 (L ω) := by
    filter_upwards [hrep, hcov 0 1 0 one_pos] with ω h1 h2
    rw [igPullback_zero_one_zero] at h2
    exact h1.trans h2
  have hfh : ∀ᵐ ω ∂P, firstHit (L ω) 0 = 0 := by
    filter_upwards [hid, htr] with ω h1 h2
    refine no_nonzero_period_of_tendsto_cocompact (L ω) h2 (firstHit (L ω) 0) fun t => ?_
    have h3 := DFunLike.congr_fun h1 t
    rw [affineReroot_zero_one_zero_apply] at h3
    exact h3.symm
  have hper : ∀ k : ℤ, ∀ᵐ ω ∂P,
      Φ (fun ρ w => K ω ρ w + k * (2 * Real.pi * igChi γ)) = Φ (K ω) := by
    intro k
    filter_upwards [hcov 0 1 (-(2 * Real.pi * k)) one_pos, hfh, hrep] with ω h1 h2 h3
    rw [igPullback_rotation, affineReroot_rotation_eq _ k h2] at h1
    exact h1.trans h3
  exact ⟨hfh, ae_all_iff.2 hper⟩

/-- **The `igMap` witness satisfies the integer period identity.** For a mating-of-trees
coupling `h`, the witness `Φ` of the frozen `igMap` clause (which ignores nonpositive
radii, represents `ηL` on `K ω = circleAvg (hIG₀ ω) + U ω`, and satisfies the
coordinate-change clause) also gives `q₀(ηL) = 0` almost surely and the simultaneous
integer period identity. -/
theorem igMap_witness_period {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
      (∀ᵐ ω ∂P, ηL ω = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ∧
      (∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0) ∧
      ∀ᵐ ω ∂P, ∀ k : ℤ,
        Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω + k * (2 * Real.pi * igChi γ))
          = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) := by
  obtain ⟨Φ, hmeas, hign, hrep, hcov, -⟩ := h.igMap
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) :=
    h.spaceFilling.mono fun ω hω => hω.2.1
  obtain ⟨hfh, hper⟩ := igMap_period_identity P γ
    (fun ω ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) ηL Φ hrep hcov htr
  exact ⟨Φ, hmeas, hign, hrep, hfh, hper⟩

/-- The pullback at scale `s` and integer rotation `-2πk` sends `K` to `K(s·, s·) + k p`. -/
theorem igPullback_scale_rotation (γ s : ℝ) (k : ℤ) (H : ℝ → ℂ → ℝ) :
    igPullback γ 0 s (-(2 * Real.pi * k)) H
      = fun ρ w => H (s * ρ) ((s : ℂ) * w) + k * (2 * Real.pi * igChi γ) := by
  have hexp := exp_neg_two_pi_int_mul_I k
  funext ρ w
  simp only [igPullback, hexp, mul_one, zero_add]
  ring

/-- At `(0, s, -2πk)` the rerooting agrees with the one at `(0, s, 0)`, once the first hit
of `0` is `0`. -/
theorem affineReroot_scale_rotation_eq (c : C(ℝ, ℂ)) (s : ℝ) (k : ℤ)
    (hfh : firstHit c 0 = 0) :
    affineReroot 0 s (-(2 * Real.pi * k)) c = affineReroot 0 s 0 c := by
  have hexp := exp_neg_two_pi_int_mul_I k
  ext t
  simp only [affineReroot, ContinuousMap.coe_mk, hexp, hfh, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero]

/-- **Deterministic scale-`s` identity** (`env-steps.tex` 790–802). For `s > 0`, almost
surely and simultaneously for every `m : ℤ`, `Φ (K(s·, s·) + m p) = R_{0,s,0} L`, where
`R_{0,s,0} L (t) = s⁻¹ L(s² t)`. The integer is absorbed by the rotation family itself. -/
theorem igMap_scale_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (igPullback γ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ))
    (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∀ m : ℤ,
      Φ (fun ρ w => K ω (s * ρ) ((s : ℂ) * w) + m * (2 * Real.pi * igChi γ))
        = affineReroot 0 s 0 (L ω) := by
  obtain ⟨hfh, -⟩ := igMap_period_identity P γ K L Φ hrep hcov htr
  have hm : ∀ m : ℤ, ∀ᵐ ω ∂P,
      Φ (fun ρ w => K ω (s * ρ) ((s : ℂ) * w) + m * (2 * Real.pi * igChi γ))
        = affineReroot 0 s 0 (L ω) := by
    intro m
    filter_upwards [hcov 0 s (-(2 * Real.pi * m)) hs, hfh] with ω h1 h2
    rw [igPullback_scale_rotation, affineReroot_scale_rotation_eq _ s m h2] at h1
    exact h1
  exact ae_all_iff.2 hm

/-- The remainder of `x` modulo `p > 0` lies in `[0, p)`; this is the range of `V` below. -/
theorem floor_remainder_mem_Ico (x p : ℝ) (hp : 0 < p) :
    0 ≤ x - ⌊x / p⌋ * p ∧ x - ⌊x / p⌋ * p < p := by
  have h1 : (⌊x / p⌋ : ℝ) ≤ x / p := Int.floor_le _
  have h2 : x / p < (⌊x / p⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (⌊x / p⌋ : ℝ) * p ≤ x := (le_div_iff₀ hp).1 h1
  have h2' : x < ((⌊x / p⌋ : ℝ) + 1) * p := (div_lt_iff₀ hp).1 h2
  rw [add_mul, one_mul] at h2'
  constructor <;> linarith

/-- **Positive-scale identity with the random integer removed** (`env-steps.tex` 790–802,
before the law step). Let `K(s r, s w) = A(r, w) + U` define the scaled array, `a` the
normalizing constant `circleAvg (I) s 0`, `p = 2πχ`, `k = ⌊(U + a)/p⌋` and
`V = U + a − k p ∈ [0, p)`. Then almost surely `Φ (A − a + V) = s⁻¹ L(s² ·)`. -/
theorem igMap_scale_normalized_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (igPullback γ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ))
    (s : ℝ) (hs : 0 < s) (A : Ω → ℝ → ℂ → ℝ) (a U : Ω → ℝ)
    (hKA : ∀ ω r w, K ω (s * r) ((s : ℂ) * w) = A ω r w + U ω) :
    ∀ᵐ ω ∂P,
      Φ (fun r w => A ω r w - a ω + (U ω + a ω
          - ((⌊(U ω + a ω) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) * (2 * Real.pi * igChi γ)))
        = affineReroot 0 s 0 (L ω) := by
  filter_upwards [igMap_scale_identity P γ K L Φ hrep hcov htr s hs] with ω hω
  have h := hω (-⌊(U ω + a ω) / (2 * Real.pi * igChi γ)⌋)
  convert h using 2
  funext r w
  rw [hKA]
  push_cast
  ring

/-- **The normalized positive-scale identity for the `igMap` witness of a coupling `h`.** With
`a = circleAvg (hIG₀) s 0` and `A (r, w) = circleAvg (hIG₀) (s r) (s w)`, the normalized field
`I^{(s)} = I(s·) − a` has circle averages `A − a`, and almost surely
`Φ (A − a + V) = s⁻¹ L(s² ·)` with `V = U + a − k p`, `k = ⌊(U + a)/p⌋`. -/
theorem igMap_witness_scale_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (s : ℝ) (hs : 0 < s) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ᵐ ω ∂P, ηL ω = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ∧
      ∀ᵐ ω ∂P,
        Φ (fun r w => LQGMetric.circleAvg (hIG₀ ω) (s * r) (s * w)
              - LQGMetric.circleAvg (hIG₀ ω) s 0
              + (U ω + LQGMetric.circleAvg (hIG₀ ω) s 0
                - ((⌊(U ω + LQGMetric.circleAvg (hIG₀ ω) s 0) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ)
                  * (2 * Real.pi * igChi γ)))
          = affineReroot 0 s 0 (ηL ω) := by
  obtain ⟨Φ, hmeas, -, hrep, hcov, -⟩ := h.igMap
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) :=
    h.spaceFilling.mono fun ω hω => hω.2.1
  refine ⟨Φ, hmeas, hrep, ?_⟩
  exact igMap_scale_normalized_identity P γ
    (fun ω ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) ηL Φ hrep hcov htr s hs
    (fun ω (r : ℝ) (w : ℂ) => LQGMetric.circleAvg (hIG₀ ω) (s * r) (s * w))
    (fun ω => LQGMetric.circleAvg (hIG₀ ω) s 0) U (fun ω r w => rfl)

end MatedCRT.Sec1
