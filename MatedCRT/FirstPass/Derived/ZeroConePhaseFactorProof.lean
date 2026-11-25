import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1
import Mathlib

/-!
# The step from `(h, η̂)` to the phase in the ergodicity of the shifted zero-cone configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1, `notes/refs/1705.11161.txt` lines 1193-1196)
infer from the independence of `G = Φ(H)` from `(h, h^IG)` that `G` is a function of the phase `θ` alone, and conclude
from `G([θ − τ_z]) = G(θ)` that it is constant (`ZeroConePhaseFactorStep`). The written answer on this proof
(`notes/fp-gaps/CODEX-MQ-sbl-15.md`, lines 37-49, "Removing the time-grid phase") proves instead that for almost every
`(h, e)` the circle function `θ ↦ V(h, e, θ)` has arbitrarily small positive periods (a Cameron–Martin bump of the
field shifts the quantum times of distant roots by the two signed offsets `D_±`, line 41), so that it equals its phase
average (line 49: "The periods are strictly positive and tend to zero ... so it is the whole circle. Thus `V` equals its
phase average almost surely").

This file states the periods as the named step `ZeroConePhasePeriods`, proves that a bounded measurable function on the
circle with almost-everywhere periods `D_j > 0`, `D_j → 0`, is almost everywhere constant
(`ae_eq_const_of_phasePeriods`: the level sets are invariant under the rotations by `D_j`; a rotation of infinite order
is ergodic, and rotations of finite orders tending to infinity leave only null and conull invariant sets), and derives
`ZeroConePhaseFactorStep`: by the configuration code of `ZeroConeConfigCovariance` the observable `Φ(F)` is almost surely
the phase average `m(h, η̂)`, a measurable function of the pair, and a function of `(h, η̂)` independent of `(h, η̂)` is
almost surely constant.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal Pointwise

section Circle

/-- The representative in `[0, 1)` of a point of the circle `ℝ/ℤ`, read at a real number, is its reduction mod `1`. -/
theorem measurableEquivIco_coe_apply (y : ℝ) :
    ((AddCircle.measurableEquivIco (1 : ℝ) 0 (y : AddCircle (1 : ℝ)) : Ico (0 : ℝ) (0 + 1)) : ℝ) =
      toIcoMod (zero_lt_one' ℝ) 0 y := by
  have hmem : toIcoMod (zero_lt_one' ℝ) 0 y ∈ Ico (0 : ℝ) (0 + 1) := toIcoMod_mem_Ico _ _ _
  have hc : ((toIcoMod (zero_lt_one' ℝ) 0 y : ℝ) : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
    rw [← self_sub_toIcoDiv_zsmul, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
      sub_zero]
  rw [← hc]
  show ((AddCircle.equivIco (1 : ℝ) 0 ((toIcoMod (zero_lt_one' ℝ) 0 y : ℝ) : AddCircle (1 : ℝ)) :
    Ico (0 : ℝ) (0 + 1)) : ℝ) = _
  rw [AddCircle.equivIco_coe_eq hmem]

/-- A point of finite positive order `n` of the circle `ℝ/ℤ` represented by `D > 0` satisfies `n D ≥ 1`. -/
theorem one_le_addOrderOf_mul {D : ℝ} (hD : 0 < D) (h : addOrderOf (D : AddCircle (1 : ℝ)) ≠ 0) :
    1 ≤ (addOrderOf (D : AddCircle (1 : ℝ)) : ℝ) * D := by
  set n := addOrderOf (D : AddCircle (1 : ℝ)) with hn
  have h0 : ((n • D : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_nsmul]
    exact addOrderOf_nsmul_eq_zero _
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
  have hpos : (0 : ℝ) < n * D := mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h)) hD
  have hk0 : (0 : ℝ) < k := by rw [hk]; exact hpos
  have hk0' : (0 : ℤ) < k := by exact_mod_cast hk0
  have hk1 : (1 : ℤ) ≤ k := by omega
  calc (1 : ℝ) ≤ k := by exact_mod_cast hk1
    _ = n * D := hk

/-- A random variable independent of itself is almost surely constant. -/
theorem ae_eq_const_of_indepFun_self {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] {f : Ω' → ℝ} (hf : Measurable f) (h : IndepFun f f μ) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, f x = c := by
  have h01 : ∀ U : Set ℝ, MeasurableSet U → (∀ᵐ x ∂μ, f x ∈ U) ∨ (∀ᵐ x ∂μ, f x ∉ U) := by
    intro U hU
    have hmul := h.measure_inter_preimage_eq_mul U U hU hU
    rw [Set.inter_self] at hmul
    by_cases h0 : μ (f ⁻¹' U) = 0
    · exact Or.inr (compl_mem_ae_iff.2 h0)
    · left
      have h1 : μ (f ⁻¹' U) = 1 := by
        have h' : μ (f ⁻¹' U) * μ (f ⁻¹' U) = μ (f ⁻¹' U) * 1 := by
          rw [mul_one]
          exact hmul.symm
        exact (ENNReal.mul_right_inj h0 (measure_ne_top _ _)).1 h'
      have hc : μ (f ⁻¹' U)ᶜ = 0 := (prob_compl_eq_zero_iff (hf hU)).2 h1
      exact mem_ae_iff.2 hc
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating MeasurableSet h01
  exact ⟨c, hc⟩

/-- **A function on the circle with arbitrarily small positive periods is constant** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-15.md`, line 49: "The periods are strictly positive and tend to zero ... The period
subgroup is closed ... so it is the whole circle. Thus `V` equals its phase average"). If `f` is measurable and, for
every `j`, `f((θ + D_j) mod 1) = f(θ)` for almost every `θ ∈ [0, 1]`, with `D_j > 0` and `D_j → 0`, then `f` is almost
everywhere constant on `[0, 1]`. The level sets of the lift of `f` to `ℝ/ℤ` are almost invariant under the rotations
by `D_j`; if one of them has infinite order it is ergodic, otherwise their orders are at least `1/D_j → ∞`. -/
theorem ae_eq_const_of_phasePeriods {f : ℝ → ℝ} (hf : Measurable f) {Dp : ℕ → ℝ} (hDpos : ∀ j, 0 < Dp j)
    (hD0 : Tendsto Dp atTop (𝓝 0))
    (hper : ∀ j, ∀ᵐ θ ∂zeroConePhase, f (toIcoMod (zero_lt_one' ℝ) 0 (θ + Dp j)) = f θ) :
    ∃ c : ℝ, ∀ᵐ θ ∂zeroConePhase, f θ = c := by
  set g : AddCircle (1 : ℝ) → ℝ := fun x => f (AddCircle.measurableEquivIco (1 : ℝ) 0 x : ℝ) with hgdef
  have hg : Measurable g :=
    hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)
  have hgcoe : ∀ y : ℝ, g y = f (toIcoMod (zero_lt_one' ℝ) 0 y) := fun y => by
    show f (AddCircle.measurableEquivIco (1 : ℝ) 0 (y : AddCircle (1 : ℝ)) : ℝ) = _
    rw [measurableEquivIco_coe_apply]
  have hZ : zeroConePhase = volume.restrict (Ioc (0 : ℝ) 1) := by
    show volume.restrict (Icc (0 : ℝ) 1) = _
    exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  have hπ : MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
    rwa [zero_add] at h
  have hIco : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) 1), θ ∈ Ico (0 : ℝ) (0 + 1) := by
    have hIoo : (volume : Measure ℝ).restrict (Ioo 0 1) = volume.restrict (Ioc 0 1) :=
      Measure.restrict_congr_set Ioo_ae_eq_Ioc
    rw [← hIoo]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [zero_add]
    exact Ioo_subset_Ico_self hθ
  -- the periods on the circle
  have hperC : ∀ j, ∀ᵐ x : AddCircle (1 : ℝ), g (((Dp j : ℝ) : AddCircle (1 : ℝ)) + x) = g x := by
    intro j
    have hS : MeasurableSet {x : AddCircle (1 : ℝ) | g (((Dp j : ℝ) : AddCircle (1 : ℝ)) + x) = g x} :=
      measurableSet_eq_fun (hg.comp (by fun_prop : Continuous fun x : AddCircle (1 : ℝ) =>
        ((Dp j : ℝ) : AddCircle (1 : ℝ)) + x).measurable) hg
    rw [← hπ.map_eq, ae_map_iff hπ.measurable.aemeasurable hS]
    have h1 := hper j
    rw [hZ] at h1
    filter_upwards [h1, hIco] with θ hθ hθI
    rw [← AddCircle.coe_add, hgcoe, hgcoe, add_comm (Dp j) θ, (toIcoMod_eq_self (zero_lt_one' ℝ)).2 hθI]
    exact hθ
  -- every level set is null or conull
  have hlev : ∀ U : Set ℝ, MeasurableSet U →
      (∀ᵐ x : AddCircle (1 : ℝ), g x ∈ U) ∨ (∀ᵐ x : AddCircle (1 : ℝ), g x ∉ U) := by
    intro U hU
    have hsm : MeasurableSet (g ⁻¹' U) := hg hU
    have hinv : ∀ j, (fun x => ((Dp j : ℝ) : AddCircle (1 : ℝ)) +ᵥ x) ⁻¹' (g ⁻¹' U) =ᵐ[volume] g ⁻¹' U := by
      intro j
      filter_upwards [hperC j] with x hx
      change (g (((Dp j : ℝ) : AddCircle (1 : ℝ)) + x) ∈ U) = (g x ∈ U)
      rw [hx]
    have hdich : g ⁻¹' U =ᵐ[volume] (∅ : Set (AddCircle (1 : ℝ))) ∨ g ⁻¹' U =ᵐ[volume] univ := by
      by_cases hord : ∃ j, addOrderOf ((Dp j : ℝ) : AddCircle (1 : ℝ)) = 0
      · obtain ⟨j, hj⟩ := hord
        have hdense : DenseRange (fun n : ℤ => n • ((Dp j : ℝ) : AddCircle (1 : ℝ))) :=
          AddCircle.denseRange_zsmul_iff.2 hj
        have herg : Ergodic (fun x : AddCircle (1 : ℝ) => ((Dp j : ℝ) : AddCircle (1 : ℝ)) +ᵥ x)
            (volume : Measure (AddCircle (1 : ℝ))) :=
          ergodic_vadd_of_denseRange_zsmul hdense volume
        exact herg.quasiErgodic.ae_empty_or_univ₀ hsm.nullMeasurableSet (hinv j)
      · have hord' : ∀ j, addOrderOf ((Dp j : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := not_exists.1 hord
        refine AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self hsm.nullMeasurableSet
          (l := atTop) (u := fun j => -((Dp j : ℝ) : AddCircle (1 : ℝ))) (fun j => ?_) ?_
        · show (-((Dp j : ℝ) : AddCircle (1 : ℝ))) +ᵥ g ⁻¹' U =ᵐ[volume] g ⁻¹' U
          rw [← Set.preimage_vadd]
          exact hinv j
        · refine tendsto_atTop.2 fun M => ?_
          have hε : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
          filter_upwards [hD0.eventually (gt_mem_nhds hε)] with j hj
          show M ≤ addOrderOf (-((Dp j : ℝ) : AddCircle (1 : ℝ)))
          rw [addOrderOf_neg]
          have hn := one_le_addOrderOf_mul (hDpos j) (hord' j)
          have hj' : Dp j * ((M : ℝ) + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hj
          have hlt : (M : ℝ) < addOrderOf ((Dp j : ℝ) : AddCircle (1 : ℝ)) := by
            nlinarith [hDpos j]
          exact (Nat.cast_lt.1 hlt).le
    rcases hdich with h0 | h1
    · exact Or.inr (compl_mem_ae_iff.2 (ae_eq_empty.1 h0))
    · exact Or.inl (mem_ae_iff.2 (ae_eq_univ.1 h1))
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating MeasurableSet hlev
  refine ⟨c, ?_⟩
  rw [hZ]
  filter_upwards [hπ.quasiMeasurePreserving.ae (p := fun x => g x = c) hc, hIco] with θ hθ hθI
  calc f θ = f (toIcoMod (zero_lt_one' ℝ) 0 θ) := by rw [(toIcoMod_eq_self (zero_lt_one' ℝ)).2 hθI]
    _ = g θ := (hgcoe θ).symm
    _ = c := hθ

/-- The reduction mod `1` of a phase shift preserves almost-everywhere statements for the uniform phase. -/
theorem ae_zeroConePhase_toIcoMod {p : ℝ → Prop} (d : ℝ) (h : ∀ᵐ θ ∂zeroConePhase, p θ) :
    ∀ᵐ θ ∂zeroConePhase, p (toIcoMod (zero_lt_one' ℝ) 0 (θ + d)) := by
  have hN0 : zeroConePhase (toMeasurable zeroConePhase {θ | ¬ p θ}) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 h
  have hpre : zeroConePhase ((fun x => toIcoMod (zero_lt_one' ℝ) 0 (x + d)) ⁻¹'
      toMeasurable zeroConePhase {θ | ¬ p θ}) = 0 := by
    rw [zeroConePhase_toIcoMod_preimage d (measurableSet_toMeasurable _ _)]
    exact hN0
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hpre
  exact subset_toMeasurable _ _ hθ

end Circle

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Arbitrarily small phase periods of the configuration observables** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-15.md`, lines 39-49: for a bounded invariant observable `V(h, e, θ)` of the configuration and
a smooth bump `b`, the field `h' = h + λ b` has an equivalent law (Cameron–Martin), the bump shifts the quantum times
of distant future and past roots by `D_+ = Δ(e([0, ∞)))` and `D_- = −Δ(e((−∞, 0]))`, `dΔ = (e^{γλb} − 1) dμ_h`
(line 41), the local approximations at uniform roots of both temporal halves give `V(h', e, {θ + D_±}) = V(h, e, θ)`
almost surely (lines 45-47), and "for almost every `h, e`, the circle function `V(h, e, ·)` has period `D` in `L¹`. Do
this for `λ = 1/j`. The periods are strictly positive and tend to zero, by full support and local finite mass"
(line 49); arXiv:1705.11161, lines 1193-1196). PENDING TRUTH CHECK.

For every realization `F` of the configuration (3.1) and every bounded measurable similarity-invariant `Φ`, almost
surely there are periods `D_j > 0` tending to `0` such that, for every `j`, `Φ(F(ω, (θ + D_j) mod 1)) = Φ(F(ω, θ))` for
almost every phase `θ`. -/
def ZeroConePhasePeriods (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
    ∀ Φ : GMSSpace → ℝ, Measurable Φ → (∃ M : ℝ, ∀ H, |Φ H| ≤ M) →
      (∀ (s : ℝ) (u) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' → Φ H' = Φ H) →
      ∀ᵐ ω ∂P, ∃ Dp : ℕ → ℝ, (∀ j, 0 < Dp j) ∧ Tendsto Dp atTop (𝓝 0) ∧
        ∀ j, ∀ᵐ θ ∂zeroConePhase, Φ (F (ω, toIcoMod (zero_lt_one' ℝ) 0 (θ + Dp j))) = Φ (F (ω, θ))

/-- **The step from `(h, η̂)` to `θ`** (arXiv:1705.11161, lines 1193-1196; written answer
`notes/fp-gaps/CODEX-MQ-sbl-15.md`, lines 37-49) from the configuration code (3.1)-(3.2) and the phase periods. With
`Cfg` the code of `ZeroConeConfigCovariance` and `H'` a measurable version of the zero-cone field, `Φ(F(ω, θ))` is
almost surely `v(H'(ω), ηL(ω), θ) = Φ(Cfg((H'(ω), ηL(ω)), θ))`; for almost every `ω` the circle function `v(H'(ω), ηL(ω), ·)`
has arbitrarily small periods, hence equals its phase average `m(H'(ω), ηL(ω))`. So `Φ(F)` is almost surely a measurable
function of `(h, η̂)`; being independent of `(h, η̂)` it is independent of itself, hence almost surely constant. -/
theorem zeroConePhaseFactorStep (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hcov : ZeroConeConfigCovariance D hγ) (hper : ZeroConePhasePeriods D hγ) :
    ZeroConePhaseFactorStep D hγ := by
  intro G F hF Φ hΦm hΦb hΦinv hind
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Cfg, hCm, hCF, -⟩ := hcov
  obtain ⟨H', hH'm, -, hH'eq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hηm : Measurable ηL := D.measurable_curves.1
  set Y : Ω → Field × C(ℝ, ℂ) := fun ω => (H' ω, ηL ω) with hYdef
  have hYm : Measurable Y := hH'm.prodMk hηm
  set v : (Field × C(ℝ, ℂ)) × ℝ → ℝ := fun q => Φ (Cfg q) with hvdef
  have hvm : Measurable v := hΦm.comp hCm
  set m : Field × C(ℝ, ℂ) → ℝ := fun y => ∫ θ, v (y, θ) ∂zeroConePhase with hmdef
  have hms : StronglyMeasurable fun y : Field × C(ℝ, ℂ) => ∫ θ, v (y, θ) ∂zeroConePhase :=
    hvm.stronglyMeasurable.integral_prod_right'
  have hmm : Measurable m := hms.measurable
  have hYfst : Measurable fun p : Ω × ℝ => Y p.1 := hYm.comp measurable_fst
  -- the observable is the code read at a measurable version of the zero-cone field
  have hH'eq' : ∀ᵐ ω ∂P, H' ω = zeroConeFieldOf γ X₀ B₀ B₀' ω := hH'eq
  have hFv : ∀ᵐ p ∂P.prod zeroConePhase, Φ (F p) = v (Y p.1, p.2) := by
    filter_upwards [hCF G F hF, Measure.quasiMeasurePreserving_fst.ae hH'eq'] with p hp hq
    rw [hp]
    show Φ (Cfg ((zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1), p.2)) = Φ (Cfg ((H' p.1, ηL p.1), p.2))
    rw [hq]
  -- for almost every sample the circle function equals its phase average
  have hS5 : ∀ᵐ ω ∂P, ∀ᵐ θ ∂zeroConePhase, v (Y ω, θ) = m (Y ω) := by
    filter_upwards [hper G F hF Φ hΦm hΦb hΦinv, Measure.ae_ae_of_ae_prod hFv] with ω hωp hωF
    obtain ⟨Dp, hDpos, hD0, hDper⟩ := hωp
    have hvper : ∀ j, ∀ᵐ θ ∂zeroConePhase,
        v (Y ω, toIcoMod (zero_lt_one' ℝ) 0 (θ + Dp j)) = v (Y ω, θ) := by
      intro j
      filter_upwards [ae_zeroConePhase_toIcoMod (Dp j) hωF, hωF, hDper j] with θ h1 h2 h3
      exact h1.symm.trans (h3.trans h2)
    obtain ⟨c, hc⟩ := ae_eq_const_of_phasePeriods (f := fun θ => v (Y ω, θ))
      (hvm.comp measurable_prodMk_left) hDpos hD0 hvper
    have hmc : m (Y ω) = c := by
      calc m (Y ω) = ∫ _θ, c ∂zeroConePhase := integral_congr_ae hc
        _ = c := by simp
    filter_upwards [hc] with θ hθ
    rw [hmc]
    exact hθ
  have hmeasS : MeasurableSet {p : Ω × ℝ | v (Y p.1, p.2) = m (Y p.1)} :=
    measurableSet_eq_fun (hvm.comp (hYfst.prodMk measurable_snd)) (hmm.comp hYfst)
  have hS6 : ∀ᵐ p ∂P.prod zeroConePhase, v (Y p.1, p.2) = m (Y p.1) :=
    (Measure.ae_prod_iff_ae_ae hmeasS).2 hS5
  have hΦm' : (fun p : Ω × ℝ => Φ (F p)) =ᵐ[P.prod zeroConePhase] fun p => m (Y p.1) := by
    filter_upwards [hFv, hS6] with p h1 h2
    exact h1.trans h2
  have hYeq : (fun p : Ω × ℝ => (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1)) =ᵐ[P.prod zeroConePhase]
      fun p => Y p.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hH'eq'] with p hp
    show (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1) = (H' p.1, ηL p.1)
    rw [hp]
  -- a function of `(h, η̂)` independent of `(h, η̂)` is constant
  have hind1 := hind.congr hΦm' hYeq
  have hind2 := hind1.comp measurable_id hmm
  obtain ⟨c, hc⟩ := ae_eq_const_of_indepFun_self (f := fun p : Ω × ℝ => m (Y p.1)) (hmm.comp hYfst) hind2
  refine ⟨c, ?_⟩
  filter_upwards [hΦm', hc] with p h1 h2
  exact h1.trans h2

end Hypotheses

end MatedCRT
