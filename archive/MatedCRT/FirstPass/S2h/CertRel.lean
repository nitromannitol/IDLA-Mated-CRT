import MatedCRT.FirstPass.S2g.Family

/-!
# The certificate relation is Borel and its code projection is analytic

For fixed countable data (dense points `z j` of `B_{3/4} \ {0}`, boundary points `b j`, rational balls `U V`, the
coordinate index `idx k J n` of the cutoff moments and the countably many Laplacian functionals `L k`), the relation
`CertRel m t w` is Borel in `(m, w)` for each fixed `t`. Its projection over rational pairs `0 < p < q` is analytic
(Lusin; Kechris 14.3). The data enter only as parameters; the identification of the coordinates with the cutoff
integrals is part of `CertCodeExactStep` and is not proved here.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal
open Classical

/-- The witness space `W = C(B̄_{3/4}, ℝ)` -/
abbrev DiscW : Type := ContinuousMap (closedBall (0 : ℂ) (3 / 4)) ℝ

/-! ### Measurability combinators (countable quantifiers) -/

theorem cr_forall {X ι : Type} [MeasurableSpace X] [Countable ι] {P : ι → X → Prop}
    (h : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∀ i, P i x} := by
  have : {x | ∀ i, P i x} = ⋂ i, {x | P i x} := by
    ext x
    simp
  rw [this]
  exact MeasurableSet.iInter h

theorem cr_exists {X ι : Type} [MeasurableSpace X] [Countable ι] {P : ι → X → Prop}
    (h : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∃ i, P i x} := by
  have : {x | ∃ i, P i x} = ⋃ i, {x | P i x} := by
    ext x
    simp
  rw [this]
  exact MeasurableSet.iUnion h

theorem cr_imp {X : Type} [MeasurableSpace X] {P Q : X → Prop} (hP : MeasurableSet {x | P x})
    (hQ : MeasurableSet {x | Q x}) : MeasurableSet {x | P x → Q x} := by
  have : {x | P x → Q x} = {x | P x}ᶜ ∪ {x | Q x} := by
    ext x
    simp [imp_iff_not_or]
  rw [this]
  exact hP.compl.union hQ

theorem cr_and {X : Type} [MeasurableSpace X] {P Q : X → Prop} (hP : MeasurableSet {x | P x})
    (hQ : MeasurableSet {x | Q x}) : MeasurableSet {x | P x ∧ Q x} :=
  hP.inter hQ

/-! ### The data and the relation -/

variable (z : ℕ → closedBall (0 : ℂ) (3 / 4)) (b : ℕ → closedBall (0 : ℂ) (3 / 4))
  (U : ℕ → Set ℂ) (idx : ℕ → Finset ℕ → ℕ → ℕ) (L : ℕ → DiscW → ℝ)

/-- The raw field `u_{t,w}(x) = w(x) + t G_{B_{3/4}}(0,x)`; only used at non-pole points `x`. -/
noncomputable def certRaw (t : ℝ) (w : DiscW) (x : closedBall (0 : ℂ) (3 / 4)) : ℝ :=
  w x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (x : ℂ)

/-- The predicate `D_B(t,w)` for the ball `U i`: every rational ball `U V` whose closure lies in
`U i` meets the raw cluster at some dense point. -/
def certD (t : ℝ) (w : DiscW) (i : ℕ) : Prop :=
  ∀ V : ℕ, closure (U V) ⊆ U i → ∃ j, (z j : ℂ) ∈ U V ∧ 0 < certRaw t w (z j)

/-- The cutoff coordinate supremum `I_k(m,t,w)`. -/
noncomputable def certI (m : ℕ → ℝ) (t : ℝ) (w : DiscW) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (J : Finset ℕ) (n : ℕ),
    if (∀ i ∈ J, certD z U t w i) then ENNReal.ofReal (m (idx k J n)) else 0

/-- The Borel relation `Cert(m,t,w)`, conditions C1 (15), C2 (16), C3 (17)-(18), C4 (20). -/
def CertRel (m : ℕ → ℝ) (t : ℝ) (w : DiscW) : Prop :=
  (∀ j, 0 ≤ certRaw t w (z j)) ∧
  (∀ j, w (b j) = 0) ∧
  (∀ j, 0 < certRaw t w (z j) → ‖(z j : ℂ)‖ ≤ 1 / 2) ∧
  (∀ n : ℕ, ∃ j, 0 < certRaw t w (z j) ∧ (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖(z j : ℂ)‖) ∧
  (∀ k, certI z U idx m t w k < ⊤ ∧ L k w = (certI z U idx m t w k).toReal)

/-! ### Measurability of the pieces, for a fixed time `t` -/

variable {z b U idx L}

theorem cr_measurable_raw (t : ℝ) (j : ℕ) :
    Measurable fun p : (ℕ → ℝ) × DiscW => certRaw t p.2 (z j) := by
  have hc : Continuous fun p : (ℕ → ℝ) × DiscW =>
      p.2 (z j) + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (z j : ℂ) :=
    ((continuous_eval_const (z j)).comp continuous_snd).add continuous_const
  exact hc.measurable

theorem cr_measurable_eval (j : ℕ) :
    Measurable fun p : (ℕ → ℝ) × DiscW => p.2 (b j) := by
  have hc : Continuous fun p : (ℕ → ℝ) × DiscW => p.2 (b j) :=
    (continuous_eval_const (b j)).comp continuous_snd
  exact hc.measurable

theorem cr_measurableSet_D (t : ℝ) (i : ℕ) :
    MeasurableSet {p : (ℕ → ℝ) × DiscW | certD z U t p.2 i} := by
  unfold certD
  refine cr_forall fun V => cr_imp (MeasurableSet.const _) ?_
  refine cr_exists fun j => cr_and (MeasurableSet.const _) ?_
  exact measurableSet_lt measurable_const (cr_measurable_raw t j)

theorem cr_measurable_I (t : ℝ) (k : ℕ) :
    Measurable fun p : (ℕ → ℝ) × DiscW => certI z U idx p.1 t p.2 k := by
  unfold certI
  refine Measurable.iSup fun J => Measurable.iSup fun n => ?_
  have hcond : MeasurableSet {p : (ℕ → ℝ) × DiscW | ∀ i ∈ J, certD z U t p.2 i} :=
    cr_forall fun i => cr_imp (MeasurableSet.const _) (cr_measurableSet_D t i)
  refine Measurable.ite hcond ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply (idx k J n)).comp measurable_fst)

/-- **The relation is Borel.** For fixed `t`, the set of pairs `(m, w)` with `Cert(m,t,w)` is measurable
in the product `(ℕ → ℝ) × C(B̄_{3/4}, ℝ)`, provided each `L k` is continuous (all tests in C1–C4 are countable Borel tests). -/
theorem measurableSet_certRel (hL : ∀ k, Continuous (L k)) (t : ℝ) :
    MeasurableSet {p : (ℕ → ℝ) × DiscW | CertRel z b U idx L p.1 t p.2} := by
  unfold CertRel
  have h1 : MeasurableSet {p : (ℕ → ℝ) × DiscW | ∀ j, 0 ≤ certRaw t p.2 (z j)} :=
    cr_forall fun j => measurableSet_le measurable_const (cr_measurable_raw t j)
  have h2 : MeasurableSet {p : (ℕ → ℝ) × DiscW | ∀ j, p.2 (b j) = 0} :=
    cr_forall fun j => measurableSet_eq_fun (cr_measurable_eval j) measurable_const
  have h3 : MeasurableSet {p : (ℕ → ℝ) × DiscW |
      ∀ j, 0 < certRaw t p.2 (z j) → ‖(z j : ℂ)‖ ≤ 1 / 2} :=
    cr_forall fun j => cr_imp (measurableSet_lt measurable_const (cr_measurable_raw t j))
      (MeasurableSet.const _)
  have h4 : MeasurableSet {p : (ℕ → ℝ) × DiscW |
      ∀ n : ℕ, ∃ j, 0 < certRaw t p.2 (z j) ∧ (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖(z j : ℂ)‖} :=
    cr_forall fun n => cr_exists fun j =>
      cr_and (measurableSet_lt measurable_const (cr_measurable_raw t j)) (MeasurableSet.const _)
  have h5 : MeasurableSet {p : (ℕ → ℝ) × DiscW |
      ∀ k, certI z U idx p.1 t p.2 k < ⊤ ∧ L k p.2 = (certI z U idx p.1 t p.2 k).toReal} :=
    cr_forall fun k => cr_and (measurableSet_lt (cr_measurable_I t k) measurable_const)
      (measurableSet_eq_fun ((hL k).measurable.comp measurable_snd)
        (ENNReal.measurable_toReal.comp (cr_measurable_I t k)))
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

/-- **The code projection is analytic.** The set of moment codes `m` for which some rational pair
`0 < p < q` carries two relation witnesses `Cert(m,p,·)` and `Cert(m,q,·)` is analytic (Lusin, Kechris 14.3). -/
theorem analyticSet_certCodes (hL : ∀ k, Continuous (L k)) :
    AnalyticSet {m : ℕ → ℝ | ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧
      ∃ w : DiscW, CertRel z b U idx L m (p : ℝ) w ∧ ∃ w' : DiscW, CertRel z b U idx L m (q : ℝ) w'} := by
  have hpair : ∀ pq : ℚ × ℚ, MeasurableSet {x : (ℕ → ℝ) × DiscW × DiscW |
      (0 < (pq.1 : ℝ) ∧ (pq.1 : ℝ) < (pq.2 : ℝ)) ∧
        CertRel z b U idx L x.1 (pq.1 : ℝ) x.2.1 ∧ CertRel z b U idx L x.1 (pq.2 : ℝ) x.2.2} := by
    intro pq
    have hA : MeasurableSet {x : (ℕ → ℝ) × DiscW × DiscW | CertRel z b U idx L x.1 (pq.1 : ℝ) x.2.1} :=
      (measurableSet_certRel hL (pq.1 : ℝ)).preimage
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hB : MeasurableSet {x : (ℕ → ℝ) × DiscW × DiscW | CertRel z b U idx L x.1 (pq.2 : ℝ) x.2.2} :=
      (measurableSet_certRel hL (pq.2 : ℝ)).preimage
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact cr_and (MeasurableSet.const _) (hA.inter hB)
  have heq : {m : ℕ → ℝ | ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧
      ∃ w : DiscW, CertRel z b U idx L m (p : ℝ) w ∧ ∃ w' : DiscW, CertRel z b U idx L m (q : ℝ) w'} =
      ⋃ pq : ℚ × ℚ, Prod.fst '' {x : (ℕ → ℝ) × DiscW × DiscW |
        (0 < (pq.1 : ℝ) ∧ (pq.1 : ℝ) < (pq.2 : ℝ)) ∧
          CertRel z b U idx L x.1 (pq.1 : ℝ) x.2.1 ∧ CertRel z b U idx L x.1 (pq.2 : ℝ) x.2.2} := by
    ext m
    constructor
    · rintro ⟨p, q, hp, hpq, w, hw, w', hw'⟩
      exact mem_iUnion.2 ⟨(p, q), ⟨(m, w, w'), ⟨⟨hp, hpq⟩, hw, hw'⟩, rfl⟩⟩
    · intro h
      obtain ⟨⟨p, q⟩, hx⟩ := mem_iUnion.1 h
      obtain ⟨x, ⟨⟨hp, hpq⟩, hw, hw'⟩, hxm⟩ := hx
      refine ⟨p, q, hp, hpq, x.2.1, ?_, x.2.2, ?_⟩
      · rw [← hxm]
        exact hw
      · rw [← hxm]
        exact hw'
  rw [heq]
  exact AnalyticSet.iUnion fun pq => (hpair pq).analyticSet_image measurable_fst

end MatedCRT
