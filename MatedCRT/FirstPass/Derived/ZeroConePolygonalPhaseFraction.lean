import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseTilt
import MatedCRT.FirstPass.Derived.ZeroConeCircleAverageInputsProof
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Prob.KernelCurveImage
import LatticeProb.Prob.DyadicCellMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Core

/-!
# The covered fraction of a root square by a time half of the space-filling curve

Let `μ_ω` be the area measure of the zero-cone field, `y` an independent uniform dyadic grid, and `S_m(ω, y)` the square
of the grid chain at the origin that is the largest of `μ_ω`-mass at most `m` (`ZeroConeRoot.rootGen`). For a time half
`e[0, ∞)` or `e(-∞, 0]` of the Lebesgue-parametrized space-filling curve `e = ηL`, this file proves that the fraction of
`S_m` covered by the time half is bounded below with probability close to one, uniformly in `m`:
for every `ε > 0` there is `δ > 0` with
`P ⊗ (grid) {Leb(S_m ∩ e(time half)) < δ Leb(S_m)} ≤ ε` for all `m ∈ (0, ∞)`.

The proof follows the three steps of the quadrant argument.

* A closed square of side `ℓ` containing `0` contains one of the four quadrant squares of side `ℓ / 2` having `0` as a
  corner (`exists_quadFit`, `quadSq_subset_cornerSquare`). The index of the quadrant and `ℓ` are functions of
  `(μ_ω, y)` and of `m` only, and `(μ_ω, y)` is independent of `ηL`
  (`exists_zeroConeField_version_indepFun_igCurve`), so the four cases are handled by a union bound and Fubini's theorem.
* The law of `ηL` is invariant under `affineReroot 0 s φ` for every `s > 0` and every angle `φ`
  (`IsMatingOfTreesCoupling.map_affineReroot_ηL`), and `affineReroot 0 s φ ηL` is the curve `(s e^{iφ})⁻¹ ηL(s² ·)`
  because `ηL` first visits `0` at time `0` almost surely. Consequently the law of the covered fraction of a quadrant
  square of side `r` does not depend on `r` or on the quadrant (`measure_quadSq_lt`).
* The covered fraction of the unit square is positive almost surely (`ae_pos_unitSquare`): the events
  `{Leb(Q_n ∩ time half) > 0}` for the quadrant squares `Q_n` of side `2^{-n}` decrease in `n`; for each `n` at least one of
  the four quadrants has the event, because `ηL[0, t]` has area `t > 0` and lies in the disk of radius `2^{-n}` for small `t`;
  by the rotation invariance of the law all four quadrants have the same probability, hence probability at least `1/4`;
  the limit event is invariant under `affineReroot 0 2 0`, and
  `ae_eq_const_of_affineReroot_two_invariant` shows that it has probability one.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open LatticeProb.DyadicOffset (cornerSquare mem_cornerSquare isClosed_cornerSquare volume_cornerSquare
  gridFloor squareAt mem_squareAt)
open scoped NNReal ENNReal

/-! ### Squares and quadrants -/

section Geometry

/-- The closed unit square `[0, 1]²` of the plane. -/
def unitSquare : Set ℂ := cornerSquare 0 0 1

/-- Membership in the closed unit square, in coordinates. -/
theorem mem_unitSquare {v : ℂ} : v ∈ unitSquare ↔ 0 ≤ v.re ∧ v.re ≤ 1 ∧ 0 ≤ v.im ∧ v.im ≤ 1 := by
  simp [unitSquare, mem_cornerSquare]

/-- The closed unit square is measurable. -/
theorem measurableSet_unitSquare : MeasurableSet unitSquare :=
  (isClosed_cornerSquare 0 0 1).measurableSet

/-- The four quadrants at the origin, indexed by the signs of the real and imaginary parts (`true` for the
nonnegative side). -/
abbrev Quad : Type := Bool × Bool

/-- There are four quadrants. -/
theorem card_quad : Fintype.card Quad = 4 := by simp

/-- The quarter turn carrying the unit square to the quadrant `q`. -/
def quadUnit (q : Quad) : ℂ :=
  if q.1 then (if q.2 then 1 else -Complex.I) else (if q.2 then Complex.I else -1)

/-- The angle of the quarter turn `quadUnit q`. -/
def quadAngle (q : Quad) : ℝ :=
  if q.1 then (if q.2 then 0 else -(Real.pi / 2)) else (if q.2 then Real.pi / 2 else Real.pi)

/-- The exponential of a real multiple of `I` in terms of cosine and sine. -/
theorem exp_ofReal_mul_I' (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `quadUnit q = e^{i · quadAngle q}`. -/
theorem exp_quadAngle (q : Quad) : Complex.exp ((quadAngle q : ℝ) * Complex.I) = quadUnit q := by
  obtain ⟨σ, τ⟩ := q
  rw [exp_ofReal_mul_I']
  cases σ <;> cases τ <;> simp [quadAngle, quadUnit]

/-- The quarter turns are nonzero and of norm one. -/
theorem normSq_quadUnit (q : Quad) : Complex.normSq (quadUnit q) = 1 := by
  obtain ⟨σ, τ⟩ := q
  cases σ <;> cases τ <;> simp [quadUnit]

/-- The quarter turns are nonzero. -/
theorem quadUnit_ne_zero (q : Quad) : quadUnit q ≠ 0 := by
  intro h
  have := normSq_quadUnit q
  rw [h] at this
  simp at this

/-- One coordinate of a quadrant square of side `r`: `[0, r]` (`σ = true`) or `[-r, 0]` (`σ = false`). -/
def cond1 (σ : Bool) (r x : ℝ) : Prop := if σ then 0 ≤ x ∧ x ≤ r else -r ≤ x ∧ x ≤ 0

/-- One coordinate of the fitting condition of a quadrant square of side `ℓ / 2` in `[a, a + ℓ]`. -/
def fit1 (σ : Bool) (a ℓ : ℝ) : Prop :=
  if σ then a ≤ 0 ∧ ℓ / 2 ≤ a + ℓ else a ≤ -(ℓ / 2) ∧ 0 ≤ a + ℓ

/-- The closed quadrant square of side `r` at the origin in the quadrant `q`. -/
def quadSq (q : Quad) (r : ℝ) : Set ℂ := {w | cond1 q.1 r w.re ∧ cond1 q.2 r w.im}

/-- Membership in a quadrant square, in coordinates. -/
theorem mem_quadSq {q : Quad} {r : ℝ} {w : ℂ} : w ∈ quadSq q r ↔ cond1 q.1 r w.re ∧ cond1 q.2 r w.im :=
  Iff.rfl

/-- The coordinate condition on the nonnegative side. -/
@[simp] theorem cond1_pos (r x : ℝ) : cond1 true r x = (0 ≤ x ∧ x ≤ r) := by simp [cond1]

/-- The coordinate condition on the nonpositive side. -/
@[simp] theorem cond1_neg (r x : ℝ) : cond1 false r x = (-r ≤ x ∧ x ≤ 0) := by simp [cond1]

/-- The fitting condition on the nonnegative side. -/
@[simp] theorem fit1_pos (a ℓ : ℝ) : fit1 true a ℓ = (a ≤ 0 ∧ ℓ / 2 ≤ a + ℓ) := by simp [fit1]

/-- The fitting condition on the nonpositive side. -/
@[simp] theorem fit1_neg (a ℓ : ℝ) : fit1 false a ℓ = (a ≤ -(ℓ / 2) ∧ 0 ≤ a + ℓ) := by simp [fit1]

/-- The quadrant `q` of side `ℓ / 2` fits in the square with lower left corner `(a, c)` and side `ℓ`. -/
def quadFit (q : Quad) (a c ℓ : ℝ) : Prop := fit1 q.1 a ℓ ∧ fit1 q.2 c ℓ

/-- A coordinate condition is monotone in the side. -/
theorem cond1_mono (σ : Bool) {r r' x : ℝ} (h : r' ≤ r) (hx : cond1 σ r' x) : cond1 σ r x := by
  cases σ
  · rw [cond1_neg] at hx ⊢
    exact ⟨by linarith [hx.1], hx.2⟩
  · rw [cond1_pos] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩

/-- A real number of absolute value at most `r` satisfies the coordinate condition on one of the two sides. -/
theorem exists_cond1 {r x : ℝ} (hx : |x| ≤ r) : ∃ σ, cond1 σ r x := by
  have h := abs_le.1 hx
  rcases le_total 0 x with h0 | h0
  · exact ⟨true, by rw [cond1_pos]; exact ⟨h0, h.2⟩⟩
  · exact ⟨false, by rw [cond1_neg]; exact ⟨h.1, h0⟩⟩

/-- The coordinate condition for the side `ℓ / 2` together with the fitting condition places the coordinate in
`[a, a + ℓ]`. -/
theorem cond1_of_fit1 {σ : Bool} {a ℓ x : ℝ} (hf : fit1 σ a ℓ) (hc : cond1 σ (ℓ / 2) x) :
    a ≤ x ∧ x ≤ a + ℓ := by
  cases σ
  · rw [fit1_neg] at hf
    rw [cond1_neg] at hc
    exact ⟨by linarith [hf.1, hc.1], by linarith [hf.2, hc.2]⟩
  · rw [fit1_pos] at hf
    rw [cond1_pos] at hc
    exact ⟨by linarith [hf.1, hc.1], by linarith [hf.2, hc.2]⟩

/-- An interval of length `ℓ` containing `0` fits a half of length `ℓ / 2` on one of the two sides. -/
theorem exists_fit1 {a ℓ : ℝ} (ha : a ≤ 0) (ha' : 0 ≤ a + ℓ) : ∃ σ, fit1 σ a ℓ := by
  by_cases h : -(ℓ / 2) ≤ a
  · exact ⟨true, by rw [fit1_pos]; exact ⟨ha, by linarith⟩⟩
  · exact ⟨false, by rw [fit1_neg]; exact ⟨(not_le.1 h).le, ha'⟩⟩

/-- A closed square of side `ℓ` containing `0` contains one of the four quadrant squares of side `ℓ / 2` at `0`. -/
theorem exists_quadFit {a c ℓ : ℝ} (ha : a ≤ 0) (ha' : 0 ≤ a + ℓ) (hc : c ≤ 0) (hc' : 0 ≤ c + ℓ) :
    ∃ q : Quad, quadFit q a c ℓ := by
  obtain ⟨σ, hσ⟩ := exists_fit1 ha ha'
  obtain ⟨τ, hτ⟩ := exists_fit1 hc hc'
  exact ⟨(σ, τ), hσ, hτ⟩

/-- A fitting quadrant square lies in the square. -/
theorem quadSq_subset_cornerSquare {q : Quad} {a c ℓ : ℝ} (h : quadFit q a c ℓ) :
    quadSq q (ℓ / 2) ⊆ cornerSquare a c ℓ := fun w hw => by
  rw [mem_cornerSquare]
  obtain ⟨h1, h2⟩ := cond1_of_fit1 h.1 (mem_quadSq.1 hw).1
  obtain ⟨h3, h4⟩ := cond1_of_fit1 h.2 (mem_quadSq.1 hw).2
  exact ⟨h1, h2, h3, h4⟩

/-- Quadrant squares are monotone in the side. -/
theorem quadSq_mono (q : Quad) {r r' : ℝ} (h : r' ≤ r) : quadSq q r' ⊆ quadSq q r := fun _ hw =>
  mem_quadSq.2 ⟨cond1_mono _ h (mem_quadSq.1 hw).1, cond1_mono _ h (mem_quadSq.1 hw).2⟩

/-- A point whose coordinates are at most `r` in absolute value lies in a quadrant square of side `r`. -/
theorem exists_mem_quadSq {r : ℝ} {w : ℂ} (h1 : |w.re| ≤ r) (h2 : |w.im| ≤ r) : ∃ q : Quad, w ∈ quadSq q r := by
  obtain ⟨σ, hσ⟩ := exists_cond1 h1
  obtain ⟨τ, hτ⟩ := exists_cond1 h2
  exact ⟨(σ, τ), mem_quadSq.2 ⟨hσ, hτ⟩⟩

/-- The quadrant square of side `1` in the nonnegative quadrant is the unit square. -/
theorem quadSq_true_one : quadSq (true, true) 1 = unitSquare := by
  ext w
  rw [mem_quadSq, mem_unitSquare]
  simp only [cond1_pos]
  tauto

/-- The coordinate sets of the quadrant squares are measurable, also when the side and the point depend measurably
on a parameter. -/
theorem measurableSet_cond1 {α : Type*} [MeasurableSpace α] {r x : α → ℝ} (hr : Measurable r) (hx : Measurable x)
    (σ : Bool) : MeasurableSet {p | cond1 σ (r p) (x p)} := by
  cases σ
  · simp only [cond1_neg]
    exact (measurableSet_le hr.neg hx).inter (measurableSet_le hx measurable_const)
  · simp only [cond1_pos]
    exact (measurableSet_le measurable_const hx).inter (measurableSet_le hx hr)

/-- Quadrant squares are measurable. -/
theorem measurableSet_quadSq (q : Quad) (r : ℝ) : MeasurableSet (quadSq q r) :=
  (measurableSet_cond1 (α := ℂ) measurable_const Complex.measurable_re q.1).inter
    (measurableSet_cond1 (α := ℂ) measurable_const Complex.measurable_im q.2)

/-- The set of parameters for which a quadrant square fits is measurable. -/
theorem measurableSet_quadFit {α : Type*} [MeasurableSpace α] {a c ℓ : α → ℝ} (ha : Measurable a)
    (hc : Measurable c) (hℓ : Measurable ℓ) (q : Quad) :
    MeasurableSet {p | quadFit q (a p) (c p) (ℓ p)} := by
  have h1 : ∀ (σ : Bool) (u : α → ℝ), Measurable u → MeasurableSet {p | fit1 σ (u p) (ℓ p)} := by
    intro σ u hu
    cases σ
    · simp only [fit1_neg]
      exact (measurableSet_le hu (hℓ.div_const 2).neg).inter (measurableSet_le measurable_const (hu.add hℓ))
    · simp only [fit1_pos]
      exact (measurableSet_le hu measurable_const).inter (measurableSet_le (hℓ.div_const 2) (hu.add hℓ))
  exact (h1 q.1 a ha).inter (h1 q.2 c hc)

end Geometry

/-! ### Scaling of the area -/

section Scaling

/-- Multiplication by a complex number `c` scales the plane area by `|c|²`. -/
theorem volume_image_mul_left (c : ℂ) (T : Set ℂ) :
    volume ((fun w => c * w) '' T) = ENNReal.ofReal (Complex.normSq c) * volume T := by
  have h := Measure.addHaar_image_linearMap (volume : Measure ℂ) (LinearMap.mulLeft ℝ c) T
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ c : ℂ →ₗ[ℝ] ℂ) = Complex.normSq c := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  rw [hdet, abs_of_nonneg (Complex.normSq_nonneg c)] at h
  exact h

/-- A quadrant square is the image of the unit square under the rotation-dilation `r · quadUnit q`. -/
theorem quadSq_eq_image {r : ℝ} (hr : 0 < r) (q : Quad) :
    quadSq q r = (fun v => ((r : ℂ) * quadUnit q) * v) '' unitSquare := by
  have hrne : r ≠ 0 := hr.ne'
  ext w
  obtain ⟨σ, τ⟩ := q
  constructor
  · intro hw
    have hw1 : cond1 σ r w.re := (mem_quadSq.1 hw).1
    have hw2 : cond1 τ r w.im := (mem_quadSq.1 hw).2
    cases σ <;> cases τ
    · rw [cond1_neg] at hw1 hw2
      refine ⟨⟨-w.re / r, -w.im / r⟩, ?_, ?_⟩
      · rw [mem_unitSquare]
        exact ⟨div_nonneg (by linarith [hw1.2]) hr.le, (div_le_one hr).2 (by linarith [hw1.1]),
          div_nonneg (by linarith [hw2.2]) hr.le, (div_le_one hr).2 (by linarith [hw2.1])⟩
      · apply Complex.ext <;> simp [quadUnit] <;> (try field_simp) <;> (try ring)
    · rw [cond1_neg] at hw1
      rw [cond1_pos] at hw2
      refine ⟨⟨w.im / r, -w.re / r⟩, ?_, ?_⟩
      · rw [mem_unitSquare]
        exact ⟨div_nonneg hw2.1 hr.le, (div_le_one hr).2 hw2.2,
          div_nonneg (by linarith [hw1.2]) hr.le, (div_le_one hr).2 (by linarith [hw1.1])⟩
      · apply Complex.ext <;> simp [quadUnit] <;> (try field_simp) <;> (try ring)
    · rw [cond1_pos] at hw1
      rw [cond1_neg] at hw2
      refine ⟨⟨-w.im / r, w.re / r⟩, ?_, ?_⟩
      · rw [mem_unitSquare]
        exact ⟨div_nonneg (by linarith [hw2.2]) hr.le, (div_le_one hr).2 (by linarith [hw2.1]),
          div_nonneg hw1.1 hr.le, (div_le_one hr).2 hw1.2⟩
      · apply Complex.ext <;> simp [quadUnit] <;> (try field_simp) <;> (try ring)
    · rw [cond1_pos] at hw1 hw2
      refine ⟨⟨w.re / r, w.im / r⟩, ?_, ?_⟩
      · rw [mem_unitSquare]
        exact ⟨div_nonneg hw1.1 hr.le, (div_le_one hr).2 hw1.2, div_nonneg hw2.1 hr.le,
          (div_le_one hr).2 hw2.2⟩
      · apply Complex.ext <;> simp [quadUnit] <;> (try field_simp) <;> (try ring)
  · rintro ⟨v, hv, rfl⟩
    rw [mem_unitSquare] at hv
    have p1 : 0 ≤ r * v.re := mul_nonneg hr.le hv.1
    have p2 : r * v.re ≤ r := mul_le_of_le_one_right hr.le hv.2.1
    have p3 : 0 ≤ r * v.im := mul_nonneg hr.le hv.2.2.1
    have p4 : r * v.im ≤ r := mul_le_of_le_one_right hr.le hv.2.2.2
    cases σ <;> cases τ
    · have e1 : (((r : ℂ) * quadUnit (false, false)) * v).re = -(r * v.re) := by
        simp [quadUnit, Complex.mul_re] <;> ring
      have e2 : (((r : ℂ) * quadUnit (false, false)) * v).im = -(r * v.im) := by
        simp [quadUnit, Complex.mul_im] <;> ring
      show cond1 false r (((r : ℂ) * quadUnit (false, false)) * v).re ∧
        cond1 false r (((r : ℂ) * quadUnit (false, false)) * v).im
      rw [e1, e2, cond1_neg, cond1_neg]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have e1 : (((r : ℂ) * quadUnit (false, true)) * v).re = -(r * v.im) := by
        simp [quadUnit, Complex.mul_re] <;> ring
      have e2 : (((r : ℂ) * quadUnit (false, true)) * v).im = r * v.re := by
        simp [quadUnit, Complex.mul_im] <;> ring
      show cond1 false r (((r : ℂ) * quadUnit (false, true)) * v).re ∧
        cond1 true r (((r : ℂ) * quadUnit (false, true)) * v).im
      rw [e1, e2, cond1_neg, cond1_pos]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have e1 : (((r : ℂ) * quadUnit (true, false)) * v).re = r * v.im := by
        simp [quadUnit, Complex.mul_re] <;> ring
      have e2 : (((r : ℂ) * quadUnit (true, false)) * v).im = -(r * v.re) := by
        simp [quadUnit, Complex.mul_im] <;> ring
      show cond1 true r (((r : ℂ) * quadUnit (true, false)) * v).re ∧
        cond1 false r (((r : ℂ) * quadUnit (true, false)) * v).im
      rw [e1, e2, cond1_pos, cond1_neg]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have e1 : (((r : ℂ) * quadUnit (true, true)) * v).re = r * v.re := by
        simp [quadUnit, Complex.mul_re] <;> ring
      have e2 : (((r : ℂ) * quadUnit (true, true)) * v).im = r * v.im := by
        simp [quadUnit, Complex.mul_im] <;> ring
      show cond1 true r (((r : ℂ) * quadUnit (true, true)) * v).re ∧
        cond1 true r (((r : ℂ) * quadUnit (true, true)) * v).im
      rw [e1, e2, cond1_pos, cond1_pos]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **Scaling of the area of a quadrant square cut by a set.** For `r > 0`,
`Leb(Q_q(r) ∩ H) = r² Leb([0,1]² ∩ (r · quadUnit q)⁻¹ H)`. -/
theorem volume_quadSq_inter {r : ℝ} (hr : 0 < r) (q : Quad) (H : Set ℂ) :
    volume (quadSq q r ∩ H) = ENNReal.ofReal (r ^ 2) *
      volume (unitSquare ∩ (fun w => ((r : ℂ) * quadUnit q)⁻¹ * w) '' H) := by
  set c : ℂ := (r : ℂ) * quadUnit q with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (quadUnit_ne_zero q)
  have hset : quadSq q r ∩ H = (fun v => c * v) '' (unitSquare ∩ (fun w => c⁻¹ * w) '' H) := by
    rw [quadSq_eq_image hr q, Set.image_inter (mul_right_injective₀ hc0)]
    congr 1
    rw [Set.image_image]
    simp [mul_inv_cancel_left₀ hc0]
  have hnorm : Complex.normSq c = r ^ 2 := by
    rw [hc, map_mul, normSq_quadUnit, Complex.normSq_ofReal]
    ring
  rw [hset, volume_image_mul_left, hnorm]

end Scaling

/-! ### The time halves of rerooted curves -/

section Reroot

/-- The area of the unit square covered by the time half `b` of `e`, after the linear change of variables `w ↦ c⁻¹ w`. -/
def hitFrac (e : C(ℝ, ℂ)) (b : Bool) (c : ℂ) : ℝ≥0∞ :=
  volume (unitSquare ∩ (fun w => c⁻¹ * w) '' timeHalf e b)

/-- The area of the quadrant square cut by the time half. -/
theorem volume_quadSq_timeHalf {r : ℝ} (hr : 0 < r) (q : Quad) (e : C(ℝ, ℂ)) (b : Bool) :
    volume (quadSq q r ∩ timeHalf e b) = ENNReal.ofReal (r ^ 2) * hitFrac e b ((r : ℂ) * quadUnit q) :=
  volume_quadSq_inter hr q _

/-- The image of an image under multiplications is the image under the product. -/
theorem image_mul_image (a b : ℂ) (T : Set ℂ) :
    (fun w => a * w) '' ((fun w => b * w) '' T) = (fun w => (a * b) * w) '' T := by
  rw [Set.image_image]
  congr 1
  funext w
  show a * (b * w) = a * b * w
  ring

/-- **The time halves of the rerooted curve.** If `e` first visits `0` at time `0`, the time half of
`affineReroot 0 s φ e` is the image of the time half of `e` under `w ↦ (s e^{iφ})⁻¹ w`. -/
theorem timeHalf_affineReroot {e : C(ℝ, ℂ)} (h0 : firstHit e 0 = 0) {s : ℝ} (hs : 0 < s) (φ : ℝ) (b : Bool) :
    timeHalf (affineReroot 0 s φ e) b =
      (fun w => ((s : ℂ) * Complex.exp ((φ : ℝ) * Complex.I))⁻¹ * w) '' timeHalf e b := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hval : ∀ t, (affineReroot 0 s φ e) t =
      ((s : ℂ) * Complex.exp ((φ : ℝ) * Complex.I))⁻¹ * e (s ^ 2 * t) := by
    intro t
    simp [affineReroot, h0]
  cases b
  · ext w
    simp only [timeHalf]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨e (s ^ 2 * t), ⟨s ^ 2 * t, mem_Iic.2 ?_, rfl⟩, (hval t).symm⟩
      nlinarith [mul_nonneg hs2.le (neg_nonneg.2 (mem_Iic.1 ht))]
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u / s ^ 2, mem_Iic.2 ?_, ?_⟩
      · have := div_nonneg (neg_nonneg.2 (mem_Iic.1 hu)) hs2.le
        rw [neg_div] at this
        linarith
      · have h2 : s ^ 2 * (u / s ^ 2) = u := by field_simp
        rw [hval, h2]
  · ext w
    simp only [timeHalf]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e (s ^ 2 * t), ⟨s ^ 2 * t, mem_Ici.2 (mul_nonneg hs2.le (mem_Ici.1 ht)), rfl⟩, (hval t).symm⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u / s ^ 2, mem_Ici.2 (div_nonneg (mem_Ici.1 hu) hs2.le), ?_⟩
      have h2 : s ^ 2 * (u / s ^ 2) = u := by field_simp
      rw [hval, h2]

/-- **The unit-square fraction of a rerooted curve.** If `e` first visits `0` at time `0`, then
`hitFrac (affineReroot 0 s φ e) b c = hitFrac e b (s e^{iφ} c)`. -/
theorem hitFrac_affineReroot {e : C(ℝ, ℂ)} (h0 : firstHit e 0 = 0) {s : ℝ} (hs : 0 < s) (φ : ℝ) (b : Bool)
    (c : ℂ) :
    hitFrac (affineReroot 0 s φ e) b c = hitFrac e b ((s : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) * c) := by
  unfold hitFrac
  rw [timeHalf_affineReroot h0 hs φ b, image_mul_image]
  have : c⁻¹ * ((s : ℂ) * Complex.exp ((φ : ℝ) * Complex.I))⁻¹ =
      ((s : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) * c)⁻¹ := by
    rw [mul_inv, mul_comm]
  rw [this]

/-- **Rotation of a quadrant.** If `e` first visits `0` at time `0`, the area of the quadrant `q` of side `r` cut by a
time half of `e` equals the area of the nonnegative quadrant of side `r` cut by the same time half of the
rotated curve `affineReroot 0 1 (quadAngle q) e`. -/
theorem volume_quadSq_rot {e : C(ℝ, ℂ)} (h0 : firstHit e 0 = 0) (b : Bool) (q : Quad) {r : ℝ} (hr : 0 < r) :
    volume (quadSq q r ∩ timeHalf e b) =
      volume (quadSq (true, true) r ∩ timeHalf (affineReroot 0 1 (quadAngle q) e) b) := by
  have h1 : quadUnit (true, true) = 1 := by simp [quadUnit]
  rw [volume_quadSq_timeHalf hr, volume_quadSq_timeHalf hr, hitFrac_affineReroot h0 one_pos, exp_quadAngle, h1]
  congr 2
  push_cast
  ring

/-- **Dilation by `2`.** If `e` first visits `0` at time `0`, the area of the nonnegative quadrant square of side `r`
cut by a time half of `affineReroot 0 2 0 e` is `r²` times the unit-square fraction `hitFrac e b (2 r)`. -/
theorem volume_quadSq_dil {e : C(ℝ, ℂ)} (h0 : firstHit e 0 = 0) (b : Bool) {r : ℝ} (hr : 0 < r) :
    volume (quadSq (true, true) r ∩ timeHalf (affineReroot 0 2 0 e) b) =
      ENNReal.ofReal (r ^ 2) * hitFrac e b (2 * (r : ℂ)) := by
  have h1 : quadUnit (true, true) = 1 := by simp [quadUnit]
  rw [volume_quadSq_timeHalf hr, hitFrac_affineReroot h0 two_pos, h1]
  congr 2
  simp

end Reroot

/-! ### Measurability -/

section Measurability

/-- The relation `w ∈ timeHalf e b` is measurable on `C(ℝ, ℂ) × ℂ`. -/
theorem measurableSet_mem_timeHalf (b : Bool) :
    MeasurableSet {p : C(ℝ, ℂ) × ℂ | p.2 ∈ timeHalf p.1 b} := by
  have hc : ∀ e : C(ℝ, ℂ), Continuous fun t => e t := fun e => e.continuous
  have hm : ∀ t : ℝ, Measurable fun e : C(ℝ, ℂ) => e t := fun t =>
    (continuous_eval_const t).measurable
  cases b
  · have : {p : C(ℝ, ℂ) × ℂ | p.2 ∈ timeHalf p.1 false} =
        ⋃ N : ℕ, {p : C(ℝ, ℂ) × ℂ | p.2 ∈ (fun t => p.1 t) '' Icc (-(N : ℝ)) 0} := by
      ext p
      simp only [timeHalf, mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨t, ht, ht'⟩
        refine ⟨⌈-t⌉₊, t, ⟨?_, ht⟩, ht'⟩
        have := Nat.le_ceil (-t)
        linarith
      · rintro ⟨N, t, ⟨_, ht⟩, ht'⟩
        exact ⟨t, ht, ht'⟩
    rw [this]
    exact MeasurableSet.iUnion fun N =>
      LatticeProb.measurableSet_mem_image_Icc (L := fun (e : C(ℝ, ℂ)) (t : ℝ) => e t) hc hm
        (by simp : -(N : ℝ) ≤ 0)
  · have : {p : C(ℝ, ℂ) × ℂ | p.2 ∈ timeHalf p.1 true} =
        ⋃ N : ℕ, {p : C(ℝ, ℂ) × ℂ | p.2 ∈ (fun t => p.1 t) '' Icc 0 (N : ℝ)} := by
      ext p
      simp only [timeHalf, mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨t, ht, ht'⟩
        refine ⟨⌈t⌉₊, t, ⟨ht, ?_⟩, ht'⟩
        exact Nat.le_ceil t
      · rintro ⟨N, t, ⟨ht, _⟩, ht'⟩
        exact ⟨t, ht, ht'⟩
    rw [this]
    exact MeasurableSet.iUnion fun N =>
      LatticeProb.measurableSet_mem_image_Icc (L := fun (e : C(ℝ, ℂ)) (t : ℝ) => e t) hc hm
        (by simp : (0 : ℝ) ≤ N)

/-- The area of a measurable set cut by a time half of a curve is a measurable function of the curve and of a
parameter on which the set depends measurably. -/
theorem measurable_volume_inter_timeHalf {Z : Type*} [MeasurableSpace Z] {A : Z → Set ℂ}
    (hA : MeasurableSet {q : (C(ℝ, ℂ) × Z) × ℂ | q.2 ∈ A q.1.2}) (b : Bool) :
    Measurable fun p : C(ℝ, ℂ) × Z => volume (A p.2 ∩ timeHalf p.1 b) := by
  have hT : MeasurableSet {q : (C(ℝ, ℂ) × Z) × ℂ | q.2 ∈ timeHalf q.1.1 b} :=
    (measurableSet_mem_timeHalf b).preimage (measurable_fst.fst.prodMk measurable_snd)
  exact measurable_measure_prodMk_left (ν := (volume : Measure ℂ)) (s := {q : (C(ℝ, ℂ) × Z) × ℂ | q.2 ∈ A q.1.2} ∩
    {q : (C(ℝ, ℂ) × Z) × ℂ | q.2 ∈ timeHalf q.1.1 b}) (hA.inter hT)

/-- The area of a fixed measurable set cut by a time half of a curve is a measurable function of the curve. -/
theorem measurable_volume_inter_timeHalf_const {A : Set ℂ} (hA : MeasurableSet A) (b : Bool) :
    Measurable fun e : C(ℝ, ℂ) => volume (A ∩ timeHalf e b) := by
  have h := measurable_volume_inter_timeHalf (Z := Unit) (A := fun _ => A)
    (hA.preimage measurable_snd) b
  exact h.comp (measurable_id.prodMk measurable_const)

end Measurability

/-! ### The law of the covered fraction -/

section Law

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The curve `ηL` first visits `0` at time `0` almost surely. -/
theorem ae_firstHit_ηL_zero
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0 :=
  MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPositiveRadii D
    (MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)

/-- **Affine invariance in the form of preimages**: for a measurable set `A` of curves,
`P (affineReroot 0 s φ ηL ∈ A) = P (ηL ∈ A)`. -/
theorem measure_preimage_affineReroot
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {s : ℝ} (hs : 0 < s) (φ : ℝ)
    {A : Set C(ℝ, ℂ)} (hA : MeasurableSet A) :
    P ((fun ω => affineReroot 0 s φ (ηL ω)) ⁻¹' A) = P (ηL ⁻¹' A) := by
  have hmap := MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL D 0 hs φ
  have hηL : Measurable ηL := D.measurable_curves.1
  have hm : Measurable fun ω => affineReroot 0 s φ (ηL ω) :=
    (MatedCRTHarmonic.L43O.measurable_affineReroot 0 s φ).comp hηL
  rw [← Measure.map_apply hm hA, hmap, Measure.map_apply hηL hA]

/-- The event that the quadrant `q` of side `r` meets the time half `b` of the curve in positive area. -/
def quadPos (b : Bool) (q : Quad) (r : ℝ) : Set C(ℝ, ℂ) :=
  {e | 0 < volume (quadSq q r ∩ timeHalf e b)}

/-- The event `quadPos b q r` is measurable. -/
theorem measurableSet_quadPos (b : Bool) (q : Quad) (r : ℝ) : MeasurableSet (quadPos b q r) :=
  measurableSet_lt measurable_const (measurable_volume_inter_timeHalf_const (measurableSet_quadSq q r) b)

/-- The event that all the quadrant squares of side `2^{-n}` of the nonnegative quadrant meet the time half in
positive area. -/
def posSet (b : Bool) : Set C(ℝ, ℂ) := ⋂ n : ℕ, quadPos b (true, true) ((1 / 2 : ℝ) ^ n)

/-- The event `posSet b` is measurable. -/
theorem measurableSet_posSet (b : Bool) : MeasurableSet (posSet b) :=
  MeasurableSet.iInter fun n => measurableSet_quadPos b _ _

/-- The four quadrants have the same probability of meeting the time half in positive area. -/
theorem measure_quadPos_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) (q : Quad) {r : ℝ}
    (hr : 0 < r) : P (ηL ⁻¹' quadPos b q r) = P (ηL ⁻¹' quadPos b (true, true) r) := by
  rw [← measure_preimage_affineReroot D one_pos (quadAngle q) (measurableSet_quadPos b (true, true) r)]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_firstHit_ηL_zero D] with ω h0
  show (0 < volume (quadSq q r ∩ timeHalf (ηL ω) b)) ↔
    0 < volume (quadSq (true, true) r ∩ timeHalf (affineReroot 0 1 (quadAngle q) (ηL ω)) b)
  rw [volume_quadSq_rot h0 b q hr]

/-- If a subset of a time half has positive area and lies in the disk of radius `r`, then one of the four quadrant
squares of side `r` meets the time half in positive area. -/
theorem exists_quadPos_of_subset {e : C(ℝ, ℂ)} {b : Bool} {r : ℝ} {T : Set ℂ} (hT0 : volume T ≠ 0)
    (hT : T ⊆ timeHalf e b) (hTr : ∀ w ∈ T, ‖w‖ < r) : ∃ q : Quad, e ∈ quadPos b q r := by
  by_contra hcon
  push_neg at hcon
  have hsub : T ⊆ ⋃ q : Quad, (quadSq q r ∩ timeHalf e b) := fun w hw => by
    obtain ⟨q, hq⟩ := exists_mem_quadSq (r := r) (w := w)
      ((Complex.abs_re_le_norm w).trans (hTr w hw).le) ((Complex.abs_im_le_norm w).trans (hTr w hw).le)
    exact mem_iUnion.2 ⟨q, hq, hT hw⟩
  have hnull : volume (⋃ q : Quad, (quadSq q r ∩ timeHalf e b)) = 0 :=
    measure_iUnion_null fun q => by simpa [quadPos] using hcon q
  exact hT0 (measure_mono_null hsub hnull)

/-- Almost surely, some quadrant square of side `r` meets the time half in positive area. -/
theorem ae_exists_quadPos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ q : Quad, ηL ω ∈ quadPos b q r := by
  filter_upwards [D.spaceFilling] with ω hω
  obtain ⟨-, -, h0, hvol⟩ := hω
  have hopen : IsOpen ((ηL ω) ⁻¹' Metric.ball (0 : ℂ) r) := Metric.isOpen_ball.preimage (ηL ω).continuous
  have hmem : (0 : ℝ) ∈ (ηL ω) ⁻¹' Metric.ball (0 : ℂ) r := by simp [h0, hr]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 hmem
  have ht0 : 0 < ρ / 2 := by positivity
  have hsub : ∀ s : ℝ, |s| ≤ ρ / 2 → ‖ηL ω s‖ < r := by
    intro s hs
    have hs' : s ∈ Metric.ball (0 : ℝ) ρ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      linarith
    simpa using hball hs'
  cases b
  · refine exists_quadPos_of_subset (T := (ηL ω) '' Icc (-(ρ / 2)) 0) ?_ ?_ ?_
    · rw [hvol (-(ρ / 2)) 0 (by linarith)]
      simpa using ht0
    · rintro _ ⟨s, hs, rfl⟩
      show ηL ω s ∈ (ηL ω) '' Iic 0
      exact ⟨s, hs.2, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hsub s (abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  · refine exists_quadPos_of_subset (T := (ηL ω) '' Icc 0 (ρ / 2)) ?_ ?_ ?_
    · rw [hvol 0 (ρ / 2) (by linarith)]
      simpa using ht0
    · rintro _ ⟨s, hs, rfl⟩
      show ηL ω s ∈ (ηL ω) '' Ici 0
      exact ⟨s, hs.1, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hsub s (abs_le.2 ⟨by linarith [hs.1], hs.2⟩)

/-- For every `r > 0`, the nonnegative quadrant of side `r` meets the time half in positive area with probability at
least `1/4`, in the form `1 ≤ 4 · P`. -/
theorem one_le_four_mul_measure
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) {r : ℝ} (hr : 0 < r) :
    1 ≤ 4 * P (ηL ⁻¹' quadPos b (true, true) r) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hcompl : P (⋃ q : Quad, ηL ⁻¹' quadPos b q r)ᶜ = 0 := by
    have h := ae_iff.1 (ae_exists_quadPos D b hr)
    have e : (⋃ q : Quad, ηL ⁻¹' quadPos b q r)ᶜ = {a | ¬∃ q : Quad, ηL a ∈ quadPos b q r} := by
      ext ω
      simp
    rw [e]
    exact h
  have h1 : 1 ≤ P (⋃ q : Quad, ηL ⁻¹' quadPos b q r) := by
    have := measure_union_le (μ := P) (⋃ q : Quad, ηL ⁻¹' quadPos b q r) (⋃ q : Quad, ηL ⁻¹' quadPos b q r)ᶜ
    rw [union_compl_self, hcompl, add_zero, measure_univ] at this
    exact this
  calc (1 : ℝ≥0∞) ≤ P (⋃ q : Quad, ηL ⁻¹' quadPos b q r) := h1
    _ ≤ ∑ q : Quad, P (ηL ⁻¹' quadPos b q r) := measure_iUnion_fintype_le _ _
    _ = ∑ _q : Quad, P (ηL ⁻¹' quadPos b (true, true) r) :=
        Finset.sum_congr rfl fun q _ => measure_quadPos_eq D b q hr
    _ = 4 * P (ηL ⁻¹' quadPos b (true, true) r) := by
        rw [Finset.sum_const, Finset.card_univ, card_quad, nsmul_eq_mul, Nat.cast_ofNat]

/-- The curve belongs to `posSet b` with positive probability. -/
theorem measure_posSet_ne_zero
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) :
    P (ηL ⁻¹' posSet b) ≠ 0 := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hanti : Antitone fun n : ℕ => ηL ⁻¹' quadPos b (true, true) ((1 / 2 : ℝ) ^ n) := by
    intro n m hnm ω hω
    have hle : ((1 / 2 : ℝ) ^ m) ≤ (1 / 2) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
    have hω' : 0 < volume (quadSq (true, true) ((1 / 2 : ℝ) ^ m) ∩ timeHalf (ηL ω) b) := hω
    exact lt_of_lt_of_le hω' (measure_mono (inter_subset_inter_left _ (quadSq_mono _ hle)))
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hηL (measurableSet_quadPos b (true, true) ((1 / 2 : ℝ) ^ n))).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hlim4 := ENNReal.Tendsto.const_mul hlim (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
  have hge : 1 ≤ 4 * P (⋂ n : ℕ, ηL ⁻¹' quadPos b (true, true) ((1 / 2 : ℝ) ^ n)) :=
    ge_of_tendsto' hlim4 fun n => one_le_four_mul_measure D b (by positivity)
  have hset : ηL ⁻¹' posSet b = ⋂ n : ℕ, ηL ⁻¹' quadPos b (true, true) ((1 / 2 : ℝ) ^ n) := by
    ext ω
    simp [posSet]
  rw [hset]
  intro h0
  rw [h0] at hge
  simp at hge

/-- **Positivity of the covered fraction of the quadrant squares.** Almost surely, every quadrant square of side `2^{-n}`
of the nonnegative quadrant meets each time half of `ηL` in positive area (the quadrant argument, closed by the
zero-one law for the dilation by `2`). -/
theorem ae_mem_posSet
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) (b : Bool) :
    ∀ᵐ ω ∂P, ηL ω ∈ posSet b := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  classical
  set g : C(ℝ, ℂ) → ℝ := (posSet b).indicator fun _ => (1 : ℝ) with hg
  have hgm : Measurable g := measurable_const.indicator (measurableSet_posSet b)
  have hinv : ∀ᵐ ω ∂P, g (affineReroot 0 2 0 (ηL ω)) = g (ηL ω) := by
    filter_upwards [ae_firstHit_ηL_zero D] with ω h0
    have h1 : quadUnit (true, true) = 1 := by simp [quadUnit]
    have hpos : ∀ r : ℝ, 0 < r →
        (0 < volume (quadSq (true, true) r ∩ timeHalf (affineReroot 0 2 0 (ηL ω)) b) ↔
          0 < volume (quadSq (true, true) (2 * r) ∩ timeHalf (ηL ω) b)) := by
      intro r hr
      have h2r : 0 < 2 * r := by positivity
      have hc : ((2 * r : ℝ) : ℂ) * quadUnit (true, true) = 2 * (r : ℂ) := by
        rw [h1]
        push_cast
        ring
      rw [volume_quadSq_dil h0 b hr, volume_quadSq_timeHalf h2r, hc, ENNReal.mul_pos_iff, ENNReal.mul_pos_iff]
      simp only [ENNReal.ofReal_pos]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨by positivity, h⟩
      · rintro ⟨-, h⟩
        exact ⟨by positivity, h⟩
    have e2 : ∀ n : ℕ, 2 * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n := fun n => by
      rw [pow_succ]
      ring
    have key : affineReroot 0 2 0 (ηL ω) ∈ posSet b ↔ ηL ω ∈ posSet b := by
      simp only [posSet, mem_iInter, quadPos, mem_setOf_eq]
      constructor
      · intro h n
        have := (hpos ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)).1 (h (n + 1))
        rwa [e2 n] at this
      · intro h n
        refine (hpos _ (by positivity)).2 ?_
        cases n with
        | zero =>
            have h1' : quadSq (true, true) ((1 / 2 : ℝ) ^ 0) ⊆ quadSq (true, true) (2 * (1 / 2 : ℝ) ^ 0) :=
              quadSq_mono _ (by norm_num)
            exact lt_of_lt_of_le (h 0) (measure_mono (inter_subset_inter_left _ h1'))
        | succ n =>
            rw [e2 n]
            exact h n
    show (posSet b).indicator (fun _ => (1 : ℝ)) (affineReroot 0 2 0 (ηL ω)) =
      (posSet b).indicator (fun _ => (1 : ℝ)) (ηL ω)
    by_cases hmem : ηL ω ∈ posSet b
    · rw [indicator_of_mem hmem, indicator_of_mem (key.2 hmem)]
    · rw [indicator_of_notMem hmem, indicator_of_notMem fun h => hmem (key.1 h)]
  obtain ⟨c, hc⟩ :=
    ae_eq_const_of_affineReroot_two_invariant D hγ (igFieldDilationMixing γ hγ) hgm hinv
  by_cases hc0 : c = 0
  · exfalso
    apply measure_posSet_ne_zero D b
    have hnot : ∀ᵐ ω ∂P, ηL ω ∉ posSet b := by
      filter_upwards [hc] with ω hω hmem
      rw [hc0] at hω
      simp [hg, hmem] at hω
    have h := ae_iff.1 hnot
    have e : ηL ⁻¹' posSet b = {ω | ¬ηL ω ∉ posSet b} := by
      ext ω
      simp
    rw [e]
    exact h
  · filter_upwards [hc] with ω hω
    by_contra hmem
    apply hc0
    rw [← hω]
    simp [hg, hmem]

/-- Almost surely the covered area of the unit square by each time half of `ηL` is positive. -/
theorem ae_pos_unitSquare
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) (b : Bool) :
    ∀ᵐ ω ∂P, 0 < volume (unitSquare ∩ timeHalf (ηL ω) b) := by
  filter_upwards [ae_mem_posSet D hγ b] with ω hω
  simp only [posSet, mem_iInter] at hω
  simpa [quadPos, quadSq_true_one] using hω 0

/-- **The law of the covered fraction of a quadrant square does not depend on its side or its quadrant**: for every
`ℓ > 0` and `δ ≥ 0`, the probability that the quadrant square of side `ℓ / 2` in the quadrant `q` is covered by the time
half `b` of `ηL` in area less than `δ ℓ²` equals the probability that the unit square is covered in area less
than `4 δ`. -/
theorem measure_quadSq_lt
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) (q : Quad) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {δ : ℝ} (hδ : 0 ≤ δ) :
    P {ω | volume (quadSq q (ℓ / 2) ∩ timeHalf (ηL ω) b) <
        ENNReal.ofReal δ * (ENNReal.ofReal ℓ * ENNReal.ofReal ℓ)} =
      P {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < ENNReal.ofReal (4 * δ)} := by
  have hr : 0 < ℓ / 2 := by positivity
  have hthr : ENNReal.ofReal δ * (ENNReal.ofReal ℓ * ENNReal.ofReal ℓ) =
      ENNReal.ofReal ((ℓ / 2) ^ 2) * ENNReal.ofReal (4 * δ) := by
    rw [← ENNReal.ofReal_mul hℓ.le, ← ENNReal.ofReal_mul hδ,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (ℓ / 2) ^ 2)]
    congr 1
    ring
  have hne0 : ENNReal.ofReal ((ℓ / 2) ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hnet : ENNReal.ofReal ((ℓ / 2) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  set A : Set C(ℝ, ℂ) := {e | volume (unitSquare ∩ timeHalf e b) < ENNReal.ofReal (4 * δ)} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt (measurable_volume_inter_timeHalf_const measurableSet_unitSquare b) measurable_const
  have hstep : ∀ ω, firstHit (ηL ω) 0 = 0 →
      (volume (quadSq q (ℓ / 2) ∩ timeHalf (ηL ω) b) <
        ENNReal.ofReal δ * (ENNReal.ofReal ℓ * ENNReal.ofReal ℓ)) ↔
      affineReroot 0 (ℓ / 2) (quadAngle q) (ηL ω) ∈ A := by
    intro ω h0
    have key : hitFrac (ηL ω) b (((ℓ / 2 : ℝ) : ℂ) * quadUnit q) =
        volume (unitSquare ∩ timeHalf (affineReroot 0 (ℓ / 2) (quadAngle q) (ηL ω)) b) := by
      have := hitFrac_affineReroot h0 hr (quadAngle q) b 1
      rw [exp_quadAngle, mul_one] at this
      rw [← this]
      simp [hitFrac]
    rw [volume_quadSq_timeHalf hr, hthr, ENNReal.mul_lt_mul_iff_right hne0 hnet, key]
    exact Iff.rfl
  rw [← measure_preimage_affineReroot D hr (quadAngle q) hAm]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_firstHit_ηL_zero D] with ω h0
  exact hstep ω h0

/-- **Small covered fractions of the unit square have small probability.** For each time half, the probability that
the unit square is covered in area less than `η` is at most any given `ε > 0` for some `η > 0`. -/
theorem exists_measure_unitSquare_lt_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) (b : Bool)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ P {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < ENNReal.ofReal η} ≤ ε := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hsm : ∀ n : ℕ, NullMeasurableSet {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < (n : ℝ≥0∞)⁻¹} P :=
    fun n =>
    (measurableSet_lt ((measurable_volume_inter_timeHalf_const measurableSet_unitSquare b).comp hηL)
      measurable_const).nullMeasurableSet
  have hanti : Antitone fun n : ℕ => {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < (n : ℝ≥0∞)⁻¹} := by
    intro n m hnm ω hω
    exact lt_of_lt_of_le hω (ENNReal.inv_le_inv.2 (by exact_mod_cast hnm))
  have hlim := tendsto_measure_iInter_atTop (μ := P) hsm hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n : ℕ, {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < (n : ℝ≥0∞)⁻¹}) = 0 := by
    have hae := ae_pos_unitSquare D hγ b
    rw [← nonpos_iff_eq_zero]
    refine (measure_mono (t := {ω | ¬ 0 < volume (unitSquare ∩ timeHalf (ηL ω) b)}) ?_).trans
      (le_of_eq (ae_iff.1 hae))
    intro ω hω
    simp only [mem_iInter, mem_setOf_eq] at hω
    simp only [mem_setOf_eq, not_lt, nonpos_iff_eq_zero]
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
    exact absurd (hω n) (not_lt.2 hn.le)
  rw [hnull] at hlim
  have hev := (tendsto_order.1 hlim).2 ε hε
  obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨((n : ℝ))⁻¹, by positivity, ?_⟩
  have : ENNReal.ofReal ((n : ℝ))⁻¹ = (n : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
  rw [this]
  exact hn.le

end Law

/-! ### The root squares -/

section Root

/-- The pairs of an area measure and a dyadic grid. -/
abbrev RootData : Type := Measure ℂ × ZeroConeRoot.DyCoord

/-- The first coordinate of the lower left corner of the root square. -/
def rootCorner₁ (z : RootData) (m : ℝ≥0∞) : ℝ :=
  gridFloor z.2.1 z.2.2.1 (ZeroConeRoot.rootGen z.1 z.2 m) 0

/-- The second coordinate of the lower left corner of the root square. -/
def rootCorner₂ (z : RootData) (m : ℝ≥0∞) : ℝ :=
  gridFloor z.2.1 z.2.2.2 (ZeroConeRoot.rootGen z.1 z.2 m) 0

/-- The side of the root square. -/
def rootSide (z : RootData) (m : ℝ≥0∞) : ℝ :=
  (2 : ℝ) ^ (z.2.1 + ((ZeroConeRoot.rootGen z.1 z.2 m : ℤ) : ℝ))

/-- The root square is the closed square with lower left corner `(rootCorner₁, rootCorner₂)` and side `rootSide`. -/
theorem rootSquare_eq (z : RootData) (m : ℝ≥0∞) :
    squareAt z.2.1 z.2.2.1 z.2.2.2 (ZeroConeRoot.rootGen z.1 z.2 m) 0 =
      cornerSquare (rootCorner₁ z m) (rootCorner₂ z m) (rootSide z m) := rfl

/-- The side of the root square is positive. -/
theorem rootSide_pos (z : RootData) (m : ℝ≥0∞) : 0 < rootSide z m :=
  Real.rpow_pos_of_pos two_pos _

/-- The root square contains the origin. -/
theorem rootCorner_spec (z : RootData) (m : ℝ≥0∞) :
    rootCorner₁ z m ≤ 0 ∧ 0 ≤ rootCorner₁ z m + rootSide z m ∧
      rootCorner₂ z m ≤ 0 ∧ 0 ≤ rootCorner₂ z m + rootSide z m := by
  have h := mem_squareAt (s := z.2.1) (o₁ := z.2.2.1) (o₂ := z.2.2.2) (ZeroConeRoot.rootGen z.1 z.2 m) 0
  rw [rootSquare_eq, mem_cornerSquare] at h
  simpa using h

/-- The first corner coordinate of the root square is measurable in the area measure and the grid. -/
theorem measurable_rootCorner₁ (m : ℝ≥0∞) : Measurable fun z : RootData => rootCorner₁ z m := by
  have hF : Measurable fun p : ℤ × ZeroConeRoot.DyCoord => gridFloor p.2.1 p.2.2.1 p.1 0 :=
    measurable_from_prod_countable_right fun j =>
      LatticeProb.CellConfigCappedSquare.measurable_gridFloor j (s := fun y : ZeroConeRoot.DyCoord => y.1)
        (o := fun y => y.2.1) (x := fun _ => 0) measurable_fst (measurable_fst.comp measurable_snd)
        measurable_const
  exact hF.comp ((ZeroConeRoot.measurable_rootGen m).prodMk measurable_snd)

/-- The second corner coordinate of the root square is measurable in the area measure and the grid. -/
theorem measurable_rootCorner₂ (m : ℝ≥0∞) : Measurable fun z : RootData => rootCorner₂ z m := by
  have hF : Measurable fun p : ℤ × ZeroConeRoot.DyCoord => gridFloor p.2.1 p.2.2.2 p.1 0 :=
    measurable_from_prod_countable_right fun j =>
      LatticeProb.CellConfigCappedSquare.measurable_gridFloor j (s := fun y : ZeroConeRoot.DyCoord => y.1)
        (o := fun y => y.2.2) (x := fun _ => 0) measurable_fst (measurable_snd.comp measurable_snd)
        measurable_const
  exact hF.comp ((ZeroConeRoot.measurable_rootGen m).prodMk measurable_snd)

/-- The side of the root square is measurable in the area measure and the grid. -/
theorem measurable_rootSide (m : ℝ≥0∞) : Measurable fun z : RootData => rootSide z m := by
  have hj : Measurable fun z : RootData => ((ZeroConeRoot.rootGen z.1 z.2 m : ℤ) : ℝ) :=
    (measurable_of_countable (Int.cast : ℤ → ℝ)).comp (ZeroConeRoot.measurable_rootGen m)
  exact measurable_const.pow ((measurable_fst.comp measurable_snd).add hj)

end Root

/-! ### The bound for the root squares -/

section Assembly

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The pairs `(curve, root data)` for which the quadrant `q` of side `rootSide / 2` fits in the root square and the time
half `b` of the curve covers it in area less than `δ` times the area of the root square. -/
def badSet (b : Bool) (δ : ℝ) (m : ℝ≥0∞) (q : Quad) : Set (C(ℝ, ℂ) × RootData) :=
  {p | quadFit q (rootCorner₁ p.2 m) (rootCorner₂ p.2 m) (rootSide p.2 m) ∧
    volume (quadSq q (rootSide p.2 m / 2) ∩ timeHalf p.1 b) <
      ENNReal.ofReal δ * (ENNReal.ofReal (rootSide p.2 m) * ENNReal.ofReal (rootSide p.2 m))}

/-- Membership in `badSet`, unfolded. -/
theorem mem_badSet {b : Bool} {δ : ℝ} {m : ℝ≥0∞} {q : Quad} {p : C(ℝ, ℂ) × RootData} :
    p ∈ badSet b δ m q ↔ quadFit q (rootCorner₁ p.2 m) (rootCorner₂ p.2 m) (rootSide p.2 m) ∧
      volume (quadSq q (rootSide p.2 m / 2) ∩ timeHalf p.1 b) <
        ENNReal.ofReal δ * (ENNReal.ofReal (rootSide p.2 m) * ENNReal.ofReal (rootSide p.2 m)) :=
  Iff.rfl

/-- The set `badSet b δ m q` is measurable. -/
theorem measurableSet_badSet (b : Bool) (δ : ℝ) (m : ℝ≥0∞) (q : Quad) : MeasurableSet (badSet b δ m q) := by
  have h1 : Measurable fun p : C(ℝ, ℂ) × RootData => rootCorner₁ p.2 m :=
    (measurable_rootCorner₁ m).comp measurable_snd
  have h2 : Measurable fun p : C(ℝ, ℂ) × RootData => rootCorner₂ p.2 m :=
    (measurable_rootCorner₂ m).comp measurable_snd
  have h3 : Measurable fun p : C(ℝ, ℂ) × RootData => rootSide p.2 m :=
    (measurable_rootSide m).comp measurable_snd
  have hfit := measurableSet_quadFit h1 h2 h3 q
  have hr : Measurable fun t : (C(ℝ, ℂ) × RootData) × ℂ => rootSide t.1.2 m / 2 :=
    ((measurable_rootSide m).comp (measurable_snd.comp measurable_fst)).div_const 2
  have hA : MeasurableSet {t : (C(ℝ, ℂ) × RootData) × ℂ | t.2 ∈ quadSq q (rootSide t.1.2 m / 2)} :=
    (measurableSet_cond1 hr (Complex.measurable_re.comp measurable_snd) q.1).inter
      (measurableSet_cond1 hr (Complex.measurable_im.comp measurable_snd) q.2)
  have hV := measurable_volume_inter_timeHalf (Z := RootData) (A := fun z => quadSq q (rootSide z m / 2)) hA b
  have hthr : Measurable fun p : C(ℝ, ℂ) × RootData =>
      ENNReal.ofReal δ * (ENNReal.ofReal (rootSide p.2 m) * ENNReal.ofReal (rootSide p.2 m)) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp h3).mul (ENNReal.measurable_ofReal.comp h3))
  exact hfit.inter (measurableSet_lt hV hthr)

/-- **The bad set has small mass for every law of the root data**: under the product of the law of `ηL` and any
probability measure on the root data, the mass of `badSet b δ m q` is at most the probability that the unit square
is covered in area less than `4 δ`. -/
theorem prod_badSet_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (b : Bool) (q : Quad) (m : ℝ≥0∞)
    {δ : ℝ} (hδ : 0 ≤ δ) (ν : Measure RootData) [IsProbabilityMeasure ν] :
    ((P.map ηL).prod ν) (badSet b δ m q) ≤
      P {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < ENNReal.ofReal (4 * δ)} := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  haveI : IsProbabilityMeasure (P.map ηL) := Measure.isProbabilityMeasure_map hηL.aemeasurable
  rw [Measure.prod_apply_symm (measurableSet_badSet b δ m q)]
  calc ∫⁻ z, (P.map ηL) ((fun e => (e, z)) ⁻¹' badSet b δ m q) ∂ν
      ≤ ∫⁻ _z, P {ω | volume (unitSquare ∩ timeHalf (ηL ω) b) < ENNReal.ofReal (4 * δ)} ∂ν := by
        refine lintegral_mono fun z => ?_
        have hsec : MeasurableSet ((fun e : C(ℝ, ℂ) => (e, z)) ⁻¹' badSet b δ m q) :=
          (measurableSet_badSet b δ m q).preimage (measurable_id.prodMk measurable_const)
        rw [Measure.map_apply hηL hsec, ← measure_quadSq_lt D b q (rootSide_pos z m) hδ]
        refine measure_mono fun ω hω => ?_
        have hω' : (ηL ω, z) ∈ badSet b δ m q := hω
        exact (mem_badSet.1 hω').2
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The set of grid and sample pairs for which the time half `b` of `ηL` covers the root square of mass at most `m`
of the area measure `μ ω` in area less than `δ` times the area of the root square. -/
def rootFracSet (ηL : Ω → C(ℝ, ℂ)) (b : Bool) (δ : ℝ) (m : ℝ≥0∞) (μ : Ω → Measure ℂ) :
    Set (Ω × ZeroConeRoot.DyCoord) :=
  {x | volume (squareAt x.2.1 x.2.2.1 x.2.2.2 (ZeroConeRoot.rootGen (μ x.1) x.2 m) 0 ∩ timeHalf (ηL x.1) b) <
    ENNReal.ofReal δ * volume (squareAt x.2.1 x.2.2.1 x.2.2.2 (ZeroConeRoot.rootGen (μ x.1) x.2 m) 0)}

/-- **The covered fraction of the root squares** (the quadrant argument). For every mating-of-trees coupling with
`γ ∈ (0, 2)`, each time half `b` of `ηL` and each `ε > 0` there is `δ > 0` such that, for all masses `m ∈ (0, ∞)`,
the probability, under the sample and the independent uniform dyadic grid `y`, that the time half covers the root square
`S_m` in area less than `δ` times the area of `S_m` is at most `ε`. -/
theorem exists_measure_areaFraction_lt_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ b : Bool, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ⊤ →
      (P.prod ZeroConeRoot.uniformDyadicLaw)
        {x | volume (squareAt x.2.1 x.2.2.1 x.2.2.2
              (ZeroConeRoot.rootGen (zeroConeArea γ X₀ B₀ B₀' x.1) x.2 m) 0 ∩ timeHalf (ηL x.1) b) <
            ENNReal.ofReal δ * volume (squareAt x.2.1 x.2.2.1 x.2.2.2
              (ZeroConeRoot.rootGen (zeroConeArea γ X₀ B₀ B₀' x.1) x.2 m) 0)} ≤ ENNReal.ofReal ε := by
  intro b ε hε
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal ε / 4 :=
    ENNReal.div_pos (ENNReal.ofReal_pos.2 hε).ne' (by norm_num)
  obtain ⟨η₁, hη₁, hη₁le⟩ := exists_measure_unitSquare_lt_le D hγ b hε4
  refine ⟨η₁ / 4, by positivity, fun m _ _ => ?_⟩
  -- a measurable version of the area measure, independent of the curve
  obtain ⟨H, hHm, hHind, hHeq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hμ'm : Measurable fun ω => ZeroConeRoot.fieldArea γ (H ω) :=
    (ZeroConeRoot.measurable_fieldArea γ).comp hHm
  have hind : IndepFun ηL (fun ω => ZeroConeRoot.fieldArea γ (H ω)) P :=
    hHind.symm.comp measurable_id (ZeroConeRoot.measurable_fieldArea γ)
  haveI : IsProbabilityMeasure (P.map fun ω => ZeroConeRoot.fieldArea γ (H ω)) :=
    Measure.isProbabilityMeasure_map hμ'm.aemeasurable
  -- replace the area measure by its measurable version
  have hae : ∀ᵐ x ∂(P.prod ZeroConeRoot.uniformDyadicLaw),
      zeroConeArea γ X₀ B₀ B₀' x.1 = ZeroConeRoot.fieldArea γ (H x.1) :=
    ZeroConeRoot.ae_prod_fst_of_ae (p := fun ω => zeroConeArea γ X₀ B₀ B₀' ω = ZeroConeRoot.fieldArea γ (H ω))
      (hHeq.mono fun ω hω => by
        show ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) = ZeroConeRoot.fieldArea γ (H ω)
        rw [hω])
  change (P.prod ZeroConeRoot.uniformDyadicLaw)
    (rootFracSet ηL b (η₁ / 4) m (zeroConeArea γ X₀ B₀ B₀')) ≤ ENNReal.ofReal ε
  have hTT' : (P.prod ZeroConeRoot.uniformDyadicLaw)
      (rootFracSet ηL b (η₁ / 4) m (zeroConeArea γ X₀ B₀ B₀')) =
      (P.prod ZeroConeRoot.uniformDyadicLaw)
        (rootFracSet ηL b (η₁ / 4) m fun ω => ZeroConeRoot.fieldArea γ (H ω)) := by
    refine measure_congr (eventuallyEqSet_iff.2 (hae.mono fun x hx => ?_))
    simp only [rootFracSet, mem_setOf_eq, hx]
  rw [hTT']
  -- the joint law of the curve and the root data is a product
  have hFm : Measurable fun x : Ω × ZeroConeRoot.DyCoord =>
      ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData) :=
    (hηL.comp measurable_fst).prodMk ((hμ'm.comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable fun ω => (ηL ω, ZeroConeRoot.fieldArea γ (H ω)) := hηL.prodMk hμ'm
  have hjoint : (P.prod ZeroConeRoot.uniformDyadicLaw).map
      (fun x : Ω × ZeroConeRoot.DyCoord =>
        ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData)) =
      (P.map ηL).prod ((P.map fun ω => ZeroConeRoot.fieldArea γ (H ω)).prod ZeroConeRoot.uniformDyadicLaw) := by
    have h1 : (fun x : Ω × ZeroConeRoot.DyCoord =>
        ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData)) =
        MeasurableEquiv.prodAssoc ∘ Prod.map (fun ω => (ηL ω, ZeroConeRoot.fieldArea γ (H ω)))
          (id : ZeroConeRoot.DyCoord → ZeroConeRoot.DyCoord) := rfl
    rw [h1, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable (hpair.prodMap measurable_id),
      ← Measure.map_prod_map P ZeroConeRoot.uniformDyadicLaw hpair measurable_id, Measure.map_id,
      (indepFun_iff_map_prod_eq_prod_map_map hηL.aemeasurable hμ'm.aemeasurable).1 hind,
      Measure.prodAssoc_prod]
  -- containment in the union of the four bad sets
  have hsub : rootFracSet ηL b (η₁ / 4) m (fun ω => ZeroConeRoot.fieldArea γ (H ω)) ⊆
      ⋃ q : Quad, (fun x : Ω × ZeroConeRoot.DyCoord =>
        ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData)) ⁻¹' badSet b (η₁ / 4) m q := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := rootCorner_spec (ZeroConeRoot.fieldArea γ (H x.1), x.2) m
    obtain ⟨q, hq⟩ := exists_quadFit h1 h2 h3 h4
    refine mem_iUnion.2 ⟨q, mem_preimage.2 (mem_badSet.2 ⟨hq, ?_⟩)⟩
    have hx' : volume (squareAt (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.1 (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.2.1
        (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.2.2
        (ZeroConeRoot.rootGen (ZeroConeRoot.fieldArea γ (H x.1), x.2).1 (ZeroConeRoot.fieldArea γ (H x.1), x.2).2 m) 0 ∩
        timeHalf (ηL x.1) b) <
        ENNReal.ofReal (η₁ / 4) * volume (squareAt (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.1
          (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.2.1 (ZeroConeRoot.fieldArea γ (H x.1), x.2).2.2.2
          (ZeroConeRoot.rootGen (ZeroConeRoot.fieldArea γ (H x.1), x.2).1
            (ZeroConeRoot.fieldArea γ (H x.1), x.2).2 m) 0) := hx
    rw [rootSquare_eq (ZeroConeRoot.fieldArea γ (H x.1), x.2) m] at hx'
    refine lt_of_le_of_lt (measure_mono (inter_subset_inter_left _ (quadSq_subset_cornerSquare hq))) ?_
    rw [volume_cornerSquare] at hx'
    exact hx'
  have h4 : (4 : ℝ≥0∞) * (ENNReal.ofReal ε / 4) = ENNReal.ofReal ε := by
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  calc (P.prod ZeroConeRoot.uniformDyadicLaw) (rootFracSet ηL b (η₁ / 4) m fun ω => ZeroConeRoot.fieldArea γ (H ω))
      ≤ (P.prod ZeroConeRoot.uniformDyadicLaw)
        (⋃ q : Quad, (fun x : Ω × ZeroConeRoot.DyCoord =>
          ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData)) ⁻¹' badSet b (η₁ / 4) m q) :=
        measure_mono hsub
    _ ≤ ∑ q : Quad, (P.prod ZeroConeRoot.uniformDyadicLaw)
        ((fun x : Ω × ZeroConeRoot.DyCoord =>
          ((ηL x.1, (ZeroConeRoot.fieldArea γ (H x.1), x.2)) : C(ℝ, ℂ) × RootData)) ⁻¹' badSet b (η₁ / 4) m q) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : Quad, ENNReal.ofReal ε / 4 := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [← Measure.map_apply hFm (measurableSet_badSet b (η₁ / 4) m q), hjoint]
        refine (prod_badSet_le D b q m (by positivity) _).trans ?_
        have h44 : 4 * (η₁ / 4) = η₁ := by ring
        rw [h44]
        exact hη₁le
    _ = ENNReal.ofReal ε := by
        rw [Finset.sum_const, Finset.card_univ, card_quad, nsmul_eq_mul, Nat.cast_ofNat]
        exact h4

end Assembly

end MatedCRT.ZeroConePolygonal
