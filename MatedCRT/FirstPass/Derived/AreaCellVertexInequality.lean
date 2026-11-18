import MatedCRT.FirstPass.Derived.AreaCellVertexMembership
import MatedCRT.FirstPass.Derived.AreaCellMeshEventually
import MatedCRT.FirstPass.Derived.StopAtExitStartTransfer

/-!
# From a uniform comparison at the cells of a finite network to the walk inequality at every vertex

Let `R n` be a finite set of area cells, closed under the conductances of the cells whose
representative lies in `ball 0 R`, and let `q n v` be points of the cells `v ∈ R n`. If, for all large
`n`, the stopped embedded walk started at the cell `v` is within Lévy-Prokhorov distance `κ / 3` of
the Brownian curve law stopped at its exit time from `ball 0 R` and started at `q n v ∈ U`, then for all
large `n` the all-set walk inequality holds at every vertex `x` with embedded vertex in `closedBall 0 ρ`
(`ρ < R`): the cell of `x` lies in `R n`, its point `q n` is within a small constant of the embedded vertex,
and the start-point shift applies.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace MatedCRT.AreaCellVertexInequality

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.StopAtExitCurveClass
  MatedCRT.StopAtExitLevyProkhorov

/-- **Uniform walk inequality at all vertices from a comparison at the cells of finite sets.**
For an area parametrized proper curve, mesh parameters `ε n → 0`, multiplicities with `m k (k+1) ≠ 0`,
finite cell sets `R n` closed under conductance away from `ball 0 R`, and points `q n v` in the cells
`v ∈ R n`: if eventually, at every cell `v ∈ R n` with `q n v ∈ U`, the stopped embedded walk is within
Lévy-Prokhorov distance `< κ / 3` of the stopped Brownian law started at `q n v`, then eventually, at every
vertex `x` with `vertexPoint (ε n) η x ∈ closedBall 0 ρ`, the stopped walk started at `x` satisfies the
all-set inequality against planar Brownian motion started at the embedded vertex. -/
theorem eventually_forall_vertex_walk_allSet_le {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (mm : ℕ → ℤ → ℤ → ℕ) (hsucc : ∀ n k, mm n k (k + 1) ≠ 0)
    {ρ R : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    {α m₀ : ℝ≥0} (hα : α = 1) (hm₀ : 0 < m₀) (hm₁ : m₀ = 1)
    (hfin : ∀ n x, ∀ᵐ ξ ∂(srwLaw (mm n) x),
      pathExitTime (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ≠ ⊤)
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (Rs : ∀ n, Set (areaCellConfig h (hε n) (mm n)).cells)
    (hclose : ∀ n (v : (areaCellConfig h (hε n) (mm n)).cells),
      areaCellRepresentative h (hε n) (mm n) v ∈ ball (0 : ReflectedGMS.Plane) R →
        ∀ w, w ∉ Rs n → (areaCellConfig h (hε n) (mm n)).c v w = 0)
    (q : ∀ n, Rs n → ReflectedGMS.Plane)
    (hq : ∀ n (v : Rs n), q n v ∈ ((v.1.1 : Cell) : Set ReflectedGMS.Plane))
    (hLP : ∀ᶠ n in atTop, ∀ v : Rs n, q n v ∈ U →
      levyProkhorovEDist
        ((srwLaw (mm n) ((euclideanCellEquiv h (hε n)).symm v.1)).map
          (fun w : ℕ → ℤ => isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint (ε n) η) hm₀.le w))
              (pathExitTime (ball (0 : ℂ) R)
                ⇑((α : ℝ) • interpPathCM (vertexPoint (ε n) η) hm₀.le w)).toNNReal)))
        (BouRabeeGwynne.stoppedBrownianLaw U (q n v) μB) < ENNReal.ofReal (κ / 3)) :
    ∀ᶠ n in atTop, ∀ x : ℤ, vertexPoint (ε n) η x ∈ closedBall (0 : ℂ) ρ →
      ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (mm n) x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ∈ A} ≤
        planarBrownianMotion (vertexPoint (ε n) η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ := by
  obtain ⟨s, hs, key⟩ := StopAtExitStartTransfer.exists_forall_walk_allSet_le hρR hκ
  set d : ℝ := min (s / 2) ((R - ρ) / 2) with hd
  have hdpos : 0 < d := lt_min (by linarith) (by linarith)
  have hds : d < s := by have := min_le_left (s / 2) ((R - ρ) / 2); linarith
  have hdR : ρ + d < R := by have := min_le_right (s / 2) ((R - ρ) / 2); linarith
  have hbd : Bornology.IsBounded (ball (0 : ReflectedGMS.Plane) R) := Metric.isBounded_ball
  filter_upwards [eventually_areaCellConfig_diam_le_of_meeting h hp hε hε0 mm hbd hdpos, hLP]
    with n hmesh hLPn
  intro x hx A
  have hvx : Complex.orthonormalBasisOneI.repr (vertexPoint (ε n) η x) ∈ ball (0 : ReflectedGMS.Plane) R := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
    have := mem_closedBall_zero_iff.1 hx
    linarith
  have hKx : ((euclideanCellEquiv h (hε n) x : (areaCellConfig h (hε n) (mm n)).cells).1 :
      Set ReflectedGMS.Plane) ∩ ball (0 : ReflectedGMS.Plane) R |>.Nonempty := by
    refine ⟨Complex.orthonormalBasisOneI.repr (vertexPoint (ε n) η x), ?_, hvx⟩
    have := areaCellRepresentative_mem h (hε n) (mm n) (euclideanCellEquiv h (hε n) x)
    rwa [areaCellRepresentative_equiv] at this
  have hdiam := hmesh _ hKx
  rw [euclideanCellEquiv_diam h (hε n) (mm n) x] at hdiam
  have hpred := AreaCellVertexMembership.dist_vertexPoint_pred_le (hε n).le h.1 x hdiam
  have hxR : (euclideanCellEquiv h (hε n) x : (areaCellConfig h (hε n) (mm n)).cells) ∈ Rs n := by
    refine AreaCellVertexMembership.euclideanCellEquiv_mem_of_pred h (hε n) (mm n) (hsucc n) (Rs n)
      (fun v => areaCellRepresentative h (hε n) (mm n) v ∈ ball (0 : ReflectedGMS.Plane) R)
      (hclose n) x ?_
    show areaCellRepresentative h (hε n) (mm n) (euclideanCellEquiv h (hε n) (x - 1)) ∈ _
    rw [areaCellRepresentative_equiv, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
    have h1 := mem_closedBall_zero_iff.1 hx
    have h2 : ‖vertexPoint (ε n) η (x - 1)‖ ≤ ‖vertexPoint (ε n) η x‖ + d := by
      have := norm_le_norm_add_norm_sub' (vertexPoint (ε n) η (x - 1)) (vertexPoint (ε n) η x)
      rw [← dist_eq_norm] at this
      linarith
    linarith
  set v : Rs n := ⟨_, hxR⟩ with hv
  have hqd : dist (q n v) (Complex.orthonormalBasisOneI.repr (vertexPoint (ε n) η x)) ≤ d :=
    AreaCellVertexMembership.dist_le_vertexPoint_of_mem_cell h (hε n) (mm n) x hdiam (hq n v)
  have h2 : dist (Complex.orthonormalBasisOneI.repr.symm (q n v)) (vertexPoint (ε n) η x) ≤ d := by
    have := Complex.orthonormalBasisOneI.repr.symm.dist_map (q n v)
      (Complex.orthonormalBasisOneI.repr (vertexPoint (ε n) η x))
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    rw [this]
    exact hqd
  have hqU : q n v ∈ U := by
    rw [hU, mem_preimage, mem_ball_zero_iff]
    have h1 := mem_closedBall_zero_iff.1 hx
    have := norm_le_norm_add_norm_sub' (Complex.orthonormalBasisOneI.repr.symm (q n v))
      (vertexPoint (ε n) η x)
    rw [← dist_eq_norm] at this
    linarith
  have hLPv := hLPn v hqU
  have hsymm : (euclideanCellEquiv h (hε n)).symm v.1 = x := Equiv.symm_apply_apply _ _
  rw [hsymm] at hLPv
  refine key (α := α) (m₀ := m₀) hα hm₀ hm₁ (ε n) η (mm n) x hx (hfin n x) (q n v) U hU ?_ μB hμB
    (κ / 3) (by linarith) le_rfl hLPv A
  linarith

/-- **The same with the Lévy-Prokhorov bound in the budget form of the covering package.**
Let `α = 1`, `r = κ / 24`, `d ≤ κ / 48` and `ofReal τ ≤ r`. If eventually the stopped walk law started at every
cell `v ∈ R n` with `q n v ∈ U` is within `4 α d + (r + τ)` of the stopped Brownian law started at `q n v`,
then the conclusion of `eventually_forall_vertex_walk_allSet_le` holds, since the bound is at most
`κ / 12 + κ / 12 < κ / 3`. -/
theorem eventually_forall_vertex_walk_allSet_le_of_budget {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (mm : ℕ → ℤ → ℤ → ℕ) (hsucc : ∀ n k, mm n k (k + 1) ≠ 0)
    {ρ R : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    {α m₀ : ℝ≥0} (hα : α = 1) (hm₀ : 0 < m₀) (hm₁ : m₀ = 1)
    (hfin : ∀ n x, ∀ᵐ ξ ∂(srwLaw (mm n) x),
      pathExitTime (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ≠ ⊤)
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (Rs : ∀ n, Set (areaCellConfig h (hε n) (mm n)).cells)
    (hclose : ∀ n (v : (areaCellConfig h (hε n) (mm n)).cells),
      areaCellRepresentative h (hε n) (mm n) v ∈ ball (0 : ReflectedGMS.Plane) R →
        ∀ w, w ∉ Rs n → (areaCellConfig h (hε n) (mm n)).c v w = 0)
    (q : ∀ n, Rs n → ReflectedGMS.Plane)
    (hq : ∀ n (v : Rs n), q n v ∈ ((v.1.1 : Cell) : Set ReflectedGMS.Plane))
    {r : ℝ≥0} (hr : (r : ℝ) = κ / 24) {d τ : ℝ} (hd : d ≤ κ / 48)
    (hτ : ENNReal.ofReal τ ≤ (r : ℝ≥0∞))
    (hLP : ∀ᶠ n in atTop, ∀ v : Rs n, q n v ∈ U →
      levyProkhorovEDist
        ((srwLaw (mm n) ((euclideanCellEquiv h (hε n)).symm v.1)).map
          (fun w : ℕ → ℤ => isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint (ε n) η) hm₀.le w))
              (pathExitTime (ball (0 : ℂ) R)
                ⇑((α : ℝ) • interpPathCM (vertexPoint (ε n) η) hm₀.le w)).toNNReal)))
        (BouRabeeGwynne.stoppedBrownianLaw U (q n v) μB) ≤
          ENNReal.ofReal (4 * ((α : ℝ) * d)) + ((r : ℝ≥0∞) + ENNReal.ofReal τ)) :
    ∀ᶠ n in atTop, ∀ x : ℤ, vertexPoint (ε n) η x ∈ closedBall (0 : ℂ) ρ →
      ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (mm n) x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ∈ A} ≤
        planarBrownianMotion (vertexPoint (ε n) η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ := by
  have hbound : ENNReal.ofReal (4 * ((α : ℝ) * d)) + ((r : ℝ≥0∞) + ENNReal.ofReal τ) <
      ENNReal.ofReal (κ / 3) := by
    have hα1 : (α : ℝ) = 1 := by rw [hα]; simp
    have hr' : (r : ℝ≥0∞) = ENNReal.ofReal (κ / 24) := by
      rw [← hr, ENNReal.ofReal_coe_nnreal]
    have h1 : ENNReal.ofReal (4 * ((α : ℝ) * d)) ≤ ENNReal.ofReal (κ / 12) :=
      ENNReal.ofReal_le_ofReal (by rw [hα1]; linarith)
    calc ENNReal.ofReal (4 * ((α : ℝ) * d)) + ((r : ℝ≥0∞) + ENNReal.ofReal τ)
        ≤ ENNReal.ofReal (κ / 12) + ((r : ℝ≥0∞) + (r : ℝ≥0∞)) := by gcongr
      _ = ENNReal.ofReal (κ / 12 + (κ / 24 + κ / 24)) := by
          rw [hr', ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (κ / 3) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  refine eventually_forall_vertex_walk_allSet_le h hp hε hε0 mm hsucc hρR hκ hα hm₀ hm₁ hfin U hU μB hμB
    Rs hclose q hq ?_
  filter_upwards [hLP] with n hn v hv
  exact lt_of_le_of_lt (hn v hv) hbound

/-- A property holding eventually along the shifted index `n + N` holds eventually. -/
theorem eventually_atTop_of_eventually_add {P : ℕ → Prop} (N : ℕ)
    (h : ∀ᶠ n in atTop, P (n + N)) : ∀ᶠ n in atTop, P n := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨n₀ + N, fun m hm => ?_⟩
  have := hn₀ (m - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- **The vertex inequality in the form delivered by the covering package.**
Same as `eventually_forall_vertex_walk_allSet_le_of_budget`, with the data in the shape of the package
output at the scale `α = 1`: finite cell sets `R (n + N)` (index shift `N`), points `q (n + N) v`
equal to `α • x` for a point `x` of the cell `v`, closure of the conductances of the cells whose scaled
representative lies in a set `Wb ⊇ ball 0 R`, and the budget bound at the cells `v ∈ R (n + N)`. The conclusion
holds eventually along the unshifted sequence. -/
theorem eventually_forall_vertex_walk_allSet_le_of_package {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (mm : ℕ → ℤ → ℤ → ℕ) (hsucc : ∀ n k, mm n k (k + 1) ≠ 0)
    {ρ R : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    {α m₀ : ℝ≥0} (hα : α = 1) (hm₀ : 0 < m₀) (hm₁ : m₀ = 1)
    (hfin : ∀ n x, ∀ᵐ ξ ∂(srwLaw (mm n) x),
      pathExitTime (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ≠ ⊤)
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (Rs : ∀ n, Set (areaCellConfig h (hε n) (mm n)).cells) (N : ℕ)
    (Wb : Set ReflectedGMS.Plane) (hWb : ball (0 : ReflectedGMS.Plane) R ⊆ Wb)
    (hclose : ∀ n (v : (areaCellConfig h (hε (n + N)) (mm (n + N))).cells),
      (α : ℝ) • areaCellRepresentative h (hε (n + N)) (mm (n + N)) v ∈ Wb →
        ∀ w, w ∉ Rs (n + N) → (areaCellConfig h (hε (n + N)) (mm (n + N))).c v w = 0)
    (q : ∀ n, Rs n → ReflectedGMS.Plane)
    (hq : ∀ n (v : Rs (n + N)), ∃ x ∈ ((v.1.1 : Cell) : Set ReflectedGMS.Plane),
      q (n + N) v = (α : ℝ) • x)
    {r : ℝ≥0} (hr : (r : ℝ) = κ / 24) {d τ : ℝ} (hd : d ≤ κ / 48)
    (hτ : ENNReal.ofReal τ ≤ (r : ℝ≥0∞))
    (hLP : ∀ᶠ n in atTop, ∀ v : Rs (n + N), q (n + N) v ∈ U →
      levyProkhorovEDist
        ((srwLaw (mm (n + N)) ((euclideanCellEquiv h (hε (n + N))).symm v.1)).map
          (fun w : ℕ → ℤ => isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint (ε (n + N)) η) hm₀.le w))
              (pathExitTime (ball (0 : ℂ) R)
                ⇑((α : ℝ) • interpPathCM (vertexPoint (ε (n + N)) η) hm₀.le w)).toNNReal)))
        (BouRabeeGwynne.stoppedBrownianLaw U (q (n + N) v) μB) ≤
          ENNReal.ofReal (4 * ((α : ℝ) * d)) + ((r : ℝ≥0∞) + ENNReal.ofReal τ)) :
    ∀ᶠ n in atTop, ∀ x : ℤ, vertexPoint (ε n) η x ∈ closedBall (0 : ℂ) ρ →
      ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (mm n) x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ∈ A} ≤
        planarBrownianMotion (vertexPoint (ε n) η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ := by
  have hα1 : (α : ℝ) = 1 := by rw [hα]; simp
  refine eventually_atTop_of_eventually_add N
    (P := fun n => ∀ x : ℤ, vertexPoint (ε n) η x ∈ closedBall (0 : ℂ) ρ →
      ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (mm n) x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (ε n) η 1 ξ) ∈ A} ≤
        planarBrownianMotion (vertexPoint (ε n) η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ) ?_
  refine eventually_forall_vertex_walk_allSet_le_of_budget (ε := fun n => ε (n + N))
    h hp (fun n => hε (n + N)) (hε0.comp (tendsto_add_atTop_nat N)) (fun n => mm (n + N))
    (fun n k => hsucc (n + N) k) hρR hκ hα hm₀ hm₁ (fun n x => hfin (n + N) x) U hU μB hμB
    (fun n => Rs (n + N)) ?_ (fun n v => q (n + N) v) ?_ hr hd hτ hLP
  · intro n v hv w hw
    refine hclose n v ?_ w hw
    rw [hα1, one_smul]
    exact hWb hv
  · intro n v
    obtain ⟨x, hx, hqx⟩ := hq n v
    rw [hqx, hα1, one_smul]
    exact hx

end MatedCRT.AreaCellVertexInequality
