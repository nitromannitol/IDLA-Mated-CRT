import MatedCRT.FirstPass.Derived.BrownianBlockExitBounds
import LatticeProb.Euclidean.GridEdgeRectangle

/-!
# The block-exit kernel of planar Brownian motion with a frozen region

The position kernel of the chaining step in the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield
invariance principle. For a mesh `s > 0`, a point `y ∈ ℂ` lies in the closed grid cell with index
`cellIndex s y = (⌊y.re / s⌋, ⌊y.im / s⌋)`; the kernel moves `y` to the exit point of planar
Brownian motion started at `y` from the open block of side `3 s` around that cell. On a frozen set
`F` (in the application, the complement of an open grid rectangle) the kernel is the Dirac mass at `y`.

* `exitPoint_eq_exitPosition`: the exit point `ω (τ_U ω).toNNReal` used in the block bounds is the
  exit position `exitPosition U`, hence measurable for open `U`.
* `cellBlockExitKernel`, `frozenBlockExitKernel`: the Markov kernels.
* `frozenBlockExitKernel_le_thickening_add`: for `y`, `b` in the same cell with the same freeze
  status and `dist y b < R ≤ r`, `κ y A ≤ κ b (thickening r A) + 24 R / s`.
* `frozenBlockExitKernel_le_thickening_add_of_gridLines`: the same for the frozen set
  `(gridRectOpen s a₁ a₂ c₁ c₂)ᶜ`, two points of the grid lines and `R ≤ infDist b (vertices s)`,
  `R ≤ s`: both conditions follow from the grid geometry.
* `frozenBlockExitKernel_latticeNbhd_le`: the mass of the `r`-neighbourhood `latticeNbhd s r` of
  the lattice `s ℤ + i s ℤ` grows by at most `144 r / s` in one step (`r ≤ s / 4`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- The exit point `ω (τ_U ω).toNNReal` of a path is its exit position (both read the path at time
`0` when it never leaves `U`). -/
theorem exitPoint_eq_exitPosition (U : Set ℂ) :
    (fun ω : ContinuousPath ℂ => ω ((ContinuousPath.exitTime U ω).toNNReal)) =
      exitPosition U := by
  funext ω
  by_cases h : ContinuousPath.exitTime U ω = ⊤
  · simp [exitPosition, ContinuousPath.exitTimeTop_apply, h]
    rfl
  · exact (exitPosition_eq U ω h).symm

theorem measurable_cellIndex (s : ℝ) : Measurable (cellIndex s) :=
  (Int.measurable_floor.comp (Complex.measurable_re.div_const s)).prodMk
    (Int.measurable_floor.comp (Complex.measurable_im.div_const s))

/-- A point lies in the closed grid cell of its own index. -/
theorem mem_closedCell_cellIndex {s : ℝ} (hs : 0 < s) (y : ℂ) :
    y ∈ closedCell s (cellIndex s y).1 (cellIndex s y).2 := by
  simp only [closedCell, cellIndex, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (le_div_iff₀ hs).1 (Int.floor_le _)
  · exact ((div_lt_iff₀ hs).1 (Int.lt_floor_add_one _)).le
  · exact (le_div_iff₀ hs).1 (Int.floor_le _)
  · exact ((div_lt_iff₀ hs).1 (Int.lt_floor_add_one _)).le

/-- The law of the exit point from the block with index `c`, as a kernel in the starting point. -/
noncomputable def blockExitKernel (s : ℝ) (c : ℤ × ℤ) : Kernel ℂ ℂ :=
  planarBrownianMotion.map (exitPosition (openBlock s c.1 c.2))

instance isMarkovKernel_blockExitKernel (s : ℝ) (c : ℤ × ℤ) :
    IsMarkovKernel (blockExitKernel s c) :=
  Kernel.IsMarkovKernel.map _ (measurable_exitPosition (isOpen_openBlock s c.1 c.2))

theorem blockExitKernel_apply (s : ℝ) (c : ℤ × ℤ) (y : ℂ) :
    blockExitKernel s c y = (planarBrownianMotion y).map (exitPosition (openBlock s c.1 c.2)) :=
  Kernel.map_apply _ (measurable_exitPosition (isOpen_openBlock s c.1 c.2)) y

/-- The exit law from the block with index `c` started at `y`, jointly in `(y, c)`. -/
noncomputable def blockExitKernelProd (s : ℝ) : Kernel (ℂ × (ℤ × ℤ)) ℂ where
  toFun p := blockExitKernel s p.2 p.1
  measurable' := measurable_from_prod_countable_left fun c => (blockExitKernel s c).measurable

theorem measurable_prod_cellIndex (s : ℝ) : Measurable (fun y : ℂ => (y, cellIndex s y)) :=
  measurable_id.prodMk (measurable_cellIndex s)

/-- The block-exit kernel: Brownian motion from `y` run until it leaves the open block of side
`3 s` around the grid cell of `y`. -/
noncomputable def cellBlockExitKernel (s : ℝ) : Kernel ℂ ℂ :=
  (blockExitKernelProd s).comap (fun y => (y, cellIndex s y)) (measurable_prod_cellIndex s)

theorem cellBlockExitKernel_apply (s : ℝ) (y : ℂ) :
    cellBlockExitKernel s y = blockExitKernel s (cellIndex s y) y := rfl

instance isMarkovKernel_cellBlockExitKernel (s : ℝ) : IsMarkovKernel (cellBlockExitKernel s) := by
  refine ⟨fun y => ?_⟩
  rw [cellBlockExitKernel_apply]
  infer_instance

/-- The value of the block-exit kernel on a Borel set, in the exit-point form of the block bounds. -/
theorem cellBlockExitKernel_apply_set (s : ℝ) (y : ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    cellBlockExitKernel s y A = planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime
      (openBlock s (cellIndex s y).1 (cellIndex s y).2) ω).toNNReal) ∈ A} := by
  rw [cellBlockExitKernel_apply, blockExitKernel_apply,
    Measure.map_apply (measurable_exitPosition (isOpen_openBlock _ _ _)) hA,
    ← exitPoint_eq_exitPosition]
  rfl

/-- **Lipschitz bound in the start, same cell.** -/
theorem cellBlockExitKernel_le_add {s : ℝ} (hs : 0 < s) {y b : ℂ}
    (hc : cellIndex s y = cellIndex s b) {A : Set ℂ} (hA : MeasurableSet A) :
    cellBlockExitKernel s y A ≤ cellBlockExitKernel s b A + ENNReal.ofReal (24 * dist y b / s) := by
  rw [cellBlockExitKernel_apply_set s y hA, cellBlockExitKernel_apply_set s b hA, hc]
  have h := abs_planarBrownian_exitPoint_openBlock_sub_le hs (mem_closedCell_cellIndex hs b) y hA
  set P := planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime
    (openBlock s (cellIndex s b).1 (cellIndex s b).2) ω).toNNReal) ∈ A}
  set Q := planarBrownianMotion b {ω | ω ((ContinuousPath.exitTime
    (openBlock s (cellIndex s b).1 (cellIndex s b).2) ω).toNNReal) ∈ A}
  have hP : P ≠ ⊤ := measure_ne_top _ _
  have hQ : Q ≠ ⊤ := measure_ne_top _ _
  have hle : P.toReal ≤ Q.toReal + 24 * dist y b / s := by
    have := (abs_le.1 h).1
    linarith
  calc P = ENNReal.ofReal P.toReal := (ENNReal.ofReal_toReal hP).symm
    _ ≤ ENNReal.ofReal (Q.toReal + 24 * dist y b / s) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal Q.toReal + ENNReal.ofReal (24 * dist y b / s) := ENNReal.ofReal_add_le
    _ = Q + ENNReal.ofReal (24 * dist y b / s) := by rw [ENNReal.ofReal_toReal hQ]

/-- The open `r`-neighbourhood of the lattice `s ℤ + i s ℤ`. -/
def latticeNbhd (s r : ℝ) : Set ℂ := {x | ∃ m k : ℤ, dist x ⟨(m : ℝ) * s, (k : ℝ) * s⟩ < r}

theorem isOpen_latticeNbhd (s r : ℝ) : IsOpen (latticeNbhd s r) := by
  have : latticeNbhd s r = ⋃ m : ℤ, ⋃ k : ℤ, ball (⟨(m : ℝ) * s, (k : ℝ) * s⟩ : ℂ) r := by
    ext x
    simp [latticeNbhd, mem_ball]
  rw [this]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem measurableSet_latticeNbhd (s r : ℝ) : MeasurableSet (latticeNbhd s r) :=
  (isOpen_latticeNbhd s r).measurableSet

/-- **Mass near the lattice, one step.** -/
theorem cellBlockExitKernel_latticeNbhd_le {s : ℝ} (hs : 0 < s) (y : ℂ) {r : ℝ} (hr : 0 < r)
    (hrs : r ≤ s / 4) :
    cellBlockExitKernel s y (latticeNbhd s r) ≤ ENNReal.ofReal (144 * r / s) := by
  rw [cellBlockExitKernel_apply_set s y (measurableSet_latticeNbhd s r)]
  exact planarBrownian_exitPoint_near_lattice_le hs (mem_closedCell_cellIndex hs y) hr hrs

/-- The block-exit kernel frozen on `F`: the Dirac mass at `y` for `y ∈ F`, the block exit
otherwise. -/
noncomputable def frozenBlockExitKernel (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) :
    Kernel ℂ ℂ :=
  open Classical in Kernel.piecewise hF (Kernel.deterministic id measurable_id)
    (cellBlockExitKernel s)

theorem frozenBlockExitKernel_of_mem (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) {y : ℂ}
    (hy : y ∈ F) : frozenBlockExitKernel s hF y = Measure.dirac y := by
  simp [frozenBlockExitKernel, Kernel.piecewise_apply, hy, Kernel.deterministic_apply]

theorem frozenBlockExitKernel_of_notMem (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) {y : ℂ}
    (hy : y ∉ F) : frozenBlockExitKernel s hF y = cellBlockExitKernel s y := by
  simp [frozenBlockExitKernel, Kernel.piecewise_apply, hy]

instance isMarkovKernel_frozenBlockExitKernel (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) :
    IsMarkovKernel (frozenBlockExitKernel s hF) := by
  unfold frozenBlockExitKernel
  infer_instance

/-- **Continuity of the frozen kernel, same cell and same freeze status.** -/
theorem frozenBlockExitKernel_le_thickening_add {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    (hF : MeasurableSet F) {y b : ℂ} (hc : cellIndex s y = cellIndex s b) (hFyb : y ∈ F ↔ b ∈ F)
    {R r : ℝ} (hd : dist y b < R) (hRr : R ≤ r) {A : Set ℂ} (hA : MeasurableSet A) :
    frozenBlockExitKernel s hF y A ≤
      frozenBlockExitKernel s hF b (thickening r A) + ENNReal.ofReal (24 * R / s) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (hd.trans_le hRr)
  by_cases hy : y ∈ F
  · rw [frozenBlockExitKernel_of_mem s hF hy, frozenBlockExitKernel_of_mem s hF (hFyb.1 hy),
      Measure.dirac_apply' _ hA]
    refine le_add_right ?_
    by_cases hyA : y ∈ A
    · have hb : b ∈ thickening r A :=
        mem_thickening_iff.2 ⟨y, hyA, by rw [dist_comm]; exact hd.trans_le hRr⟩
      simp [hyA, Measure.dirac_apply_of_mem hb]
    · simp [hyA]
  · rw [frozenBlockExitKernel_of_notMem s hF hy,
      frozenBlockExitKernel_of_notMem s hF (fun hb => hy (hFyb.2 hb))]
    calc cellBlockExitKernel s y A
        ≤ cellBlockExitKernel s b A + ENNReal.ofReal (24 * dist y b / s) :=
          cellBlockExitKernel_le_add hs hc hA
      _ ≤ cellBlockExitKernel s b (thickening r A) + ENNReal.ofReal (24 * R / s) := by
          have hdb : dist y b ≤ R := hd.le
          exact add_le_add (measure_mono (self_subset_thickening hr A))
            (ENNReal.ofReal_le_ofReal (by gcongr))

theorem isOpen_gridRectOpen (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) : IsOpen (gridRectOpen s a₁ a₂ c₁ c₂) := by
  simp only [gridRectOpen, ofPred_and]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

/-- **Continuity of the kernel frozen off an open grid rectangle, on the grid lines.** For two
points `y`, `b` of the grid lines with `dist y b < R`, `R ≤ s` and `R ≤ infDist b (vertices s)`,
both lie in the same cell and have the same freeze status. -/
theorem frozenBlockExitKernel_le_thickening_add_of_gridLines {s : ℝ} (hs : 0 < s)
    (a₁ a₂ c₁ c₂ : ℤ) {y b : ℂ} (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) {R r : ℝ}
    (hd : dist y b < R) (hRs : R ≤ s) (hfar : R ≤ infDist b (vertices s)) (hRr : R ≤ r)
    {A : Set ℂ} (hA : MeasurableSet A) :
    frozenBlockExitKernel s (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl y A ≤
      frozenBlockExitKernel s (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl b
        (thickening r A) + ENNReal.ofReal (24 * R / s) :=
  frozenBlockExitKernel_le_thickening_add hs _
    (cellIndex_eq_of_le_infDist_vertices hs hRs hy hb hd hfar)
    (not_congr (mem_gridRectOpen_iff_of_le_infDist hs hRs hy hb hd hfar a₁ a₂ c₁ c₂)) hd hRr hA

/-- **Mass near the lattice, one step of the frozen kernel**: `κ x D_r ≤ 1_{D_r}(x) + 144 r / s`. -/
theorem frozenBlockExitKernel_latticeNbhd_le {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    (hF : MeasurableSet F) (x : ℂ) {r : ℝ} (hr : 0 < r) (hrs : r ≤ s / 4) :
    frozenBlockExitKernel s hF x (latticeNbhd s r) ≤
      (latticeNbhd s r).indicator 1 x + ENNReal.ofReal (144 * r / s) := by
  by_cases hx : x ∈ F
  · rw [frozenBlockExitKernel_of_mem s hF hx, Measure.dirac_apply' _ (measurableSet_latticeNbhd s r)]
    exact le_self_add
  · rw [frozenBlockExitKernel_of_notMem s hF hx]
    exact (cellBlockExitKernel_latticeNbhd_le hs x hr hrs).trans le_add_self

end BlockExit

end MatedCRT
