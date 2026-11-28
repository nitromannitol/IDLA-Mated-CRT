import MatedCRT.FirstPass.Derived.GMS21Theorem310Form
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem310

/-!
# Gwynne–Miller–Sheffield, Theorem 3.10, proved

`GMSTheorem310` (`GMS21Theorem310Form.lean`) copies the statement `ReflectedGMS.GMS.Theorem3_10` of the
Lattice-Probability file `LatticeProb/Bonanno/ReflectedGMS/GMS/Theorem310Statement.lean`, which Lattice-Probability
proves as `ReflectedGMS.GMS.theorem3_10` (`LatticeProb/Bonanno/ReflectedGMS/GMS/Theorem310.lean`): Theorem 3.10 of
Gwynne–Miller–Sheffield, arXiv:1807.07515, the invariance principle uniform in the starting point. The copied
definitions have the same bodies as the originals, so the two statements agree by unfolding.

## Main statements

* `gmsTheorem310`: Theorem 3.10 of arXiv:1807.07515, `GMSTheorem310`, with no hypothesis.
-/

set_option autoImplicit false

namespace MatedCRT

/-- **Gwynne–Miller–Sheffield, Theorem 3.10** (arXiv:1807.07515): every probability law on the GMS space with mass
transport, ergodicity modulo scaling, finite expectation and connectedness along lines satisfies the uniform-start
invariance principle `GMSTheorem310Form`. -/
theorem gmsTheorem310 : GMSTheorem310 := ReflectedGMS.GMS.theorem3_10

end MatedCRT
