import MatedCRT.FirstPass.S1S2S8SA

/-!
# Closed results, Appendix A (task fp-Closure-counted-results, worker z1)

Each `closed_A_k` is `firstPass_A_k` (S1S2S8SA.lean), restated by `alias`. The firstPass theorems have no
hypotheses, so the closed results have none. Discrete potential theory: discrete divergence theorem and discrete
conservation of mass of the divisible sandpile (Armitage-Gardiner style discrete Laplacian).
-/

namespace MatedCRT

/-- Appendix A.1 (discrete divergence theorem), closed. No hypotheses. -/
alias closed_A_1 := firstPass_A_1

/-- Appendix A.2 (discrete basic properties, general form), closed. No hypotheses. -/
alias closed_A_2 := firstPass_A_2

/-- Appendix A.3 (discrete Laplacian bound, general form), closed. No hypotheses. -/
alias closed_A_3 := firstPass_A_3

/-- Appendix A.4 (discrete conservation of mass, general form), closed. No hypotheses. -/
alias closed_A_4 := firstPass_A_4

end MatedCRT
