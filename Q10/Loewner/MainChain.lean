import autoproof.Q10.SolutionClosure.StrictLoewner

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Mainline terminal strict closure from data-lower assumptions. -/
theorem q10_mainline_terminal_compare_auto_strict_from_data_lower
    (P : TexProblem n M r q)
    (beta err0 eps : Real)
    (hLamNonneg : 0 ≤ P.lam)
    (hKpsd : P.K.PosSemidef)
    (hLamPos : 0 < P.lam)
    (hBetaPos : 0 < beta)
    (hBetaLeOne : beta ≤ 1)
    (hBetaLtTrace : beta < P.K.trace + 1)
    (hBetaGtAutoInverse :
      (1 / (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) < beta)
    (hDataLower :
      ∀ x : Fin r × Fin n → Real,
        beta * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x))
          ≤ star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x))
    (hErr0 : 0 < err0)
    (hEps : 0 < eps) :
    (QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧
      QuadraticLe (denseMatrix P.toProblem)
        (((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam))
          • precond1Matrix P.toProblem) ∧
      spectralKappa beta (P.K.trace + 1)
        < spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) ∧
      pcgRate (spectralKappa beta (P.K.trace + 1))
        < pcgRate (spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ∧
    (∃ k1 k2 : Nat,
      2 * (pcgRate (spectralKappa (1 : Real)
            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ^ k1
            * err0 ≤ eps ∧
      2 * (pcgRate (spectralKappa beta (P.K.trace + 1))) ^ k2 * err0 ≤ eps ∧
      k2 ≤ k1) := by
  exact q10_solutiontxt_terminal_compare_auto_strict_from_data_lower
    (P := P) (beta := beta) (err0 := err0) (eps := eps)
    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)
    (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)
    (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)
    (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)

end
end Q10
end AutoProof
