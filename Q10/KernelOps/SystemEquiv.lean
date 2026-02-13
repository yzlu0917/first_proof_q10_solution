import autoproof.Q10.Core.Operators.ObservedOps

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Mainline kernel-operator identity: dense vectorized system and sparse matrix-free system
are definitionally equivalent on every iterate. -/
theorem q10_mainline_system_equiv_matrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W B : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = rhsVec K B ↔ applyMatrixFreeSparse K Z Ω lam W = K * B := by
  simpa using q10_system_equiv_matrixFreeSparse
    (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK) (W := W) (B := B)

end
end Q10
end AutoProof
