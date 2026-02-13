import autoproof.Q10.TraceAndRates.RateTheory.KrylovMinimax

set_option autoImplicit false

open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Preconditioned operator in vectorized coordinates:
`vec ∘ (MinvLin ∘ applyALin) ∘ unvec`. -/
def precondDenseVecLin
    (P : Problem n M r q)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real) :
    Module.End Real (Fin r × Fin n → Real) where
  toFun := fun v => (precondApplyALin P MinvLin (unvec v)).vec
  map_add' := by
    intro x y
    have hunvec :
        unvec (x + y) = unvec x + unvec y := by
      ext i j
      simp [unvec]
    ext ij
    rcases ij with ⟨j, i⟩
    simp [precondApplyALin, hunvec, map_add]
  map_smul' := by
    intro a x
    have hunvec :
        unvec (a • x) = a • unvec x := by
      ext i j
      simp [unvec]
    ext ij
    rcases ij with ⟨j, i⟩
    simp [precondApplyALin, hunvec, map_smul]

theorem precondApplyALin_vec_eq_precondDenseVecLin
    (P : Problem n M r q)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (X : Matrix (Fin n) (Fin r) Real) :
    (precondApplyALin P MinvLin X).vec = precondDenseVecLin P MinvLin X.vec := by
  rfl

theorem precondApplyALin_iterate_vec_eq_precondDenseVecLin_iterate
    (P : Problem n M r q)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (k : Nat)
    (X : Matrix (Fin n) (Fin r) Real) :
    (((precondApplyALin P MinvLin)^[k]) X).vec
      = (((precondDenseVecLin P MinvLin)^[k]) X.vec) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        (((precondApplyALin P MinvLin)^[k + 1]) X).vec
            = (precondApplyALin P MinvLin ((((precondApplyALin P MinvLin)^[k]) X))).vec := by
                simp [Function.iterate_succ_apply']
        _ = precondDenseVecLin P MinvLin ((((precondApplyALin P MinvLin)^[k]) X).vec) :=
              precondApplyALin_vec_eq_precondDenseVecLin
                (P := P) (MinvLin := MinvLin) ((((precondApplyALin P MinvLin)^[k]) X))
        _ = precondDenseVecLin P MinvLin
              ((((precondDenseVecLin P MinvLin)^[k]) X.vec) : Fin r × Fin n → Real) := by
              rw [ih]
        _ = (((precondDenseVecLin P MinvLin)^[k + 1]) X.vec) := by
              simp [Function.iterate_succ_apply']

theorem polyApplyLin_precondApplyALin_vec_eq_polyApplyLin_precondDenseVecLin
    (P : Problem n M r q)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (p : Polynomial Real)
    (X : Matrix (Fin n) (Fin r) Real) :
    (polyApplyLin (precondApplyALin P MinvLin) p X).vec
      = polyApplyLin (precondDenseVecLin P MinvLin) p X.vec := by
  induction p using Polynomial.induction_on with
  | C a =>
      simp [polyApplyLin]
  | add p q ihp ihq =>
      simpa [polyApplyLin] using congrArg₂ (fun u v => u + v) ihp ihq
  | monomial m a _ =>
      have hRecurrence :
          (precondApplyALin P MinvLin ((((precondApplyALin P MinvLin)^[m]) X))).vec
            = precondDenseVecLin P MinvLin
                ((((precondDenseVecLin P MinvLin)^[m]) X.vec) : Fin r × Fin n → Real) := by
        calc
          (precondApplyALin P MinvLin ((((precondApplyALin P MinvLin)^[m]) X))).vec
              = precondDenseVecLin P MinvLin ((((precondApplyALin P MinvLin)^[m]) X).vec) :=
                  precondApplyALin_vec_eq_precondDenseVecLin
                    (P := P) (MinvLin := MinvLin) ((((precondApplyALin P MinvLin)^[m]) X))
          _ = precondDenseVecLin P MinvLin
                ((((precondDenseVecLin P MinvLin)^[m]) X.vec) : Fin r × Fin n → Real) := by
                rw [precondApplyALin_iterate_vec_eq_precondDenseVecLin_iterate
                  (P := P) (MinvLin := MinvLin) (k := m) (X := X)]
      have hSmul :
          a • (precondApplyALin P MinvLin ((((precondApplyALin P MinvLin)^[m]) X))).vec
            = a • precondDenseVecLin P MinvLin
                ((((precondDenseVecLin P MinvLin)^[m]) X.vec) : Fin r × Fin n → Real) :=
        congrArg (fun t => a • t) hRecurrence
      simpa [polyApplyLin, Module.End.pow_apply, Function.iterate_succ_apply'] using hSmul

/-- Generic matrix-vector form of polynomial action for a linear endomorphism on
`Fin r × Fin n → Real`. -/
theorem polyApplyLin_linEnd_eq_aeval_mulVec
    (f : Module.End Real (Fin r × Fin n → Real))
    (p : Polynomial Real)
    (v : Fin r × Fin n → Real) :
    polyApplyLin f p v = (Polynomial.aeval (LinearMap.toMatrixAlgEquiv' f) p) *ᵥ v := by
  let ψ :
      ((Fin r × Fin n → Real) →ₗ[Real] (Fin r × Fin n → Real)) →+*
        Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
    (LinearMap.toMatrixAlgEquiv' :
      ((Fin r × Fin n → Real) →ₗ[Real] (Fin r × Fin n → Real)) ≃ₐ[Real]
      Matrix (Fin r × Fin n) (Fin r × Fin n) Real).toRingHom
  have hmap := Polynomial.map_aeval_eq_aeval_map
    (R := Real)
    (S := ((Fin r × Fin n → Real) →ₗ[Real] (Fin r × Fin n → Real)))
    (T := Real)
    (U := Matrix (Fin r × Fin n) (Fin r × Fin n) Real)
    (φ := RingHom.id Real) (ψ := ψ)
    (h := by
      ext x i j
      change (algebraMap Real (Matrix (Fin r × Fin n) (Fin r × Fin n) Real) x) i j
        = x * ((Pi.single j (1 : Real) : (Fin r × Fin n) → Real) i)
      by_cases hij : i = j
      · subst hij
        simp [Matrix.algebraMap_eq_diagonal]
      · simp [Matrix.algebraMap_eq_diagonal, hij])
    p f
  have hEndMat :
      LinearMap.toMatrixAlgEquiv' (Polynomial.aeval f p)
        = Polynomial.aeval (LinearMap.toMatrixAlgEquiv' f) p := by
    simpa [ψ, Polynomial.map_id, RingHom.id_apply] using hmap
  have hEnd :
      Polynomial.aeval f p
        = Matrix.toLinAlgEquiv' (Polynomial.aeval (LinearMap.toMatrixAlgEquiv' f) p) := by
    apply Matrix.toLinAlgEquiv'.symm.injective
    simpa using hEndMat
  calc
    polyApplyLin f p v
        = (Polynomial.aeval f p) v := by rfl
    _ = (Matrix.toLinAlgEquiv' (Polynomial.aeval (LinearMap.toMatrixAlgEquiv' f) p)) v := by rw [hEnd]
    _ = (Polynomial.aeval (LinearMap.toMatrixAlgEquiv' f) p) *ᵥ v := by
          simp [Matrix.toLinAlgEquiv'_apply]

/-- Preconditioned interval-to-operator certificate:
for the preconditioned linear operator and seed `Minv r₀`, every interval polynomial
envelope yields the corresponding vector-action norm bound. -/
def IntervalToOperatorBoundPrecond
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (mu L err0z : Real) : Prop :=
  ∀ p : Polynomial Real, ∀ c : Real, IntervalPolyBound mu L p c →
    ‖(polyApplyLin (precondApplyALin P MinvLin) p (Minv (pcgR0 P x0))).vec‖ ≤ c * err0z

/-- Internal spectral bridge for `IntervalToOperatorBoundPrecond`:
derive the preconditioned interval-operator certificate from symmetry/spectrum of
the vectorized preconditioned operator and an L2 bound of the preconditioned seed. -/
theorem intervalToOperatorBoundPrecond_of_denseSpectrum
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (mu L err0z : Real)
    (hMuLeL : mu ≤ L)
    (hSymm :
      (LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))ᵀ
        = LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))
    (hEigRange :
      spectrum ℝ (LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))
        ⊆ Set.Icc mu L)
    (hErr0z : ‖WithLp.toLp 2 (Minv (pcgR0 P x0)).vec‖ ≤ err0z) :
    IntervalToOperatorBoundPrecond P Minv MinvLin x0 mu L err0z := by
  letI : Fintype (Fin r × Fin n) := inferInstance
  letI : DecidableEq (Fin r × Fin n) := inferInstance
  intro p c hB
  have hc : 0 ≤ c := by
    exact le_trans (abs_nonneg (p.eval mu)) (hB mu le_rfl hMuLeL)
  let A : Matrix (Fin r × Fin n) (Fin r × Fin n) Real :=
    LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin)
  have hHerm : A.IsHermitian := by
    simpa [A, Matrix.IsHermitian, Matrix.conjTranspose] using hSymm
  have hOp : ‖Polynomial.aeval A p‖ ≤ c :=
    matrix_aeval_opNorm_le_of_intervalSpectrum
      (A := A) (hA := hHerm) (mu := mu) (L := L) (c := c)
      (hEigRange := by simpa [A] using hEigRange) (p := p) (hBound := hB) (hc := hc)
  let z0 : Matrix (Fin n) (Fin r) Real := Minv (pcgR0 P x0)
  let x : EuclideanSpace Real (Fin r × Fin n) :=
    (EuclideanSpace.equiv (Fin r × Fin n) Real).symm z0.vec
  have hx_ofLp : x.ofLp = z0.vec := by
    simpa [x, z0] using
      (EuclideanSpace.equiv (Fin r × Fin n) Real).apply_symm_apply z0.vec
  have hMul := Matrix.l2_opNorm_mulVec (A := Polynomial.aeval A p) (x := x)
  have hMul' :
      ‖(EuclideanSpace.equiv (Fin r × Fin n) Real).symm
          ((Polynomial.aeval A p) *ᵥ z0.vec)‖
        ≤ ‖Polynomial.aeval A p‖ * ‖x‖ := by
    simpa [hx_ofLp] using hMul
  have hMul'' :
      ‖(EuclideanSpace.equiv (Fin r × Fin n) Real).symm
          ((Polynomial.aeval A p) *ᵥ z0.vec)‖
        ≤ c * err0z := by
    have h1 : ‖Polynomial.aeval A p‖ * ‖x‖ ≤ c * ‖x‖ := by gcongr
    have h2 : c * ‖x‖ ≤ c * err0z := by
      gcongr
      simpa [x, z0] using hErr0z
    exact le_trans hMul' (le_trans h1 h2)
  have hVecEq :
      (polyApplyLin (precondApplyALin P MinvLin) p z0).vec
        = (Polynomial.aeval A p) *ᵥ z0.vec := by
    calc
      (polyApplyLin (precondApplyALin P MinvLin) p z0).vec
          = polyApplyLin (precondDenseVecLin P MinvLin) p z0.vec := by
              simpa [z0] using
                (polyApplyLin_precondApplyALin_vec_eq_polyApplyLin_precondDenseVecLin
                  (P := P) (MinvLin := MinvLin) (p := p) (X := z0))
      _ = (Polynomial.aeval (LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin)) p) *ᵥ z0.vec :=
            polyApplyLin_linEnd_eq_aeval_mulVec
              (f := precondDenseVecLin P MinvLin) (p := p) (v := z0.vec)
      _ = (Polynomial.aeval A p) *ᵥ z0.vec := by rfl
  have hL2Bound :
      ‖WithLp.toLp 2 ((polyApplyLin (precondApplyALin P MinvLin) p z0).vec)‖ ≤ c * err0z := by
    simpa [hVecEq, x, z0] using hMul''
  calc
    ‖(polyApplyLin (precondApplyALin P MinvLin) p z0).vec‖
        ≤ ‖WithLp.toLp 2 ((polyApplyLin (precondApplyALin P MinvLin) p z0).vec)‖ :=
          vec_norm_le_toLp2_norm
            (v := (polyApplyLin (precondApplyALin P MinvLin) p z0).vec)
    _ ≤ c * err0z := hL2Bound

/-- From canonical preconditioned residual-polynomial interval control and a stable left inverse,
derive a concrete residual bound at step `k` directly from the PCG algorithm body. -/
theorem pcgResidualNorm_le_of_precond_residualPolyRec_interval
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (MinvInv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {mu L err0z cInv cPoly : Real}
    (hMinv : ∀ X : Matrix (Fin n) (Fin r) Real, Minv X = MinvLin X)
    (hLeftInv : ∀ X : Matrix (Fin n) (Fin r) Real, MinvInv (Minv X) = X)
    (hcInv : 0 ≤ cInv)
    (hInvBound : ∀ X : Matrix (Fin n) (Fin r) Real,
      ‖(MinvInv X).vec‖ ≤ cInv * ‖X.vec‖)
    (hInt : IntervalToOperatorBoundPrecond P Minv MinvLin x0 mu L err0z)
    (k : Nat)
    (hPoly : IntervalPolyBound mu L (pcgPrecondResidualPolyRec P Minv x0 k) cPoly) :
    pcgResidualNorm P Minv x0 k ≤ cInv * (cPoly * err0z) := by
  have hCore :
      ‖(pcgRun P Minv x0 k).r.vec‖
        ≤ cInv * ‖(polyApplyLin (precondApplyALin P MinvLin)
            (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖ :=
    pcgRun_precond_residual_norm_le_leftInverse_polyRec
      (P := P) (Minv := Minv) (MinvLin := MinvLin) (MinvInv := MinvInv)
      (x0 := x0) (hMinv := hMinv) (hLeftInv := hLeftInv) (hInvBound := hInvBound) k
  have hPolyBound :
      ‖(polyApplyLin (precondApplyALin P MinvLin)
          (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖
        ≤ cPoly * err0z := hInt _ _ hPoly
  have hScale :
      cInv * ‖(polyApplyLin (precondApplyALin P MinvLin)
          (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖
        ≤ cInv * (cPoly * err0z) := by
    exact mul_le_mul_of_nonneg_left hPolyBound hcInv
  exact le_trans (by simpa [pcgResidualNorm] using hCore) hScale

/-- Canonical coefficient-based interval envelope for a polynomial on `[mu, L]`:
sum of absolute coefficients weighted by `max(|mu|, |L|)^i`. -/
def polyAbsBoundOnIcc (mu L : Real) (p : Polynomial Real) : Real :=
  Finset.sum (Finset.range (p.natDegree + 1))
    (fun i => |p.coeff i| * (max (|mu|) (|L|)) ^ i)

/-- The coefficient-based envelope `polyAbsBoundOnIcc` bounds `|p(x)|` on `[mu, L]`. -/
theorem intervalPolyBound_polyAbsBoundOnIcc
    (mu L : Real) (p : Polynomial Real) :
    IntervalPolyBound mu L p (polyAbsBoundOnIcc mu L p) := by
  intro x hxMu hxL
  let m : Real := max (|mu|) (|L|)
  have hAbsx : |x| ≤ m := by
    have hLower : -m ≤ x := by
      calc
        -m ≤ -|mu| := by
          dsimp [m]
          exact neg_le_neg (le_max_left _ _)
        _ ≤ mu := by simpa using (neg_abs_le mu)
        _ ≤ x := hxMu
    have hUpper : x ≤ m := by
      calc
        x ≤ L := hxL
        _ ≤ |L| := le_abs_self L
        _ ≤ m := by
          dsimp [m]
          exact le_max_right _ _
    exact abs_le.mpr ⟨hLower, hUpper⟩
  have hEval :
      p.eval x = Finset.sum (Finset.range (p.natDegree + 1)) (fun i => p.coeff i * x ^ i) := by
    simpa using (Polynomial.eval_eq_sum_range (p := p) x)
  calc
    |p.eval x|
        = |Finset.sum (Finset.range (p.natDegree + 1)) (fun i => p.coeff i * x ^ i)| := by rw [hEval]
    _ ≤ Finset.sum (Finset.range (p.natDegree + 1)) (fun i => |p.coeff i * x ^ i|) := by
          simpa using (Finset.abs_sum_le_sum_abs
            (s := Finset.range (p.natDegree + 1)) (f := fun i => p.coeff i * x ^ i))
    _ = Finset.sum (Finset.range (p.natDegree + 1)) (fun i => |p.coeff i| * |x| ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [abs_mul, abs_pow]
    _ ≤ Finset.sum (Finset.range (p.natDegree + 1)) (fun i => |p.coeff i| * m ^ i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg x) hAbsx i)
            (abs_nonneg (p.coeff i))
    _ = polyAbsBoundOnIcc mu L p := by
          simp [polyAbsBoundOnIcc, m]

/-- No-`hPolyEnvelope` residual bound from the algorithm body:
for each `k`, use the canonical coefficient envelope of
`pcgPrecondResidualPolyRec` on `[μ,L]`. -/
theorem pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (MinvInv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {mu L err0z cInv : Real}
    (hMinv : ∀ X : Matrix (Fin n) (Fin r) Real, Minv X = MinvLin X)
    (hLeftInv : ∀ X : Matrix (Fin n) (Fin r) Real, MinvInv (Minv X) = X)
    (hcInv : 0 ≤ cInv)
    (hInvBound : ∀ X : Matrix (Fin n) (Fin r) Real,
      ‖(MinvInv X).vec‖ ≤ cInv * ‖X.vec‖)
    (hInt : IntervalToOperatorBoundPrecond P Minv MinvLin x0 mu L err0z) :
    ∀ k : Nat,
      pcgResidualNorm P Minv x0 k
        ≤ cInv * (polyAbsBoundOnIcc mu L (pcgPrecondResidualPolyRec P Minv x0 k) * err0z) := by
  intro k
  have hPoly :
      IntervalPolyBound mu L (pcgPrecondResidualPolyRec P Minv x0 k)
        (polyAbsBoundOnIcc mu L (pcgPrecondResidualPolyRec P Minv x0 k)) :=
    intervalPolyBound_polyAbsBoundOnIcc (mu := mu) (L := L)
      (p := pcgPrecondResidualPolyRec P Minv x0 k)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    pcgResidualNorm_le_of_precond_residualPolyRec_interval
      (P := P) (Minv := Minv) (MinvLin := MinvLin) (MinvInv := MinvInv)
      (x0 := x0) (mu := mu) (L := L) (err0z := err0z) (cInv := cInv)
      (cPoly := polyAbsBoundOnIcc mu L (pcgPrecondResidualPolyRec P Minv x0 k))
      (hMinv := hMinv) (hLeftInv := hLeftInv) (hcInv := hcInv)
      (hInvBound := hInvBound) (hInt := hInt) (k := k) (hPoly := hPoly)

/-- Dense-spectrum specialization of
`pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope`: no `hPolyEnvelope`
input is required, only operator spectrum/symmetry and a seed norm bound. -/
theorem pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope_of_denseSpectrum
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (MinvInv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {mu L err0z cInv : Real}
    (hMuLeL : mu ≤ L)
    (hMinv : ∀ X : Matrix (Fin n) (Fin r) Real, Minv X = MinvLin X)
    (hLeftInv : ∀ X : Matrix (Fin n) (Fin r) Real, MinvInv (Minv X) = X)
    (hcInv : 0 ≤ cInv)
    (hInvBound : ∀ X : Matrix (Fin n) (Fin r) Real,
      ‖(MinvInv X).vec‖ ≤ cInv * ‖X.vec‖)
    (hSymm :
      (LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))ᵀ
        = LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))
    (hEigRange :
      spectrum ℝ (LinearMap.toMatrixAlgEquiv' (precondDenseVecLin P MinvLin))
        ⊆ Set.Icc mu L)
    (hErr0z : ‖WithLp.toLp 2 (Minv (pcgR0 P x0)).vec‖ ≤ err0z) :
    ∀ k : Nat,
      pcgResidualNorm P Minv x0 k
        ≤ cInv * (polyAbsBoundOnIcc mu L (pcgPrecondResidualPolyRec P Minv x0 k) * err0z) := by
  have hInt :
      IntervalToOperatorBoundPrecond P Minv MinvLin x0 mu L err0z :=
    intervalToOperatorBoundPrecond_of_denseSpectrum
      (P := P) (Minv := Minv) (MinvLin := MinvLin) (x0 := x0)
      (mu := mu) (L := L) (err0z := err0z)
      (hMuLeL := hMuLeL) (hSymm := hSymm) (hEigRange := hEigRange) (hErr0z := hErr0z)
  exact pcgResidualNorm_le_of_precond_residualPolyRec_coeffEnvelope
    (P := P) (Minv := Minv) (MinvLin := MinvLin) (MinvInv := MinvInv)
    (x0 := x0) (mu := mu) (L := L) (err0z := err0z) (cInv := cInv)
    (hMinv := hMinv) (hLeftInv := hLeftInv) (hcInv := hcInv)
    (hInvBound := hInvBound) (hInt := hInt)

end
end Q10
end AutoProof
