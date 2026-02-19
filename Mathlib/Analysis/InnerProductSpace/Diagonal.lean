/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Diagonal operators on finite `PiLp 2` direct sums

This file defines diagonal actions of bounded operators on finite direct sums represented as
`PiLp 2`, together with coordinate maps for matrix-entry arguments.

## Main definitions

* `ContinuousLinearMap.diagOp`: diagonal action of `a : H →L[ℂ] H` on
  `PiLp 2 (fun _ : ι => H)`.
* `ContinuousLinearMap.diagOpStarAlgHom`: the induced `⋆`-algebra morphism.
* `ContinuousLinearMap.diagOpSingle`: injection into a single coordinate.
* `ContinuousLinearMap.diagOpEntry`: extraction of an `(i,j)` entry operator.

## Tags

diagonal operator, direct sum, Hilbert space, PiLp
-/

@[expose] public section

open scoped InnerProductSpace

universe u v

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type v} [Fintype ι]

noncomputable section

/-- The endomorphism space of `PiLp 2 (fun _ : ι => H)` has its canonical `ℂ`-algebra structure. -/
noncomputable instance instAlgebraPiLpEnd :
    Algebra ℂ (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
  (ContinuousLinearMap.toNormedAlgebra (𝕜 := ℂ) (E := PiLp 2 (fun _ : ι => H))).toAlgebra

/-- Diagonal operator on a finite `PiLp 2` direct sum. -/
noncomputable def diagOp (a : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  let e : (PiLp 2 (fun _ : ι => H)) ≃L[ℂ] ((i : ι) → H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  e.symm ∘L (piMap fun _ : ι => a) ∘L e

/-- Coordinatewise formula for `diagOp`. -/
@[simp] theorem diagOp_apply (a : H →L[ℂ] H) (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (diagOp a x) i = a (x i) := by
  simp [diagOp]

/-- Multiplicativity of `diagOp`. -/
@[simp] theorem diagOp_mul (a b : H →L[ℂ] H) : diagOp (ι := ι) (a * b) = diagOp a * diagOp b := by
  ext x i
  simp [ContinuousLinearMap.mul_def]

/-- Unitality of `diagOp`. -/
@[simp] theorem diagOp_one : diagOp (ι := ι) (1 : H →L[ℂ] H) = 1 := by
  ext x i
  simp

/-- Projection commutes with diagonal action. -/
@[simp] theorem proj_comp_diagOp (a : H →L[ℂ] H) (i : ι) :
    (PiLp.proj 2 (fun _ : ι => H) i) ∘L diagOp a = a ∘L (PiLp.proj 2 (fun _ : ι => H) i) := by
  ext x
  simp [diagOp_apply]

/-! ### Compatibility with adjoints -/

section CompleteSpace

variable [CompleteSpace H]

/-- Compatibility of `diagOp` with adjoints. -/
@[simp] theorem diagOp_star (a : H →L[ℂ] H) : diagOp (ι := ι) (star a) = star (diagOp a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [diagOp_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using (ContinuousLinearMap.adjoint_inner_left (A := a) (x := y i) (y := x i))

/-- The canonical star-algebra morphism sending an operator to its diagonal action on a finite
`PiLp 2` direct sum. -/
noncomputable def diagOpStarAlgHom :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) := by
  exact
    { toFun := diagOp (ι := ι)
      map_one' := diagOp_one (H := H) (ι := ι)
      map_mul' _ _ := diagOp_mul (H := H) (ι := ι) _ _
      map_zero' := by
        ext x i
        simp [diagOp_apply]
      map_add' _ _ := by
        ext x i
        simp [diagOp_apply]
      commutes' z := by
        ext x i
        change z • (x i) = (z • x) i
        simp
      map_star' _ := diagOp_star (H := H) (ι := ι) _ }

end CompleteSpace

/-! ### Coordinate injections and matrix entries -/

section DecidableEq

variable [DecidableEq ι]

/-- `diagOpSingle i` injects a vector into coordinate `i` of a finite `PiLp 2` direct sum. -/
noncomputable def diagOpSingle (i : ι) : H →L[ℂ] PiLp 2 (fun _ : ι => H) := by
  let e : (PiLp 2 (fun _ : ι => H)) ≃L[ℂ] ((j : ι) → H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  exact e.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

/-- Formula for coordinates of `diagOpSingle`. -/
@[simp] theorem diagOpSingle_apply (i j : ι) (x : H) :
    (diagOpSingle (H := H) i x) j = if j = i then x else 0 := by
  by_cases hji : j = i
  · subst hji
    simp [diagOpSingle]
  · simp [diagOpSingle, hji]

/-- Decomposition of a vector as sum of coordinate singletons. -/
@[simp] theorem sum_diagOpSingle (x : PiLp 2 (fun _ : ι => H)) :
    (∑ i, diagOpSingle (H := H) i (x i)) = x := by
  ext j
  simp [diagOpSingle_apply]

/-- Coordinate singleton intertwines diagonal action. -/
@[simp] theorem diagOp_comp_single (a : H →L[ℂ] H) (i : ι) :
    diagOp a ∘L diagOpSingle (H := H) i = diagOpSingle (H := H) i ∘L a := by
  ext x j
  by_cases hji : j = i
  · subst hji
    simp [diagOpSingle_apply]
  · simp [diagOpSingle_apply, hji]

/-- The `(i,j)` entry operator extracted from an operator on a finite `PiLp 2` direct sum. -/
noncomputable def diagOpEntry (z : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i) ∘L z ∘L diagOpSingle (H := H) j

/-- Formula for applying an extracted `(i,j)` entry operator. -/
@[simp] theorem diagOpEntry_apply (z : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (i j : ι) (x : H) :
    diagOpEntry (H := H) z i j x = (z (diagOpSingle (H := H) j x)) i := rfl

/-- Coordinate expansion in terms of extracted entries. -/
lemma coord_eq_sum_diagOpEntry (z : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (i : ι) (v : PiLp 2 (fun _ : ι => H)) :
    (z v) i = ∑ j, diagOpEntry (H := H) z i j (v j) := by
  have hzsum : z (∑ j, diagOpSingle (H := H) j (v j)) = z v :=
    congrArg z (sum_diagOpSingle (H := H) (ι := ι) v)
  have hzmap : z (∑ j, diagOpSingle (H := H) j (v j)) =
      ∑ j, z (diagOpSingle (H := H) j (v j)) := by
    simpa using map_sum z (fun j => diagOpSingle (H := H) j (v j)) Finset.univ
  calc
    (z v) i = (z (∑ j, diagOpSingle (H := H) j (v j))) i := by
      exact congrArg (fun w : PiLp 2 (fun _ : ι => H) => w i) hzsum.symm
    _ = (∑ j, z (diagOpSingle (H := H) j (v j))) i := by
      exact congrArg (fun w : PiLp 2 (fun _ : ι => H) => w i) hzmap
    _ = ∑ j, (z (diagOpSingle (H := H) j (v j))) i := by simp
    _ = ∑ j, diagOpEntry (H := H) z i j (v j) := by simp [diagOpEntry]

end DecidableEq

end

end ContinuousLinearMap
