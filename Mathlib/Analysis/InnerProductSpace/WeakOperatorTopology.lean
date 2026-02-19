/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Algebra.Group.Center

/-!
# The weak operator topology in Hilbert spaces

This file gives a few properties of the weak operator topology that are specific to operators on
Hilbert spaces. This mostly involves using the Fréchet-Riesz representation to convert between
applications of elements of the dual and inner products with vectors in the space.
-/

public section

open scoped Topology InnerProductSpace

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[ext]
lemma ext_inner {A B : E →WOT[𝕜] F} (h : ∀ x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) : A = B := by
  rw [ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a) x⟫` tends to `⟪y, A x⟫` along the same filter. -/
lemma tendsto_iff_forall_inner_apply_tendsto [CompleteSpace F] {α : Type*} {l : Filter α}
    {f : α → E →WOT[𝕜] F} {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜) := by
  simp_rw [tendsto_iff_forall_dual_apply_tendsto]
  exact .symm <| forall_congr' fun _ ↦
    Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ ↦ Iff.rfl

lemma le_nhds_iff_forall_inner_apply_le_nhds [CompleteSpace F] {l : Filter (E →WOT[𝕜] F)}
    {A : E →WOT[𝕜] F} : l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫_𝕜) ≤ 𝓝 (⟪y, A x⟫_𝕜) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)

end ContinuousLinearMapWOT

namespace ContinuousLinearMap

variable {𝕜 : Type*} {H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- For any set `T` of endomorphisms, its centralizer is weak-operator closed. -/
theorem isClosed_image_toWOT_centralizer (T : Set (H →L[𝕜] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id 𝕜) H H) '' Set.centralizer T) := by
  classical
  let toWOTEquiv : (H →L[𝕜] H) ≃ₗ[𝕜] (H →WOT[𝕜] H) :=
    ContinuousLinearMap.toWOT (RingHom.id 𝕜) H H
  let leftCompWOT (z : H →L[𝕜] H) : (H →WOT[𝕜] H) → (H →WOT[𝕜] H) :=
    fun A => toWOTEquiv (z.comp (toWOTEquiv.symm A))
  let rightCompWOT (z : H →L[𝕜] H) : (H →WOT[𝕜] H) → (H →WOT[𝕜] H) :=
    fun A => toWOTEquiv ((toWOTEquiv.symm A).comp z)
  have hcont_left : ∀ z : H →L[𝕜] H, Continuous (leftCompWOT z) := by
    intro z
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    simpa [leftCompWOT, toWOTEquiv, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id 𝕜) (x := x) (y := y.comp z))
  have hcont_right : ∀ z : H →L[𝕜] H, Continuous (rightCompWOT z) := by
    intro z
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    simpa [rightCompWOT, toWOTEquiv, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id 𝕜) (x := z x) (y := y))
  have hset : (toWOTEquiv '' Set.centralizer T) =
      ⋂ z ∈ T, {A : H →WOT[𝕜] H | leftCompWOT z A = rightCompWOT z A} := by
    ext A
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Set.mem_iInter]
      intro z
      rw [Set.mem_iInter]
      intro hz
      simpa [leftCompWOT, rightCompWOT, toWOTEquiv, ContinuousLinearMap.mul_def] using
        congrArg toWOTEquiv (ha z hz)
    · intro hA
      refine ⟨toWOTEquiv.symm A, ?_, by simp [toWOTEquiv]⟩
      intro z hz
      have hzA : leftCompWOT z A = rightCompWOT z A := by
        exact (Set.mem_iInter.mp (Set.mem_iInter.mp hA z) hz)
      simpa [leftCompWOT, rightCompWOT, toWOTEquiv, ContinuousLinearMap.mul_def] using
        congrArg toWOTEquiv.symm hzA
  have hclosed : IsClosed (toWOTEquiv '' Set.centralizer T) := by
    rw [hset]
    exact isClosed_biInter fun z hz =>
      isClosed_eq (hcont_left z) (hcont_right z)
  simpa [toWOTEquiv] using hclosed

end ContinuousLinearMap
