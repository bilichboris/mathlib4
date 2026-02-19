/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `WStarAlgebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `VonNeumannAlgebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/

@[expose] public section


universe u v

open scoped InnerProductSpace

/-- Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `WStarAlgebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WStarAlgebra (M : Type u) [CStarAlgebra M] : Prop where
  /-- There is a Banach space `X` whose dual is isometrically (conjugate-linearly) isomorphic
  to the `WStarAlgebra`. -/
  exists_predual :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X),
      Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

-- TODO: Without this, `VonNeumannAlgebra` times out. Why?
/-- The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `WStarAlgebra` for the abstract notion (a C^*-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `VonNeumannAlgebra`
(although we will later construct the instance `WStarAlgebra (H →L[ℂ] H)`),
and instead will use `⊤ : VonNeumannAlgebra H`.
-/
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends StarSubalgebra ℂ (H →L[ℂ] H) where
  /-- The double commutant (a.k.a. centralizer) of a `VonNeumannAlgebra` is itself. -/
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a *-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

noncomputable section

noncomputable instance instAlgebraPiLpEnd :
    Algebra ℂ (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
  (ContinuousLinearMap.toNormedAlgebra (𝕜 := ℂ) (E := PiLp 2 (fun _ : ι => H))).toAlgebra

/-- Diagonal operator on a finite `PiLp 2` direct sum. -/
noncomputable def diagOp (a : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) := by
  let e : (PiLp 2 (fun _ : ι => H)) ≃L[ℂ] ((i : ι) → H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  exact e.symm.toContinuousLinearMap ∘L ((ContinuousLinearMap.piMap fun _ : ι => a) ∘L
    e.toContinuousLinearMap)

omit [CompleteSpace H] [DecidableEq ι] in
/-- Coordinatewise formula for `diagOp`. -/
@[simp] theorem diagOp_apply (a : H →L[ℂ] H) (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (diagOp a x) i = a (x i) := by
  simp [diagOp]

omit [CompleteSpace H] [DecidableEq ι] in
/-- Multiplicativity of `diagOp`. -/
@[simp] theorem diagOp_mul (a b : H →L[ℂ] H) : diagOp (ι := ι) (a * b) = diagOp a * diagOp b := by
  ext x i
  simp [ContinuousLinearMap.mul_def]

omit [CompleteSpace H] [DecidableEq ι] in
/-- Unitality of `diagOp`. -/
@[simp] theorem diagOp_one : diagOp (ι := ι) (1 : H →L[ℂ] H) = 1 := by
  ext x i
  simp

omit [DecidableEq ι] in
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

/-- `diagOpSingle i` injects a vector into coordinate `i` of a finite `PiLp 2` direct sum. -/
noncomputable def diagOpSingle (i : ι) : H →L[ℂ] PiLp 2 (fun _ : ι => H) := by
  let e : (PiLp 2 (fun _ : ι => H)) ≃L[ℂ] ((j : ι) → H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  exact e.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] in
/-- Formula for coordinates of `diagOpSingle`. -/
@[simp] theorem diagOpSingle_apply (i j : ι) (x : H) :
    (diagOpSingle (H := H) i x) j = if j = i then x else 0 := by
  by_cases hji : j = i
  · subst hji
    simp [diagOpSingle]
  · simp [diagOpSingle, hji]

omit [CompleteSpace H] in
/-- Decomposition of a vector as sum of coordinate singletons. -/
@[simp] theorem sum_diagOpSingle (x : PiLp 2 (fun _ : ι => H)) :
    (∑ i, diagOpSingle (H := H) i (x i)) = x := by
  ext j
  simp [diagOpSingle_apply]

omit [CompleteSpace H] [DecidableEq ι] in
/-- Projection commutes with diagonal action. -/
@[simp] theorem proj_comp_diagOp (a : H →L[ℂ] H) (i : ι) :
    (PiLp.proj 2 (fun _ : ι => H) i) ∘L diagOp a = a ∘L (PiLp.proj 2 (fun _ : ι => H) i) := by
  ext x
  simp [diagOp_apply]

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- Formula for applying an extracted `(i,j)` entry operator. -/
@[simp] theorem diagOpEntry_apply (z : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (i j : ι) (x : H) :
    diagOpEntry (H := H) z i j x = (z (diagOpSingle (H := H) j x)) i := rfl

omit [CompleteSpace H] in
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

end

end ContinuousLinearMap

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance instSetLike : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) where
  coe S := S.carrier
  coe_injective' S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr

instance : PartialOrder (VonNeumannAlgebra H) := .ofSetLike (VonNeumannAlgebra H) (H →L[ℂ] H)

noncomputable instance instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  star_mem {s} := s.star_mem'

instance instSubringClass : SubringClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a ∈ s.toStarSubalgebra from neg_mem ha

@[simp]
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ S.toStarSubalgebra ↔ x ∈ (S : Set (H →L[ℂ] H)) :=
  Iff.rfl

@[simp]
theorem coe_toStarSubalgebra (S : VonNeumannAlgebra H) :
    (S.toStarSubalgebra : Set (H →L[ℂ] H)) = S :=
  rfl

@[simp]
theorem coe_mk (S : StarSubalgebra ℂ (H →L[ℂ] H)) (h) :
    ((⟨S, h⟩ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = S :=
  rfl

@[ext]
theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S :=
  S.centralizer_centralizer'

/-- The centralizer of a `VonNeumannAlgebra`, as a `VonNeumannAlgebra`. -/
noncomputable def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by simp

@[simp]
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H →L[ℂ] H)) := by
  simp [commutant]

@[simp]
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H →L[ℂ] H} :
    z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g := by
  rw [← SetLike.mem_coe, coe_commutant]
  rfl

@[simp]
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective <| by simp

/-- Cyclic subspace closure form of the double-centralizer approximation lemma. -/
theorem doubleCentralizer_apply_mem_closure_image_apply
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (ξ : H) :
    x ξ ∈ closure ((fun a : H →L[ℂ] H => a ξ) '' (S : Set (H →L[ℂ] H))) := by
  let K0 : Submodule ℂ H :=
    S.toSubalgebra.toSubmodule.map (ContinuousLinearMap.apply ℂ H ξ).toLinearMap
  let K : Submodule ℂ H := K0.topologicalClosure
  have hK0 : (K0 : Set H) = ((fun a : H →L[ℂ] H => a ξ) '' (S : Set (H →L[ℂ] H))) := by
    ext v
    constructor
    · intro hv
      rcases Submodule.mem_map.mp hv with ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  have hK_invt : ∀ {a : H →L[ℂ] H}, a ∈ S → K ∈ Module.End.invtSubmodule (a : H →ₗ[ℂ] H) := by
    intro a ha
    have hK0_invt : K0 ∈ Module.End.invtSubmodule (a : H →ₗ[ℂ] H) := by
      rw [Module.End.mem_invtSubmodule]
      intro v hv
      rcases Submodule.mem_map.mp hv with ⟨b, hb, rfl⟩
      refine Submodule.mem_map.mpr ?_
      refine ⟨a * b, S.mul_mem ha hb, ?_⟩
      simp [ContinuousLinearMap.mul_def]
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    have hv' : v ∈ closure (K0 : Set H) := by
      dsimp [K] at hv
      exact hv
    have hle : K0 ≤ Submodule.comap (a : H →ₗ[ℂ] H) K0 :=
      (Module.End.mem_invtSubmodule (a : H →ₗ[ℂ] H)).1 hK0_invt
    have hmaps : Set.MapsTo (fun y : H => a y) (K0 : Set H) (K0 : Set H) := by
      intro y hy
      exact hle hy
    have hav : a v ∈ closure (K0 : Set H) :=
      map_mem_closure a.continuous hv' hmaps
    change a v ∈ K0.topologicalClosure
    exact hav
  have hKorth_invt : ∀ {a : H →L[ℂ] H}, a ∈ S → Kᗮ ∈ Module.End.invtSubmodule (a : H →ₗ[ℂ] H) := by
    intro a ha
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    change a v ∈ Kᗮ
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have hu' : (star a) u ∈ K := hK_invt (star_mem ha) hu
    have hvu : ⟪(star a) u, v⟫_ℂ = 0 := hv ((star a) u) hu'
    have hadj : ⟪(star a) u, v⟫_ℂ = ⟪u, a v⟫_ℂ := by
      simpa [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint_inner_left (A := a) (x := v) (y := u))
    exact hadj.symm.trans hvu
  let p : H →L[ℂ] H := K.starProjection
  have hp_eq : ∀ {a : H →L[ℂ] H}, a ∈ S → p * a = a * p := by
    intro a ha
    have hRange :
        ((p : H →L[ℂ] H).toLinearMap).range ∈ Module.End.invtSubmodule (a : H →ₗ[ℂ] H) := by
      simpa [p, Submodule.range_starProjection] using (hK_invt ha)
    have hKer :
        ((p : H →L[ℂ] H).toLinearMap).ker ∈ Module.End.invtSubmodule (a : H →ₗ[ℂ] H) := by
      simpa [p, Submodule.ker_starProjection] using (hKorth_invt ha)
    have hp_idem_cont : IsIdempotentElem (p : H →L[ℂ] H) :=
      Submodule.isIdempotentElem_starProjection (K := K)
    have hp_idem : IsIdempotentElem ((p : H →L[ℂ] H).toLinearMap) :=
      ContinuousLinearMap.IsIdempotentElem.toLinearMap hp_idem_cont
    have hcomm : Commute ((p : H →L[ℂ] H).toLinearMap) (a : H →ₗ[ℂ] H) :=
      (LinearMap.IsIdempotentElem.commute_iff
        (T := (a : H →ₗ[ℂ] H)) (f := ((p : H →L[ℂ] H).toLinearMap)) hp_idem).2
        ⟨hRange, hKer⟩
    ext v
    simpa [ContinuousLinearMap.mul_def] using congrArg (fun f : H →ₗ[ℂ] H => f v) hcomm.eq
  have hp_mem : p ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro a ha
    simpa [eq_comm] using (hp_eq ha)
  have hpx : p * x = x * p := hx p hp_mem
  have hxK : ∀ v ∈ K, x v ∈ K := by
    intro v hv
    have hpv : p v = v := (Submodule.starProjection_eq_self_iff (K := K)).2 hv
    have hpxv : p (x v) = x v := by
      have h := congrArg (fun f : H →L[ℂ] H => f v) hpx
      simpa [ContinuousLinearMap.mul_def, hpv] using h
    exact (Submodule.starProjection_eq_self_iff (K := K)).1 hpxv
  have hξK0 : ξ ∈ K0 := by
    refine Submodule.mem_map.mpr ?_
    exact ⟨1, S.one_mem, by simp⟩
  have hξK : ξ ∈ K := Submodule.le_topologicalClosure K0 hξK0
  have hxξK : x ξ ∈ K := hxK ξ hξK
  have hxξClosure : x ξ ∈ closure (K0 : Set H) := by
    dsimp [K] at hxξK
    exact hxξK
  rw [hK0] at hxξClosure
  exact hxξClosure

/-- Diagonal lift of a double-centralizer element remains in the corresponding double centralizer
on finite direct sums. -/
lemma diagOp_mem_doubleCentralizer_map {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ContinuousLinearMap.diagOp (H := H) (ι := ι) x ∈ Set.centralizer
      (Set.centralizer
        ((StarSubalgebra.map (ContinuousLinearMap.diagOpStarAlgHom (H := H) (ι := ι)) S :
          Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)))) ) := by
  intro z hz
  have hEntryMem : ∀ i j,
      ContinuousLinearMap.diagOpEntry (H := H) z i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro i j a ha
    have haDiag : ContinuousLinearMap.diagOp (ι := ι) a ∈
        (StarSubalgebra.map (ContinuousLinearMap.diagOpStarAlgHom (H := H) (ι := ι)) S :
          Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) :=
      ⟨a, ha, rfl⟩
    have hza : ContinuousLinearMap.diagOp (ι := ι) a * z =
        z * ContinuousLinearMap.diagOp (ι := ι) a := hz _ haDiag
    ext u
    have hu := congrArg (fun T : (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) =>
      (T (ContinuousLinearMap.diagOpSingle (H := H) j u)) i) hza
    have hs : (ContinuousLinearMap.diagOp (ι := ι) a)
        (ContinuousLinearMap.diagOpSingle (H := H) j u) =
        ContinuousLinearMap.diagOpSingle (H := H) j (a u) := by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [ContinuousLinearMap.diagOp_apply, ContinuousLinearMap.diagOpSingle_apply]
      · simp [ContinuousLinearMap.diagOp_apply, ContinuousLinearMap.diagOpSingle_apply, hk]
    have hu' : a ((z (ContinuousLinearMap.diagOpSingle (H := H) j u)) i) =
        (z (ContinuousLinearMap.diagOpSingle (H := H) j (a u))) i := by
      simpa [ContinuousLinearMap.mul_def, hs] using hu
    simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.diagOpEntry] using hu'
  ext v i
  have hleft :
      (z (ContinuousLinearMap.diagOp (ι := ι) x v)) i =
        ∑ j, ContinuousLinearMap.diagOpEntry (H := H) z i j (x (v j)) := by
    simpa [ContinuousLinearMap.diagOp_apply] using
      (ContinuousLinearMap.coord_eq_sum_diagOpEntry (H := H) z i
        (ContinuousLinearMap.diagOp (ι := ι) x v))
  have hright :
      (ContinuousLinearMap.diagOp (ι := ι) x (z v)) i =
        ∑ j, ContinuousLinearMap.diagOpEntry (H := H) z i j (x (v j)) := by
    calc
      (ContinuousLinearMap.diagOp (ι := ι) x (z v)) i = x ((z v) i) := by
        simp [ContinuousLinearMap.diagOp_apply]
      _ = x (∑ j, ContinuousLinearMap.diagOpEntry (H := H) z i j (v j)) := by
        rw [ContinuousLinearMap.coord_eq_sum_diagOpEntry (H := H) z i v]
      _ = ∑ j, x (ContinuousLinearMap.diagOpEntry (H := H) z i j (v j)) := by simp
      _ = ∑ j, ContinuousLinearMap.diagOpEntry (H := H) z i j (x (v j)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        have hcomm : ContinuousLinearMap.diagOpEntry (H := H) z i j * x =
            x * ContinuousLinearMap.diagOpEntry (H := H) z i j := hx _ (hEntryMem i j)
        have hcommv := congrArg (fun T : H →L[ℂ] H => T (v j)) hcomm
        simpa [ContinuousLinearMap.mul_def] using hcommv.symm
  simp [ContinuousLinearMap.mul_def, hleft, hright]

/-- Finite-family closure approximation obtained from the matrix trick on finite direct sums. -/
theorem doubleCentralizer_finite_family_mem_closure_image_apply {ι : Type v} [Fintype ι]
    [DecidableEq ι] (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (ξ : PiLp 2 (fun _ : ι => H)) :
    ContinuousLinearMap.diagOp (H := H) (ι := ι) x ξ ∈
      closure ((fun a : H →L[ℂ] H =>
        ContinuousLinearMap.diagOp (H := H) (ι := ι) a ξ) '' (S : Set (H →L[ℂ] H))) := by
  let Sdiag : StarSubalgebra ℂ (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
    StarSubalgebra.map (ContinuousLinearMap.diagOpStarAlgHom (H := H) (ι := ι)) S
  have hxdiag : ContinuousLinearMap.diagOp (H := H) (ι := ι) x ∈
      Set.centralizer (Set.centralizer (Sdiag : Set
        (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)))) :=
    diagOp_mem_doubleCentralizer_map (H := H) (ι := ι) S hx
  have hcyc := doubleCentralizer_apply_mem_closure_image_apply
    (H := PiLp 2 (fun _ : ι => H)) (S := Sdiag)
    (x := ContinuousLinearMap.diagOp (H := H) (ι := ι) x) hxdiag ξ
  have hset :
      ((fun a : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) => a ξ) '' (Sdiag : Set
        (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)))) =
      ((fun a : H →L[ℂ] H => ContinuousLinearMap.diagOp (H := H) (ι := ι) a ξ) '' (S : Set
        (H →L[ℂ] H))) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases ha with ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ContinuousLinearMap.diagOp (H := H) (ι := ι) a, ⟨a, ha, rfl⟩, rfl⟩
  simpa [hset] using hcyc

/-- WOT closure membership for a double-centralizer element. -/
theorem doubleCentralizer_mem_closure_image_toWOT
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H x) ∈
      closure ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) := by
  classical
  let toWOT : (H →L[ℂ] H) → (H →WOT[ℂ] H) := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  let p : SeminormFamily ℂ (H →WOT[ℂ] H) (H × StrongDual ℂ H) :=
    ContinuousLinearMapWOT.seminormFamily (RingHom.id ℂ) H H
  have hp : WithSeminorms p :=
    ContinuousLinearMapWOT.withSeminorms (σ := RingHom.id ℂ) (E := H) (F := H)
  refine mem_closure_iff.2 ?_
  intro U hUopen hxU
  have hUnhds : U ∈ nhds (toWOT x) := hUopen.mem_nhds hxU
  rcases (WithSeminorms.mem_nhds_iff hp (toWOT x) U).1 hUnhds with ⟨s, r, hr, hsub⟩
  let M : NNReal := s.sup (fun q : H × StrongDual ℂ H => ‖q.2‖₊)
  let C : ℝ := (M : ℝ) + 1
  have hCpos : 0 < C := by
    have hMnonneg : 0 ≤ (M : ℝ) := by
      exact_mod_cast (show (0 : NNReal) ≤ M from bot_le)
    dsimp [C]
    linarith
  let ε : ℝ := r / C
  have hε : 0 < ε := by exact div_pos hr hCpos
  let ξs : PiLp 2 (fun _ : s => H) := WithLp.toLp 2 (fun q : s => q.1.1)
  letI : DecidableEq s := Classical.decEq s
  have hclosePi :
      ContinuousLinearMap.diagOp (H := H) (ι := s) x ξs ∈
        closure ((fun a : H →L[ℂ] H =>
          ContinuousLinearMap.diagOp (H := H) (ι := s) a ξs) '' (S : Set (H →L[ℂ] H))) :=
    doubleCentralizer_finite_family_mem_closure_image_apply (H := H) (ι := s) S hx ξs
  rcases Metric.mem_closure_iff.1 hclosePi ε hε with ⟨w, hw, hdist⟩
  rcases hw with ⟨a, ha, rfl⟩
  have hsball :
      toWOT a ∈ (s.sup p).ball (toWOT x) r := by
    rw [Seminorm.ball_finset_sup_eq_iInter _ s _ hr]
    refine Set.mem_iInter₂.2 ?_
    intro q hq
    let qs : s := ⟨q, hq⟩
    have hcoord : dist (x q.1) (a q.1) < ε := by
      have hle := PiLp.dist_apply_le
        (x := ContinuousLinearMap.diagOp (H := H) (ι := s) x ξs)
        (y := ContinuousLinearMap.diagOp (H := H) (ι := s) a ξs) qs
      have hcoord' : dist ((ContinuousLinearMap.diagOp (H := H) (ι := s) x ξs) qs)
          ((ContinuousLinearMap.diagOp (H := H) (ι := s) a ξs) qs) < ε := by
        exact lt_of_le_of_lt hle hdist
      simpa [ξs, ContinuousLinearMap.diagOp_apply, PiLp.toLp_apply] using hcoord'
    have hvec : ‖(a - x) q.1‖ < ε := by
      simpa [dist_eq_norm, ContinuousLinearMap.sub_apply, norm_sub_rev] using hcoord
    have hnorm_le_C : ‖q.2‖ ≤ C := by
      have hnn : ‖q.2‖₊ ≤ M := by
        dsimp [M]
        exact Finset.le_sup (f := fun z : H × StrongDual ℂ H => ‖z.2‖₊) hq
      have hreal : ‖q.2‖ ≤ (M : ℝ) := by
        exact_mod_cast hnn
      dsimp [C]
      linarith
    have hleop : ‖q.2 ((a - x) q.1)‖ ≤ ‖q.2‖ * ‖(a - x) q.1‖ := by
      simpa using (q.2.le_opNorm ((a - x) q.1))
    have hCε : C * ε = r := by
      have hCne : C ≠ 0 := by exact ne_of_gt hCpos
      dsimp [ε]
      field_simp [hCne]
    have hlt_r : ‖q.2 ((a - x) q.1)‖ < r := by
      by_cases hy0 : ‖q.2‖ = 0
      · have hq0 : q.2 = 0 := by simpa using hy0
        simpa [hq0] using hr
      · have hypos : 0 < ‖q.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
        have hmul_lt : ‖q.2‖ * ‖(a - x) q.1‖ < ‖q.2‖ * ε := by
          nlinarith [hypos, hvec]
        have hmul_le : ‖q.2‖ * ε ≤ C * ε :=
          mul_le_mul_of_nonneg_right hnorm_le_C (le_of_lt hε)
        have hlt_Cε : ‖q.2‖ * ‖(a - x) q.1‖ < C * ε := lt_of_lt_of_le hmul_lt hmul_le
        exact lt_of_le_of_lt hleop (hCε ▸ hlt_Cε)
    rw [Seminorm.mem_ball]
    change ‖q.2 (((toWOT a - toWOT x) q.1))‖ < r
    simpa [toWOT, ContinuousLinearMap.toWOT_apply, ContinuousLinearMapWOT.sub_apply,
      ContinuousLinearMap.sub_apply] using hlt_r
  refine ⟨toWOT a, hsub hsball, ?_⟩
  exact ⟨a, ha, rfl⟩

/-- Von Neumann's double commutant theorem:
a `*`-subalgebra of bounded operators is equal to its double commutant
if and only if it is weak-operator-topology closed. -/
theorem double_commutant_iff_isClosed_image_toWOT
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) ↔
      IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) := by
  constructor
  · intro hS
    simpa [hS] using
      (ContinuousLinearMap.isClosed_image_toWOT_centralizer
        (T := Set.centralizer (S : Set (H →L[ℂ] H))))
  · intro hClosed
    apply Set.Subset.antisymm
    · intro x hx
      have hxclosure := doubleCentralizer_mem_closure_image_toWOT (H := H) S hx
      have hximage : (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H x) ∈
          (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H)) := by
        simpa [hClosed.closure_eq] using hxclosure
      rcases hximage with ⟨a, ha, hax⟩
      have hax' : a = x := (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).injective hax
      have hxa : x = a := hax'.symm
      simpa [hxa] using ha
    · simpa using (Set.subset_centralizer_centralizer (S := (S : Set (H →L[ℂ] H))))

open ContinuousLinearMap in
/-- An idempotent is an element in a von Neumann algebra if and only if
its range and kernel are invariant under the commutant. -/
theorem IsIdempotentElem.mem_iff {e : H →L[ℂ] H} (h : IsIdempotentElem e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant,
      e.range ∈ Module.End.invtSubmodule y ∧ e.ker ∈ Module.End.invtSubmodule y := by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

open VonNeumannAlgebra ContinuousLinearMap in
/-- A star projection is an element in a von Neumann algebra if and only if
its range is invariant under the commutant. -/
theorem IsStarProjection.mem_iff {e : H →L[ℂ] H} (he : IsStarProjection e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant, e.range ∈ Module.End.invtSubmodule y := by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using congr(star $(h _ (star_mem hx)))

end VonNeumannAlgebra
