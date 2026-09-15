/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremF
import Amenability.TheoremH
import Amenability.TheoremI
import Amenability.TheoremJ
import Palomar.Proofs

open Coalgebra Module

namespace HopfAmenability
noncomputable section
universe u v w
variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- Rounding preserves or improves the expansion ratio dim(E + F E) / dim(E).
The acting space F is a finite subcoalgebra; E is any nonzero finite subspace.
The target coalgebra M need not be cocommutative. -/
theorem palomar_rounding
    (F : FiniteSubcoalgebra k H) (E : Submodule k M)
    [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M, C.carrier ≠ ⊥ ∧
      (sfinrank k (actionExpansion F.carrier C.carrier) : ℚ) /
          (finrank k C.carrier : ℚ) ≤
        (sfinrank k (actionExpansion F.carrier E) : ℚ) /
          (finrank k E : ℚ) :=
  exists_finiteSubcoalgebra_expansion_ratio_le F E hE

/-- Theorem A: Følner subcoalgebras exist exactly when Følner subspaces exist.
Both conditions quantify over every finite-dimensional acting subspace and
positive rational tolerance, and require a nonzero witness. -/
theorem palomar_amenability :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) ↔
      HasActionFolnerSubspaces (k := k) (H := H) (M := M) :=
  isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces

end
end HopfAmenability


namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v w
/-- The finite-dimensional Følner condition for an explicitly given bilinear action.
The expansion is E plus the span of all a • e with a in F and e in E. -/
def Folner {k : Type u} {A : Type v} {M : Type w}
    [Field k] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M]
    (act : A →ₗ[k] M →ₗ[k] M) : Prop :=
  ∀ F : Submodule k A, FiniteDimensional k F → ∀ ε : ℚ, 0 < ε →
    ∃ E : Submodule k M, E ≠ ⊥ ∧ FiniteDimensional k E ∧
      (sfinrank k (E ⊔ Submodule.map₂ act F E) : ℚ) ≤
        (1 + ε) * finrank k E

/-- Algebraic amenability of U(L), equivalent by the proved Lie generator test
to the manuscript's coalgebraic definition of amenability of L. -/
def LieAmenable (k : Type u) (L : Type v)
    [Field k] [LieRing L] [LieAlgebra k L] : Prop :=
  Folner (Algebra.lsmul k k (UniversalEnvelopingAlgebra k L) :
    UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k (UniversalEnvelopingAlgebra k L)).toLinearMap

/-- Finite-set Følner amenability for a group action, including the identity
in the acting set so that the expansion includes A itself. -/
def GroupActionAmenable (G : Type v) (X : Type w)
    [Group G] [MulAction G X] : Prop := by
  classical
  exact ∀ S : Finset G, ∀ ε : ℚ, 0 < ε → ∃ A : Finset X,
    A.Nonempty ∧
      (((insert 1 S).product A |>.image (fun p => p.1 • p.2)).card : ℚ) ≤
        (1 + ε) * A.card
end
end Palomar

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v w x
section Hopf
variable {k : Type u} [Field k] {H : Type v}
variable [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- B: equivariant surjective coalgebra images of amenable module coalgebras
are amenable. Both source and target carry compatible H-actions. -/
theorem theoremB {M : Type w} {Q : Type x}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [AddCommGroup Q] [Module k Q] [Module H Q] [IsScalarTower k H Q]
    [Coalgebra k Q] [IsHopfModuleCoalgebra k H Q]
    (q : M →ₗc[k] Q) (heq : ∀ (h : H) (m : M), q (h • m) = h • q m)
    (hsurj : Function.Surjective q)
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := Q) :=
  by
    exact hM.of_surjective_coalgHom q heq hsurj

/-- C: H is amenable iff every nonzero H-module coalgebra is amenable.
The equivalence quantifies over carriers in H's universe; the next declaration
also states the forward implication for an arbitrary carrier universe. -/
theorem theoremC : IsAmenableHopfAlgebra (k := k) (H := H) ↔
    ∀ (N : Type v) [AddCommGroup N] [Module k N] [Module H N]
      [IsScalarTower k H N] [Coalgebra k N]
      [IsHopfModuleCoalgebra k H N] [Nontrivial N],
      IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := N) :=
  isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras

/-- C, forward implication without a common-universe restriction. -/
theorem theoremC_module {M : Type w}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M] [Nontrivial M]
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) :=
  isAmenable_moduleCoalgebra_of_isAmenableHopfAlgebra hH

/-- D, conditional on the unformalized Takeuchi–Wigner input: H is projective
as a K-module by restriction along the displayed Hopf embedding. -/
theorem theoremD {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hprojective : letI := Module.compHom H i.toAlgHom.toRingHom; Module.Projective K H)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfAlgebra (k := k) (H := K) :=
  palomar_hopf_descent i hprojective hH
end Hopf

section Cleft
variable {k : Type u} [Field k] {A : Type v} {B : Type w} {C : Type x}
variable [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
variable [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
variable [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C]

/-- E: cleft extensions of amenable Hopf algebras are amenable. The displayed
sequence includes a unital coalgebra section and the coinvariant identity. -/
theorem theoremE_extension (e : CleftExactSequence (k := k) A B C)
    (hA : IsAmenableHopfAlgebra (k := k) (H := A))
    (hC : IsAmenableHopfAlgebra (k := k) (H := C)) :
    IsAmenableHopfAlgebra (k := k) (H := B) :=
  isAmenableHopfAlgebra_cleftExtension_of_components e hA hC

/-- E, equivalence form: the reverse subalgebra implication is conditional
on projectivity of B over A, the same literature input as in D. -/
theorem theoremE_iff (e : CleftExactSequence (k := k) A B C)
    (hprojective : letI := Module.compHom B e.inclusion.toAlgHom.toRingHom;
      Module.Projective A B) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) :=
  by
    constructor
    · intro hB
      constructor
      · exact palomar_hopf_descent
          { e.inclusion with injective := e.inclusion_injective } hprojective hB
      · exact e.isAmenableHopfAlgebra_quotient hB
    · rintro ⟨hA, hC⟩
      exact isAmenableHopfAlgebra_cleftExtension_of_components e hA hC
end Cleft
end
end Palomar

namespace Palomar
open HopfAmenability Module
universe u v w
private theorem folner_iff {k : Type u} {H : Type v} {M : Type w}
    [Field k] [Ring H] [HopfAlgebra k H]
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M] :
    Folner (Algebra.lsmul k k M : H →ₐ[k] Module.End k M).toLinearMap ↔
      HasActionFolnerSubspaces (k := k) (H := H) (M := M) := by
  unfold Folner HasActionFolnerSubspaces
  simp_rw [actionExpansion, actionSubspace_eq_map₂]
private theorem lie_iff {k : Type u} {L : Type v}
    [Field k] [LieRing L] [LieAlgebra k L] :
    LieAmenable k L ↔ IsAmenableLieAlgebra (k := k) (L := L) := by
  rw [LieAmenable, folner_iff, isAmenableLieAlgebra_iff_algebraicallyAmenable]
  rfl
end Palomar

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v w x
section Group
variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V]

/-- F: a quotient of a permutation module is amenable when a basis point
has nonzero image and its orbit is amenable. -/
theorem theoremF_permutation {X : Type x} [MulAction G X]
    (q : MonoidAlgebra k X →ₗ[k] V) (hsurj : Function.Surjective q)
    (heq : ∀ (g : G) (x : X), q (MonoidAlgebra.single (g • x) 1) =
      (MonoidAlgebra.single g (1 : k) : MonoidAlgebra k G) •
        q (MonoidAlgebra.single x 1))
    (x : X) (hx : q (MonoidAlgebra.single x 1) ≠ 0)
    (horbit : GroupActionAmenable G (MulAction.orbit G x)) :
    Folner (Algebra.lsmul k k V : MonoidAlgebra k G →ₐ[k] Module.End k V).toLinearMap :=
  by
    apply folner_iff.mpr
    apply hasActionFolnerSubspaces_of_quotient_permutationModule q hsurj heq x hx
    classical
    intro S ε hε
    obtain ⟨A, hA, hbound⟩ := horbit S ε hε
    refine ⟨A, hA, ?_⟩
    convert hbound using 2
    congr 1
    ext y
    simp only [groupSetExpansion, Finset.mem_image]


/-- F: every nonzero module over an amenable group's group algebra is
algebraically amenable, over any field. -/
theorem theoremF (hG : GroupActionAmenable G G) [Nontrivial V] :
    Folner (Algebra.lsmul k k V : MonoidAlgebra k G →ₐ[k] Module.End k V).toLinearMap :=
  by
    apply folner_iff.mpr
    exact hasActionFolnerSubspaces_of_isAmenableGroup hG inferInstance
end Group

section Lie
variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

/-- G: locally subexponential Lie growth implies amenability. -/
theorem theoremG_growth (h : HasLocallySubexponentialGrowth k L) :
    LieAmenable k L :=
  lie_iff.mpr (isAmenableLieAlgebra_of_locallySubexponentialGrowth h)

/-- G: amenability descends along injective Lie homomorphisms.
The proof uses relative PBW and does not require the projectivity hypothesis of D. -/
theorem theoremG_subalgebra {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f) (hQ : LieAmenable k Q) :
    LieAmenable k L :=
  lie_iff.mpr (palomar_lie_descent f hf (lie_iff.mp hQ))

/-- G: Lie quotients of amenable Lie algebras are amenable. -/
theorem theoremG_quotient (I : LieIdeal k L) (hL : LieAmenable k L) :
    LieAmenable k (L ⧸ I) :=
  lie_iff.mpr (isAmenableLieAlgebra_quotient (LieIdeal.quotientMkLieHom I)
    (LieIdeal.quotientMkLieHom_surjective I) (lie_iff.mp hL))

/-- G: a Lie algebra is amenable iff its ideal and quotient are amenable. -/
theorem theoremG_extension (I : LieIdeal k L) :
    LieAmenable k L ↔ LieAmenable k I ∧ LieAmenable k (L ⧸ I) :=
  by
    constructor
    · intro hL
      exact ⟨theoremG_subalgebra (LieSubalgebra.incl (I : LieSubalgebra k L))
        (fun _ _ h => Subtype.ext h) hL, theoremG_quotient I hL⟩
    · rintro ⟨hI, hQ⟩
      exact lie_iff.mpr (isAmenableLieAlgebra_extension_of_components I
        (lie_iff.mp hI) (lie_iff.mp hQ))

/-- G: directed unions of amenable Lie subalgebras are amenable. -/
theorem theoremG_union {ι : Type w} [Nonempty ι]
    (S : ι → LieSubalgebra k L) (hdir : Directed (· ≤ ·) S) (hsup : iSup S = ⊤)
    (hS : ∀ i, LieAmenable k (S i)) : LieAmenable k L :=
  lie_iff.mpr (isAmenableLieAlgebra_directedUnion S hdir hsup
    (fun i => lie_iff.mp (hS i)))
end Lie

section Hierarchy
variable (k : Type u) [Field k]

/-- H: elementary Lie algebras are subexponentially amenable. -/
theorem theoremH_EL_SL (A : LieAlgebraObject.{u, u} k)
    (hA : IsElementaryLieObject.{u, u, u} A) :
    IsSubexponentiallyAmenableLieObject k A :=
  hA.isSubexponentiallyAmenable

/-- H: subexponentially amenable Lie algebras are amenable. -/
theorem theoremH_SL_AL (A : LieAlgebraObject.{u, u} k)
    (hA : IsSubexponentiallyAmenableLieObject k A) : LieAmenable k A.Carrier :=
  lie_iff.mpr hA.isAmenable

/-- H: in characteristic zero the inclusion EL ⊆ SL is strict, witnessed
in the proof by the Witt algebra. No literature input is assumed here. -/
theorem theoremH_charZero [CharZero k] :
    ∃ A : LieAlgebraObject.{u, u} k,
      IsSubexponentiallyAmenableLieObject k A ∧ ¬ IsElementaryLieObject.{u, u, u} A :=
  elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras k

/-- H over an arbitrary field, conditional on the positive-characteristic
PSZ construction. The explicit input supplies a finitely generated algebra
of subexponential growth outside EL in each prime characteristic. -/
theorem theoremH
    (hPSZ : ∀ p : ℕ, ∀ (_ : Fact p.Prime) (_ : CharP k p),
      ∃ A : LieAlgebraObject.{u, u} k,
        HasSubexponentialLieGrowth k A.Carrier ∧ ¬ IsElementaryLieObject.{u, u, u} A) :
    ∃ A : LieAlgebraObject.{u, u} k,
      IsSubexponentiallyAmenableLieObject k A ∧ ¬ IsElementaryLieObject.{u, u, u} A :=
  by
    let p := ringChar k
    let : CharP k p := ringChar.charP k
    rcases CharP.char_is_prime_or_zero k p with hp | hp
    · obtain ⟨A, hA, hn⟩ := hPSZ p ⟨hp⟩ inferInstance
      exact ⟨A, IsSubexponentiallyAmenableLieObject.subexponential A hA, hn⟩
    · let : CharP k 0 := CharP.congr p hp
      let : CharZero k := CharP.charP_to_charZero k
      exact theoremH_charZero k

/-- I: an amenable finitely generated Lie algebra of exponential growth,
with locally finite-dimensional ideal and split one-dimensional quotient. -/
theorem theoremI : ∃ A : LieAlgebraObject.{u, u} k, ∃ K : LieIdeal k A.Carrier,
    IsFinitelyGeneratedLieAlgebra (k := k) A.Carrier ∧
    HasExponentialLieGrowth k A.Carrier ∧
    IsLocallyFiniteDimensionalLieAlgebra k K ∧
    FiniteDimensional k (A.Carrier ⧸ K) ∧ Module.finrank k (A.Carrier ⧸ K) = 1 ∧
    LieAmenable k A.Carrier ∧
    ∃ e : k ≃ₗ[k] (A.Carrier ⧸ K), ∃ s : k →ₗ[k] A.Carrier,
      (∀ x y, ⁅s x, s y⁆ = 0) ∧ (∀ r, K.toSubmodule.mkQ (s r) = e r) :=
  by
    obtain ⟨e⟩ := exists_amenable_exponentialGrowth_locallyFiniteByOne k
    exact ⟨e.L, e.K, e.finitelyGenerated, e.exponentialGrowth, e.locallyFiniteKernel,
      e.quotientFiniteDimensional, e.quotientFinrank, lie_iff.mpr e.amenable,
      e.quotientEquiv, e.splitting, e.splitting_lie, e.quotient_splitting⟩
end Hierarchy
end
end Palomar

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v w
/-- The degree-n symbol W_n → direct sum of W_i/W_(i + 1), for a descending
filtration W. All quotients and the direct sum use their canonical k-modules. -/
def symbol {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (n : ℕ) :
    W n →ₗ[k] DirectSum ℕ (fun i => W i ⧸ (W (i + 1)).comap (W i).subtype) :=
  (DirectSum.lof k ℕ _ n).comp ((W (n + 1)).comap (W n).subtype).mkQ
end
end Palomar

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v
variable {k : Type u} {H M : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
local notation "W" => augmentationModuleFiltration (k := k) (H := H) (M := M)
private theorem graded_comul_decomposition (n : ℕ) (m : W n)
    (z : (i : Fin (n + 1)) → W i ⊗[k] W (n - i))
    (hz : Coalgebra.comul (R := k) (A := M) m =
      ∑ i : Fin (n + 1), TensorProduct.mapIncl (W i) (W (n - i)) (z i)) :
    augmentationGradedComul (k := k) (H := H) (M := M) (symbol W n m) =
      ∑ i : Fin (n + 1), TensorProduct.map (symbol W i) (symbol W (n - i)) (z i) := by
  let lift (i : Fin (n + 1)) : W i ⊗[k] W (n - i) →ₗ[k] tensorFiltration W n :=
    (TensorProduct.mapIncl (W i) (W (n - i))).codRestrict _
      (fun z => (le_iSup (fun j : Fin (n + 1) =>
        LinearMap.range (TensorProduct.mapIncl (W j) (W (n-j)))) i) ⟨z, rfl⟩)
  let T := (gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
    (tensorFiltrationCoordinates (k := k) W n)
  have hT (i : Fin (n + 1)) (a : W i ⊗[k] W (n - i)) :
      T (lift i a) = TensorProduct.map (symbol W i) (symbol W (n - i)) a := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      change gradedTensorInclusion (k := k) (H := H) (M := M) n
        (tensorFiltrationCoordinates W n
          ⟨TensorProduct.mapIncl (W i) (W (n - i)) (a ⊗ₜ[k] b), _⟩) = _
      rw [tensorFiltrationCoordinates_mapIncl_tmul W
        (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M))]
      rw [gradedTensorInclusion_of_tmul]
      rfl
  have heq : (⟨Coalgebra.comul (R := k) (A := M) m,
      augmentationModuleFiltration_comul (k := k) (H := H) (M := M) n m m.property⟩ :
      tensorFiltration W n) = ∑ i, lift i (z i) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hz
  change augmentationGradedComul (k := k) (H := H) (M := M)
    (DirectSum.of _ n (Submodule.Quotient.mk m)) = _
  rw [augmentationGradedComul_of_mk]
  change T ⟨Coalgebra.comul (R := k) (A := M) m, _⟩ = _
  rw [heq, map_sum]
  exact Finset.sum_congr rfl fun i _ => hT i (z i)
end
end Palomar

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v
variable {k : Type u} {H M : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
local notation "W" => augmentationModuleFiltration (k := k) (H := H) (M := M)
local notation "I" => augmentationFiltration (k := k) (H := H)
local notation "GH" => AugmentationGradedHopf (k := k) (H := H)
local notation "GM" => AugmentationGradedModule (k := k) (H := H) (M := M)

/-- Canonical additive group of the direct sum of homogeneous quotients. -/
local instance gradedHopfAddCommGroup : AddCommGroup GH :=
  @DFinsupp.addCommGroup ℕ (fun n => I n ⧸ (I (n + 1)).comap (I n).subtype)
    (fun _ => inferInstance)

/-- J: the augmentation-associated graded of an amenable module coalgebra is
amenable. The existential action and coalgebra are specified on all homogeneous
representatives: [h] acts on [m] by [h • m], counit is zero in positive degrees,
and coproduct is induced by every total-degree decomposition of the original
coproduct. Thus the witnesses are subcoalgebras for the canonical graded
coproduct, not an arbitrary coalgebra structure. The statement includes the
construction of these operations; no realization or amenability data is assumed. -/
theorem theoremJ (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    ∃ act : GH →ₗ[k] GM →ₗ[k] GM, ∃ co : Coalgebra k GM,
      (∀ i j (h : I i) (m : W j), ∃ hm : (h : H) • (m : M) ∈ W (i + j),
        act (symbol I i h) (symbol W j m) = symbol W (i + j) ⟨(h : H) • (m : M), hm⟩) ∧
      (∀ n (m : W n), co.counit (symbol W n m) =
        if n = 0 then Coalgebra.counit (R := k) (A := M) m else 0) ∧
      (∀ n (m : W n) (z : (i : Fin (n + 1)) → W i ⊗[k] W (n - i)),
        Coalgebra.comul (R := k) (A := M) m =
          ∑ i : Fin (n + 1), TensorProduct.mapIncl (W i) (W (n - i)) (z i) →
        co.comul (symbol W n m) =
          ∑ i : Fin (n + 1), TensorProduct.map (symbol W i) (symbol W (n - i)) (z i)) ∧
      (letI := co;
        ∀ F : Submodule k GH, FiniteDimensional k F → ∀ ε : ℚ, 0 < ε →
          ∃ C : FiniteSubcoalgebra k GM, C.carrier ≠ ⊥ ∧
            (sfinrank k (C.carrier ⊔ Submodule.map₂ act F C.carrier) : ℚ) ≤
              (1 + ε) * finrank k C.carrier) :=
  by
    let act : GH →ₗ[k] GM →ₗ[k] GM :=
      (Algebra.lsmul k k GM : GH →ₐ[k] Module.End k GM).toLinearMap
    refine ⟨act, inferInstance, ?_, ?_, ?_, ?_⟩
    · intro i j h m
      refine ⟨augmentationFiltration_action_le (k := k) i j
        (product_mem_actionSubspace h.property m.property), ?_⟩
      change (DirectSum.of (fun n => AugmentationGradedHopfPiece (k := k) (H := H) n)
        i (Submodule.Quotient.mk h)) •
        (DirectSum.of (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n)
          j (Submodule.Quotient.mk m)) =
        DirectSum.of (fun n => AugmentationGradedModulePiece (k := k) (H := H) (M := M) n)
          (i + j) (Submodule.Quotient.mk _)
      rw [DirectSum.Gmodule.of_smul_of]
      rfl
    · intro n m
      change augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ n (Submodule.Quotient.mk m)) = _
      split_ifs with hn
      · exact augmentationGradedCounit_of_eq_zero hn m
      · exact augmentationGradedCounit_of_ne_zero n hn _
    · intro n m z hz
      exact graded_comul_decomposition n m z hz
    · intro F hF ε hε
      obtain ⟨C, hC, hratio⟩ := hM.associatedGraded F hF ε hε
      refine ⟨C, hC, ?_⟩
      rw [actionExpansion, actionSubspace_eq_map₂] at hratio
      exact hratio
end
end Palomar
