/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

-- Palomar compiles Challenge directly, without lakefile.toml options. Keep
-- pending instance synthesis identical in both independently compiled files.
set_option maxSynthPendingDepth 3

/-!
# Amenability of Lie, group and Hopf algebras: Theorems A–J

Independent statements for Laurent Bartholdi's arXiv:2609.10373v1.
A gives sharp coalgebraic rounding and equivalence of the two Følner conditions.
B–E give Hopf-module quotients, the all-module characterization, subalgebra
permanence and cleft extensions. F concerns permutation modules and amenable
groups. G gives Lie growth and permanence. H gives EL ⊆ SL ⊆ AL and strictness
of EL ⊆ SL. I constructs an amenable Lie algebra of exponential growth with
a locally finite-dimensional ideal and split one-dimensional quotient.
J constructs the canonical graded action and coalgebra and proves amenability.

D and the reverse implication of E explicitly assume the unformalized
Takeuchi–Masuoka–Wigner projectivity input. The arbitrary-characteristic H
explicitly assumes the positive-characteristic PSZ construction; its
characteristic-zero version and both hierarchy inclusions are unconditional.
No compared Solution declaration uses these inputs as axioms or proof holes.

All mathematical definitions appear here or in Mathlib. The common library
names below have the same definitions in Solution's imports. Palomar.LieAmenable
uses the algebraic Følner condition on U(L), proved equivalent to the manuscript
Lie-subcoalgebra definition in Amenability.LieGeneratorTest. Rational tolerances
are used throughout. The C equivalence uses one carrier universe, supplemented
by a forward statement for arbitrary carrier universes. J is specified through
homogeneous representatives, without importing the proof's graded structures.

See docs/PALOMAR.md for the complete statement-to-proof map and disclosures.
-/

open Coalgebra Module TensorProduct
namespace HopfAmenability
noncomputable section
universe u v w

/-- The finrank of a submodule, with the scalar field explicit and the
ambient module inferred from the submodule argument. -/
noncomputable abbrev sfinrank
    (k : Type*) {V : Type*} [DivisionRing k]
    [AddCommGroup V] [Module k V]
    (P : Submodule k V) : ℕ :=
  Module.finrank k P

section Subcoalgebras
variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

/-- Comultiplication carries C into the image of C tensor C. The counit
restricts automatically because its codomain is the base field. -/
def IsSubcoalgebra (C : Submodule k H) : Prop :=
  ∀ ⦃x : H⦄, x ∈ C →
    Coalgebra.comul (R := k) x ∈
      LinearMap.range (TensorProduct.mapIncl C C)

/-- A finite-dimensional subspace closed under comultiplication. -/
structure FiniteSubcoalgebra (k : Type u) (H : Type v)
    [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H] where
  carrier : Submodule k H
  isSubcoalgebra : IsSubcoalgebra (k := k) carrier
  finiteDimensional : FiniteDimensional k carrier

instance (C : FiniteSubcoalgebra k H) : FiniteDimensional k C.carrier :=
  C.finiteDimensional
end Subcoalgebras

section Action
variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- The linear map h tensor m maps to h acting on m. -/
def hopfModuleAction : H ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (Algebra.lsmul k k M).toLinearMap

/-- The action is a coalgebra morphism: it preserves counit and coproduct. -/
class IsHopfModuleCoalgebra
    (k : Type u) (H : Type v) (M : Type w)
    [Field k] [Ring H] [HopfAlgebra k H]
    [AddCommGroup M] [Module k M]
    [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] : Prop where
  counit_action :
    Coalgebra.counit (R := k) (A := M) ∘ₗ hopfModuleAction =
      Coalgebra.counit (R := k) (A := H ⊗[k] M)
  comul_action :
    Coalgebra.comul (R := k) (A := M) ∘ₗ hopfModuleAction =
      TensorProduct.map hopfModuleAction hopfModuleAction ∘ₗ
        Coalgebra.comul (R := k) (A := H ⊗[k] M)

/-- The action restricted to F tensor E. -/
def restrictedHopfModuleAction (F : Submodule k H) (E : Submodule k M) :
    F ⊗[k] E →ₗ[k] M :=
  hopfModuleAction.comp (TensorProduct.mapIncl F E)

/-- The span F E of products h acting on m, for h in F and m in E. -/
def actionSubspace (F : Submodule k H) (E : Submodule k M) : Submodule k M :=
  LinearMap.range (restrictedHopfModuleAction F E)

/-- The expansion E + F E. -/
def actionExpansion (F : Submodule k H) (E : Submodule k M) : Submodule k M :=
  E ⊔ actionSubspace F E

/-- Algebraic amenability: arbitrarily invariant nonzero finite subspaces.
Here sfinrank abbreviates Module.finrank on a submodule, used only for finite spaces. -/
def HasActionFolnerSubspaces : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k M, E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k (actionExpansion F E) : ℚ) ≤ (1 + ε) * sfinrank k E

variable [Coalgebra k M]
/-- Coalgebraic amenability: the same condition with finite subcoalgebras. -/
def IsAmenableHopfModuleCoalgebra : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : FiniteSubcoalgebra k M, C.carrier ≠ ⊥ ∧
        (sfinrank k (actionExpansion F C.carrier) : ℚ) ≤
          (1 + ε) * finrank k C.carrier
end Action
end
end HopfAmenability

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
  by sorry

/-- Theorem A: Følner subcoalgebras exist exactly when Følner subspaces exist.
Both conditions quantify over every finite-dimensional acting subspace and
positive rational tolerance, and require a nonzero witness. -/
theorem palomar_amenability :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) ↔
      HasActionFolnerSubspaces (k := k) (H := H) (M := M) :=
  by sorry

end
end HopfAmenability


open Coalgebra Module TensorProduct
namespace HopfAmenability
noncomputable section
universe u v w x
section Hopf
variable {k : Type u} {H : Type v} [Field k] [Ring H] [HopfAlgebra k H]
/-- A morphism of Hopf algebras, bundled from its algebra map and coalgebra
compatibility identities. -/
structure HopfAlgebraHom (K : Type w) [Ring K] [HopfAlgebra k K] where
  toAlgHom : H →ₐ[k] K
  map_counit : (Coalgebra.counit (R := k) (A := K)).comp
      toAlgHom.toLinearMap = Coalgebra.counit (R := k) (A := H)
  map_comul : (TensorProduct.map toAlgHom.toLinearMap toAlgHom.toLinearMap).comp
      (Coalgebra.comul (R := k) (A := H)) =
        (Coalgebra.comul (R := k) (A := K)).comp toAlgHom.toLinearMap

instance {K : Type w} [Ring K] [HopfAlgebra k K] : CoeFun
    (HopfAlgebraHom (k := k) (H := H) K) (fun _ => H → K) :=
  ⟨fun f => f.toAlgHom⟩

/-- Regard a Hopf-algebra morphism as a coalgebra morphism. -/
def HopfAlgebraHom.toCoalgHom {K : Type w} [Ring K] [HopfAlgebra k K]
    (f : HopfAlgebraHom (k := k) (H := H) K) : H →ₗc[k] K where
  toLinearMap := f.toAlgHom.toLinearMap
  counit_comp := f.map_counit
  map_comp_comul := f.map_comul

/-- A Hopf-subalgebra presentation is an injective Hopf morphism. -/
structure HopfSubalgebraEmbedding (K : Type w) [Ring K] [HopfAlgebra k K]
    extends HopfAlgebraHom (k := k) (H := K) H where
  injective : Function.Injective toAlgHom

/-- Amenability of the regular Hopf-module coalgebra. -/
def IsAmenableHopfAlgebra : Prop :=
  IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := H)
end Hopf
variable {k : Type u}
/-- The right coinvariants of a Hopf morphism `B → C`. -/
noncomputable def rightCoinvariants
    {B : Type v} {C : Type w} [Field k]
    [Ring B] [HopfAlgebra k B] [Ring C] [HopfAlgebra k C]
    (p : HopfAlgebraHom (k := k) (H := B) C) : Submodule k B :=
  LinearMap.ker
    ((TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := B)) -
      (TensorProduct.mk k B C).flip 1)

/-- Intrinsic data for a cleft exact sequence. -/
structure CleftExactSequence
    (A : Type v) (B : Type w) (C : Type x) [Field k]
    [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C] where
  inclusion : HopfAlgebraHom (k := k) (H := A) B
  projection : HopfAlgebraHom (k := k) (H := B) C
  inclusion_injective : Function.Injective inclusion
  projection_surjective : Function.Surjective projection
  projection_inclusion : ∀ a,
    projection (inclusion a) = algebraMap k C (Coalgebra.counit (R := k) a)
  coalgebraSection : C →ₗc[k] B
  projection_section : projection.toAlgHom.toLinearMap.comp
      coalgebraSection.toLinearMap = LinearMap.id
  section_one : coalgebraSection 1 = 1
  coinvariants : LinearMap.range inclusion.toAlgHom.toLinearMap =
    rightCoinvariants projection

end
end HopfAmenability
namespace HopfAmenability
noncomputable section
universe u v w
/-- A bundled Lie algebra over `k`.  This small project-local bundle is used
only to state closure constructions whose constituents have different
underlying types. -/
structure LieAlgebraObject (k : Type u) [Field k] where
  Carrier : Type v
  lieRing : LieRing Carrier
  lieAlgebra : LieAlgebra k Carrier

attribute [instance] LieAlgebraObject.lieRing LieAlgebraObject.lieAlgebra

/-- Bundle an already-instanced Lie algebra. -/
def LieAlgebraObject.of (k : Type u) [Field k] (L : Type v)
    [LieRing L] [LieAlgebra k L] :
  LieAlgebraObject k where
  Carrier := L
  lieRing := inferInstance
  lieAlgebra := inferInstance

variable {k : Type u} [Field k]

/-- The Lie algebra carried by a Lie ideal. -/
def LieAlgebraObject.ofIdeal (A : LieAlgebraObject k)
    (I : LieIdeal k A.Carrier) : LieAlgebraObject k :=
  LieAlgebraObject.of k I

/-- The quotient Lie algebra by a Lie ideal. -/
def LieAlgebraObject.quotient (A : LieAlgebraObject k)
    (I : LieIdeal k A.Carrier) : LieAlgebraObject k :=
  LieAlgebraObject.of k (A.Carrier ⧸ I)

/-- The Lie algebra carried by a Lie subalgebra. -/
def LieAlgebraObject.ofSubalgebra (A : LieAlgebraObject k)
    (S : LieSubalgebra k A.Carrier) : LieAlgebraObject k :=
  LieAlgebraObject.of k S

/-- The inductively generated class `EL` from the article.  Trivial
extensions are harmless; the constructors work with an ideal and its
canonical quotient, while directed unions are expressed by a directed
family whose supremum is the whole algebra. -/
inductive IsElementaryLieObject : LieAlgebraObject k → Prop
  | finiteDimensional (A : LieAlgebraObject k)
      (hA : FiniteDimensional k A.Carrier) : IsElementaryLieObject A
  | abelian (A : LieAlgebraObject k) (hA : IsLieAbelian A.Carrier) :
      IsElementaryLieObject A
  | extension (A : LieAlgebraObject k) (I : LieIdeal k A.Carrier)
      (hI : IsElementaryLieObject (A.ofIdeal I))
      (hQ : IsElementaryLieObject (A.quotient I)) :
      IsElementaryLieObject A
  | directedUnion (A : LieAlgebraObject k) (ι : Type v) [Nonempty ι]
      (S : ι → LieSubalgebra k A.Carrier)
      (hdir : Directed (· ≤ ·) S)
      (hsup : @iSup _ _ CompleteLattice.toSupSet S = ⊤)
      (hS : ∀ i, IsElementaryLieObject (A.ofSubalgebra (S i))) :
      IsElementaryLieObject A

/-- An unbundled Lie algebra is elementarily amenable when its bundled
object belongs to the inductively generated elementary class. -/
def IsElementarilyAmenableLieAlgebra (L : Type v)
    [LieRing L] [LieAlgebra k L] : Prop :=
  IsElementaryLieObject.{u, v, v} (LieAlgebraObject.of k L)

/-- Finite generation as a Lie algebra. -/
def IsFinitelyGeneratedLieAlgebra (L : Type v)
    [LieRing L] [LieAlgebra k L] : Prop :=
  ∃ s : Finset L, LieSubalgebra.lieSpan k L (s : Set L) = ⊤

section LieAction
variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
variable {M : Type w} [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
def lieActionBilinear : L →ₗ[k] M →ₗ[k] M :=
  (LieModule.toEnd k L M : L →ₗ[k] Module.End k M)

def lieActionMap (F : Submodule k L) (E : Submodule k M) :
    F ⊗[k] E →ₗ[k] M :=
  TensorProduct.lift
    ((lieActionBilinear (k := k) (L := L) (M := M)).domRestrict₁₂ F E)

/-- Stable surjectivity instance for the identity scalar map. -/
theorem lieActionScalarSurjective : RingHomSurjective (RingHom.id k) :=
  RingHomSurjective.ids

def lieActionSubspace (F : Submodule k L) (E : Submodule k M) :
    Submodule k M :=
  letI : RingHomSurjective (RingHom.id k) := lieActionScalarSurjective
  LinearMap.range (lieActionMap F E)

def lieExpansion (F : Submodule k L) (E : Submodule k M) :
    Submodule k M :=
  E ⊔ lieActionSubspace F E

end LieAction
/-- A natural-valued sequence has subexponential growth if it is bounded by
every rational exponential rate greater than one, up to a positive
multiplicative constant. -/
def IsSubexponentialSequence (a : ℕ → ℕ) : Prop :=
  ∀ q : ℚ, 1 < q →
    ∃ C : ℚ, 0 < C ∧ ∀ n : ℕ, (a n : ℚ) ≤ C * q ^ n

variable (k)
/-- Lie balls generated by a coefficient subspace. -/
def lieGrowthBall {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) : ℕ → Submodule k L
  | 0 => F
  | n + 1 => lieExpansion F (lieGrowthBall F n)

/-- A Lie algebra is locally finite-dimensional if every finite-dimensional
subspace is contained in a finite-dimensional Lie subalgebra. -/
def IsLocallyFiniteDimensionalLieAlgebra
    (L : Type v) [LieRing L] [LieAlgebra k L] : Prop :=
  ∀ P : Submodule k L, FiniteDimensional k P →
    ∃ S : LieSubalgebra k L,
      P ≤ S.toSubmodule ∧ FiniteDimensional k S

/-- Exponential Lie growth with respect to a finite-dimensional generating
subspace. -/
def HasExponentialLieGrowth
    (L : Type v) [LieRing L] [LieAlgebra k L] : Prop :=
  ∃ F : Submodule k L,
    Module.Finite k F ∧
      LieSubalgebra.lieSpan k L (F : Set L) = ⊤ ∧
      ∃ q : ℚ, 1 < q ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        q ^ n ≤ (sfinrank k (lieGrowthBall k F n) : ℚ)

/-- Genuine subexponential growth of a finitely generated Lie algebra,
using the manuscript Lie balls (with the documented zero-based shift). -/
def HasSubexponentialLieGrowth
    (L : Type v) [LieRing L] [LieAlgebra k L] : Prop :=
  ∃ F : Submodule k L,
    FiniteDimensional k F ∧
      LieSubalgebra.lieSpan k L (F : Set L) = ⊤ ∧
      IsSubexponentialSequence
        (fun n => sfinrank k (lieGrowthBall k F n))

/-- Every finitely generated Lie subalgebra has genuine subexponential
growth. -/
def HasLocallySubexponentialGrowth
    (L : Type v) [LieRing L] [LieAlgebra k L] : Prop :=
  ∀ S : LieSubalgebra k L,
    IsFinitelyGeneratedLieAlgebra (k := k) S →
      HasSubexponentialLieGrowth k S

end
end HopfAmenability
namespace HopfAmenability
noncomputable section
universe u
variable (k : Type u) [Field k]
/-- The class `SL`: the closure of subexponential-growth Lie algebras under
extensions and directed unions.  As for `EL`, subalgebra and quotient
closure is a derived property of this hierarchy. -/
inductive IsSubexponentiallyAmenableLieObject : LieAlgebraObject k → Prop
  | subexponential (A : LieAlgebraObject k)
      (hA : HasSubexponentialLieGrowth k A.Carrier) :
      IsSubexponentiallyAmenableLieObject A
  | extension (A : LieAlgebraObject k) (I : LieIdeal k A.Carrier)
      (hI : IsSubexponentiallyAmenableLieObject (A.ofIdeal I))
      (hQ : IsSubexponentiallyAmenableLieObject (A.quotient I)) :
      IsSubexponentiallyAmenableLieObject A
  | directedUnion (A : LieAlgebraObject k) (ι : Type u) [Nonempty ι]
      (S : ι → LieSubalgebra k A.Carrier)
      (hdir : Directed (· ≤ ·) S) (hsup : iSup S = ⊤)
      (hS : ∀ i,
        IsSubexponentiallyAmenableLieObject (A.ofSubalgebra (S i))) :
      IsSubexponentiallyAmenableLieObject A

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
  by sorry

/-- C: H is amenable iff every nonzero H-module coalgebra is amenable.
The equivalence quantifies over carriers in H's universe; the next declaration
also states the forward implication for an arbitrary carrier universe. -/
theorem theoremC : IsAmenableHopfAlgebra (k := k) (H := H) ↔
    ∀ (N : Type v) [AddCommGroup N] [Module k N] [Module H N]
      [IsScalarTower k H N] [Coalgebra k N]
      [IsHopfModuleCoalgebra k H N] [Nontrivial N],
      IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := N) :=
  by sorry

/-- C, forward implication without a common-universe restriction. -/
theorem theoremC_module {M : Type w}
    [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Coalgebra k M] [IsHopfModuleCoalgebra k H M] [Nontrivial M]
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M) :=
  by sorry

/-- D, conditional on the unformalized Takeuchi–Wigner input: H is projective
as a K-module by restriction along the displayed Hopf embedding. -/
theorem theoremD {K : Type w} [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hprojective : letI := Module.compHom H i.toAlgHom.toRingHom; Module.Projective K H)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfAlgebra (k := k) (H := K) :=
  by sorry
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
  by sorry

/-- E, equivalence form: the reverse subalgebra implication is conditional
on projectivity of B over A, the same literature input as in D. -/
theorem theoremE_iff (e : CleftExactSequence (k := k) A B C)
    (hprojective : letI := Module.compHom B e.inclusion.toAlgHom.toRingHom;
      Module.Projective A B) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) :=
  by sorry
end Cleft
end
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
  by sorry

/-- F: every nonzero module over an amenable group's group algebra is
algebraically amenable, over any field. -/
theorem theoremF (hG : GroupActionAmenable G G) [Nontrivial V] :
    Folner (Algebra.lsmul k k V : MonoidAlgebra k G →ₐ[k] Module.End k V).toLinearMap :=
  by sorry
end Group

section Lie
variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

/-- G: locally subexponential Lie growth implies amenability. -/
theorem theoremG_growth (h : HasLocallySubexponentialGrowth k L) :
    LieAmenable k L :=
  by sorry

/-- G: amenability descends along injective Lie homomorphisms.
The proof uses relative PBW and does not require the projectivity hypothesis of D. -/
theorem theoremG_subalgebra {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f) (hQ : LieAmenable k Q) :
    LieAmenable k L :=
  by sorry

/-- G: Lie quotients of amenable Lie algebras are amenable. -/
theorem theoremG_quotient (I : LieIdeal k L) (hL : LieAmenable k L) :
    LieAmenable k (L ⧸ I) :=
  by sorry

/-- G: a Lie algebra is amenable iff its ideal and quotient are amenable. -/
theorem theoremG_extension (I : LieIdeal k L) :
    LieAmenable k L ↔ LieAmenable k I ∧ LieAmenable k (L ⧸ I) :=
  by sorry

/-- G: directed unions of amenable Lie subalgebras are amenable. -/
theorem theoremG_union {ι : Type w} [Nonempty ι]
    (S : ι → LieSubalgebra k L) (hdir : Directed (· ≤ ·) S) (hsup : iSup S = ⊤)
    (hS : ∀ i, LieAmenable k (S i)) : LieAmenable k L :=
  by sorry
end Lie

section Hierarchy
variable (k : Type u) [Field k]

/-- H: elementary Lie algebras are subexponentially amenable. -/
theorem theoremH_EL_SL (A : LieAlgebraObject.{u, u} k)
    (hA : IsElementaryLieObject.{u, u, u} A) :
    IsSubexponentiallyAmenableLieObject k A :=
  by sorry

/-- H: subexponentially amenable Lie algebras are amenable. -/
theorem theoremH_SL_AL (A : LieAlgebraObject.{u, u} k)
    (hA : IsSubexponentiallyAmenableLieObject k A) : LieAmenable k A.Carrier :=
  by sorry

/-- H: in characteristic zero the inclusion EL ⊆ SL is strict, witnessed
in the proof by the Witt algebra. No literature input is assumed here. -/
theorem theoremH_charZero [CharZero k] :
    ∃ A : LieAlgebraObject.{u, u} k,
      IsSubexponentiallyAmenableLieObject k A ∧ ¬ IsElementaryLieObject.{u, u, u} A :=
  by sorry

/-- H over an arbitrary field, conditional on the positive-characteristic
PSZ construction. The explicit input supplies a finitely generated algebra
of subexponential growth outside EL in each prime characteristic. -/
theorem theoremH
    (hPSZ : ∀ p : ℕ, ∀ (_ : Fact p.Prime) (_ : CharP k p),
      ∃ A : LieAlgebraObject.{u, u} k,
        HasSubexponentialLieGrowth k A.Carrier ∧ ¬ IsElementaryLieObject.{u, u, u} A) :
    ∃ A : LieAlgebraObject.{u, u} k,
      IsSubexponentiallyAmenableLieObject k A ∧ ¬ IsElementaryLieObject.{u, u, u} A :=
  by sorry

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
  by sorry
end Hierarchy
end
end Palomar

namespace HopfAmenability
noncomputable section
universe u v w
variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
/-- The augmentation ideal of a bialgebra. -/
def augmentationIdeal : Ideal H :=
  RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom

/-- A stable proof term for the scalar tower in the augmentation filtration. -/
theorem augmentationScalarTower : IsScalarTower k H H := IsScalarTower.right

/-- The descending augmentation filtration. -/
def augmentationFiltration (n : ℕ) : Submodule k H :=
  letI : IsScalarTower k H H := augmentationScalarTower
  ((augmentationIdeal (k := k) (H := H) ^ n : Ideal H) :
    Submodule H H).restrictScalars k

/-- The augmentation filtration on a left Hopf module. -/
def augmentationModuleFiltration
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] (n : ℕ) : Submodule k M :=
  actionSubspace (augmentationFiltration (k := k) (H := H) n) ⊤

/-- The underlying augmentation-graded module. -/
abbrev AugmentationGradedModule
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :=
  DirectSum ℕ fun n =>
    augmentationModuleFiltration (k := k) (H := H) (M := M) n ⧸
      (augmentationModuleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
        (augmentationModuleFiltration (k := k) (H := H) (M := M) n).subtype

/-- The underlying augmentation-graded Hopf vector space. -/
abbrev AugmentationGradedHopf :=
  DirectSum ℕ fun n =>
    augmentationFiltration (k := k) (H := H) n ⧸
      (augmentationFiltration (k := k) (H := H) (n + 1)).comap
        (augmentationFiltration (k := k) (H := H) n).subtype

end
end HopfAmenability

namespace Palomar
open HopfAmenability Coalgebra Module TensorProduct
noncomputable section
universe u v w
/-- Stable composition instance for the symbol map. -/
theorem symbolCompTriple {k : Type u} [Field k] :
    RingHomCompTriple (RingHom.id k) (RingHom.id k) (RingHom.id k) :=
  RingHomCompTriple.ids

/-- The degree-n symbol W_n → direct sum of W_i/W_(i + 1), for a descending
filtration W. All quotients and the direct sum use their canonical k-modules. -/
def symbol {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (n : ℕ) :
    W n →ₗ[k] DirectSum ℕ (fun i => W i ⧸ (W (i + 1)).comap (W i).subtype) :=
  letI : RingHomCompTriple (RingHom.id k) (RingHom.id k) (RingHom.id k) :=
    symbolCompTriple
  (DirectSum.lof k ℕ _ n).comp ((W (n + 1)).comap (W n).subtype).mkQ
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
  by sorry
end
end Palomar
