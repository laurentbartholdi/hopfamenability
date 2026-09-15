/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremD
import Amenability.TheoremE
import Amenability.TheoremG

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

local notation "U" => UniversalEnvelopingAlgebra k L

section HopfSubalgebraDescent

universe x y

variable {H : Type x} {K : Type y}
variable [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [Ring K] [HopfAlgebra k K] [Coalgebra.IsCocomm k K]

omit [Coalgebra.IsCocomm k H] in
/-- Algebraic amenability descends along a cocommutative Hopf-subalgebra
embedding. The only external input is projectivity; the Følner descent is
`algebraicallyAmenable_of_projective` above. -/
theorem palomar_algebraic_descent
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hprojective : letI := hopfSubalgebraRestrictionModule i; Module.Projective K H)
    (hH : IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H)) :
    IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := K) := by
  let _ : Module K H := hopfSubalgebraRestrictionModule i
  let _ : IsScalarTower k K H :=
    IsScalarTower.of_algebraMap_smul fun r h => by
      change i.toAlgHom (algebraMap k K r) * h = r • h
      rw [i.toAlgHom.commutes, Algebra.smul_def]
  have hrestricted : IsAlgebraicallyAmenableModule
      (k := k) (A := K) (Q := H) := by
    intro F hF ε hε
    let F' : Submodule k H := F.map i.toAlgHom.toLinearMap
    let _ : FiniteDimensional k F' := by
      dsimp [F']
      infer_instance
    obtain ⟨E, hE, hEfd, hratio⟩ := hH F' inferInstance ε hε
    refine ⟨E, hE, hEfd, ?_⟩
    have hexpansion :
        algebraModuleExpansion (k := k) F E = actionExpansion F' E := by
      rw [algebraModuleExpansion, actionExpansion, actionSubspace_eq_map₂]
      congr 1
      apply le_antisymm
      · apply Submodule.map₂_le.2
        intro a ha e he
        exact Submodule.mem_map₂
          (Algebra.lsmul k k H).toLinearMap F' E
          (show i.toAlgHom a ∈ F' from ⟨a, ha, rfl⟩) he
      · apply Submodule.map₂_le.2
        intro a ha e he
        rcases ha with ⟨a, ha, rfl⟩
        exact Submodule.mem_map₂ _ _ _ ha he
    rwa [hexpansion]
  let _ : Module.Projective K H :=
    hprojective
  have hK := algebraicallyAmenable_of_projective hrestricted
  intro F hF ε hε
  obtain ⟨E, hE, hEfd, hratio⟩ := hK F hF ε hε
  exact ⟨E, hE, hEfd, by
    simpa only [algebraModuleExpansion, actionExpansion,
      actionSubspace_eq_map₂] using hratio⟩

/-- **Theorem D.** Every Hopf subalgebra of an amenable cocommutative Hopf
algebra is amenable. -/
theorem palomar_hopf_descent
    (i : HopfSubalgebraEmbedding (k := k) (H := H) K)
    (hprojective : letI := hopfSubalgebraRestrictionModule i; Module.Projective K H)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfAlgebra (k := k) (H := K) := by
  apply isAmenableHopfAlgebra_iff_algebraicallyAmenable.mpr
  exact palomar_algebraic_descent i hprojective
    (isAmenableHopfAlgebra_iff_algebraicallyAmenable.mp hH)

end HopfSubalgebraDescent


end
end HopfAmenability

namespace HopfAmenability
universe u v w
variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
/-- Relative PBW supplies subalgebra descent without the external Hopf projectivity input. -/
theorem palomar_lie_descent {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  isAmenableLieAlgebra_of_injective_of_iota_injective f hf
    UniversalEnvelopingAlgebra.iota_injective
    UniversalEnvelopingAlgebra.iota_injective hQ
end HopfAmenability
