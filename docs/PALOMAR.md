# Palomar submission: Theorems A–J

The package covers all manuscript main theorems through **21 compared declarations**.
The source is Laurent Bartholdi,
[Amenability of Lie, Group and Hopf algebras](https://arxiv.org/abs/2609.10373v1).

## Statement-to-proof map

Names below are in `Palomar`, except the two A declarations in `HopfAmenability`.
Every listed declaration is in `Solution.lean` and selected by `comparator.json`.

| Result | Compared declarations | Proof source and qualifications |
|---|---|---|
| A | `palomar_rounding`, `palomar_amenability` | Sharp rounding and the Følner equivalence from `TheoremA.lean`. |
| B | `theoremB` | Equivariant surjective coalgebra quotients, `TheoremB.lean`. |
| C | `theoremC`, `theoremC_module` | All nonzero module coalgebras, `TheoremC.lean`; the second declaration allows an arbitrary target universe. |
| D | `theoremD` | Hopf-subalgebra permanence, conditional on explicit projectivity of the ambient algebra over the displayed subalgebra. |
| E | `theoremE_extension`, `theoremE_iff` | Cleft extensions, `TheoremE.lean`; only the iff form needs explicit projectivity. |
| F | `theoremF_permutation`, `theoremF` | Permutation-module quotients and nonzero modules of amenable groups, `TheoremF.lean`. |
| G | `theoremG_growth`, `theoremG_subalgebra`, `theoremG_quotient`, `theoremG_extension`, `theoremG_union` | Lie growth and permanence; relative PBW supplies unconditional subalgebra descent and the extension equivalence. |
| H | `theoremH_EL_SL`, `theoremH_SL_AL`, `theoremH_charZero`, `theoremH` | Hierarchy inclusions and strictness. Only the general-field separation needs the explicit positive-characteristic PSZ input. |
| I | `theoremI` | Finitely generated exponential-growth amenable Lie algebra with a locally finite-dimensional ideal and a split one-dimensional quotient, `TheoremI.lean`. |
| J | `theoremJ` | Canonical augmentation-graded action and coalgebra, with Følner subcoalgebras, `TheoremJ.lean`. |

The selected statements do not claim that the two literature inputs have been
formalized. The proof library retains its projectivity axiom and designated PSZ
hole; **none of the 21 compared proofs uses either**. Conditional proofs are
ordinary Lean theorems with explicit hypotheses, not an expanded axiom allowlist.

## Independent statement

`Challenge.lean` imports only Mathlib and spells out the definitions needed to
read A–J. Its theorem proofs are deliberate `sorry` placeholders authorized in
`AGENTS.md`. `Solution.lean` imports the substantive development and supplies
proofs with matching names and types. Never import Challenge into Solution.
There are no definition holes: `definition_names` is empty.

For the Lie results, `Palomar.LieAmenable` is the algebraic Følner condition on
the regular module of U(L). The solution uses the proved equivalence in
`LieGeneratorTest.lean` with the manuscript's finite-subcoalgebra definition.
The growth balls and inductive hierarchies retain the library definitions.

For J the underlying graded vector spaces are explicitly the direct sums of
successive augmentation quotients. The statement constructs a bilinear action
and a coalgebra structure and specifies them on all homogeneous representatives:
`[h] • [m] = [h • m]`; counit is the original counit in degree zero and zero in
positive degrees; coproduct is obtained from each total-degree decomposition of
the original coproduct. It then asserts the Følner condition using subcoalgebras
for that coproduct. This characterizes the canonical structures without importing
the substantial construction into the independent statement.

The C equivalence retains the library's same-universe quantifier; the separate
forward implication quantifies over an arbitrary module carrier universe.
Rational tolerances and the zero-based shift in Lie growth balls are explicit.

## Literature inputs

- **D and E iff:** `hprojective` asserts that the ambient Hopf algebra, with
  its regular action restricted along the given inclusion, is projective.
  The manuscript's Theorem 2.2 derives this from Takeuchi's Theorem 3.1 and
  Masuoka–Wigner's Theorem 2.1. `Palomar/Proofs.lean` repeats the short descent
  argument using this hypothesis, leaving the original public endpoints intact.
- **H in arbitrary characteristic:** `hPSZ` asserts that in prime positive
  characteristic there is a finitely generated Lie algebra of subexponential
  growth outside EL. This is the input described in the manuscript's Section 5,
  especially Theorem 5.4 and the PSZ/self-similar references there. The statement
  does not certify that construction. Characteristic-zero separation via the
  Witt algebra and the hierarchy inclusions are separately compared without it.
- **G:** the public library endpoint uses Hopf-subalgebra permanence, but the
  library also proves descent using relative PBW. The submission uses the latter,
  so no projectivity hypothesis or axiom appears in the compared G statements.

## Local verification

```sh
lake build
bash scripts/check_architecture.sh
bash scripts/check_palomar.sh
```

The submission script compiles the two independent modules, checks their source
signatures, compares their elaborated statements and reachable declarations
structurally (including definition bodies and auxiliary proofs), and checks each
solution axiom list against the standard three axioms. `Palomar/CheckStatements.lean` is a development check; it does not
replace Comparator's sandboxed export/replay or NanoDa's independent kernel.
The comparison deliberately does not unfold definitions or inline generated
proofs: these can conceal differences that Comparator rejects. Stable named
instance proofs and an explicit supremum instance keep the independently
elaborated declarations identical.
The only expected statement warnings are the intentional Challenge holes.
Building the wider project may also replay its designated PSZ warning.

The metadata is validated against the upstream formalization.yaml schema. The
committed toolchain and manifest pin the Lean and library versions.

## Registry verification and submission

Follow the current [submission instructions](https://palomar-registry.org/how-to-submit)
and [Comparator instructions](https://github.com/leanprover/comparator).
Full Comparator verification requires Linux/Landrun, a compatible lean4export,
and NanoDa. `comparator.json` enables NanoDa and allows only `propext`,
`Quot.sound`, and `Classical.choice`. Full Comparator/NanoDa verification has
not been run on the preparation machine (macOS).

On 2026-09-16, the corrected package passed Comparator's actual export,
structural comparison, axiom validation, and Lean kernel replay locally, using
Comparator `575674928e239f5bc452aab72d1dd7b0f1326494` and lean4export
`cacf989bd75f608700820f6afc595f32e7a99a4d` (the failed submission's revisions).
That development run used upstream's `scripts/fake-landrun.sh` and a temporary
configuration with NanoDa disabled; the committed configuration retains NanoDa.
Hosted verification is still required for the full sandboxed check.

Review the statements and metadata, commit and push the final snapshot to
`laurentbartholdi/hopfamenability`, and obtain the full SHA with
`git rev-parse HEAD`. Submit that SHA with the default root project,
`comparator.json`, and `formalization.yaml`. The branch name is not a snapshot
identifier. Preparation itself does not push, submit, or register the project.

Sources for the submission layout:

- [Tao's announcement](https://terrytao.wordpress.com/2026/08/18/palomar-a-registry-of-lean-verified-mathematics/)
- [About Palomar](https://palomar-registry.org/about)
- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Metadata standard](https://github.com/mathlib-initiative/formalization.yaml)
