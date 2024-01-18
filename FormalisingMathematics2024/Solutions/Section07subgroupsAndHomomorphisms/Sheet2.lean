/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Group homomorphisms

mathlib has group homomorphisms. The type of group homomorphisms from `G` to `H` is called
`MonoidHom G H`, but we hardly ever use that name; instead we use the notation, which
is `G →* H`, i.e. "`*`-preserving map between groups". Note in particular that we do *not*
write `f : G → H` for a group homomorphism and then have some
function `is_group_hom : (G → H) → Prop` saying that it's a group homomorphism, we just have a
completely new type, whose terms are pairs consisting of the function and the axiom
that `f(g₁g₂)=f(g₁)f(g₂)` for all g₁ and g₂.
-/

-- Let `G` and `H` be groups.
variable {G H : Type} [Group G] [Group H]

-- let `φ : G → H` be a group homomorphism
variable (φ : G →* H)

-- Even though `φ` is not technically a function (it's a pair consisting of a function and
-- a proof), we can still evaluate `φ` at a term of type `G` and get a term of type `H`.
-- let `a` be an element of G
variable (a : G)

-- let's make the element `φ(a)` of `H`
example : H :=
  φ a

-- Here's the basic API for group homomorphisms
example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b

example : φ 1 = 1 :=
  φ.map_one

example (a : G) : φ a⁻¹ = (φ a)⁻¹ :=
  φ.map_inv a

-- The identity group homomorphism from `G` to `G` is called `monoid_hom.id G`
example : MonoidHom.id G a = a := by rfl

-- true by definition
-- Let K be a third group.
variable (K : Type) [Group K]

-- Let `ψ : H →* K` be another group homomorphism
variable (ψ : H →* K)

-- The composite of ψ and φ can't be written `ψ ∘ φ` in Lean, because `∘` is notation
-- for function composition, and `φ` and `ψ` aren't functions, they're collections of
-- data containing a function and some other things. So we use `monoid_hom.comp` to
-- compose functions. We can use dot notation for this.
example : G →* K :=
  ψ.comp φ

-- When are two group homomorphisms equal? When they agree on all inputs. The `ext` tactic
-- knows this.
-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.
theorem comp_id : φ.comp (MonoidHom.id G) = φ :=
  by
  ext x
  rfl

theorem id_comp : (MonoidHom.id H).comp φ = φ :=
  by
  ext x
  rfl

theorem comp_assoc {L : Type} [Group L] (ρ : K →* L) : (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) := by
  rfl

-- The kernel of a group homomorphism `φ` is a subgroup of the source group.
-- The elements of the kernel are *defined* to be `{x | φ x = 1}`.
-- Note the use of dot notation to save us having to write `monoid_hom.ker`.
-- `φ.ker` *means* `monoid_hom.ker φ` because `φ` has type `monoid_hom [something]`
example (φ : G →* H) : Subgroup G :=
  φ.ker

-- or `monoid_hom.ker φ`
example (φ : G →* H) (x : G) : x ∈ φ.ker ↔ φ x = 1 := by rfl

-- true by definition
-- Similarly the image is defined in the obvious way, with `monoid_hom.range`
example (φ : G →* H) : Subgroup H :=
  φ.range

example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y := by rfl

-- true by definition
-- `subgroup.map` is used for the image of a subgroup under a group hom
example (φ : G →* H) (S : Subgroup G) : Subgroup H :=
  S.map φ

example (φ : G →* H) (S : Subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y := by rfl

-- and `subgroup.comap` is used for the preimage of a subgroup under a group hom.
example (φ : G →* H) (S : Subgroup H) : Subgroup G :=
  S.comap φ

example (φ : G →* H) (T : Subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T := by rfl

-- Here are some basic facts about these constructions.
-- Preimage of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.comap (MonoidHom.id G) = S :=
  by
  ext x
  rfl

-- Image of a subgroup along the identity map is the same subgroup
example (S : Subgroup G) : S.map (MonoidHom.id G) = S :=
  by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

-- preimage preserves `≤` (i.e. if `S ≤ T` are subgroups of `H` then `φ⁻¹(S) ≤ φ⁻¹(T)`)
example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ :=
  by
  intro g hg
  apply hST
  exact hg

-- image preserves `≤` (i.e. if `S ≤ T` are subgroups of `G` then `φ(S) ≤ φ(T)`)
example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ :=
  by
  rintro h ⟨g, hg, rfl⟩
  refine' ⟨g, _, rfl⟩
  exact hST hg

-- Pulling a subgroup back along one homomorphism and then another, is equal
-- to pulling it back along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : U.comap (ψ.comp φ) = (U.comap ψ).comap φ := by
  rfl

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : S.map (ψ.comp φ) = (S.map φ).map ψ :=
  by
  ext c
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine' ⟨φ a, _, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
