/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.RepresentationTheory.Basic


namespace Section20Sheet2Solutions

/-

# Representation theory

Homomorphisms between representations; representations as modules.

-/
-- Let ρ and σ be representations of G on V and W
variable {k : Type} [Field k] {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module k V]
variable {W : Type} [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

-- According to one of my PhD students yesterday, there is no "G-linear map" class!
-- So let's make one.
-- this makes the `ext` tactic work on rep_maps, i.e. it shows that two rep_maps are
-- the same if they are the same underlying function
/-- The G-equivariant linear maps between two representations. -/
@[ext]
structure RepMap (ρ : Representation k G V) (σ : Representation k G W) : Type where
  toLinearMap : V →ₗ[k] W
  map_apply : ∀ (g : G) (v : V), toLinearMap (ρ g v) = σ g (toLinearMap v)

-- What should be now prove about it?
/-

## Categories

A category is a collection of objects, and between any pair of objects there's a collection
of maps or morphisms. Technical point: these maps/morphisms *don't actually have to be functions*,
the definition is more abstract than that. But let's not dwell on this right now.

That's not the end of the definition of a category -- there is a bit more structure,
and some axioms, but let's just give some examples first:

Example: in set theory the collection of all sets is a category; the morphisms between two sets
are just the functions between the sets.

Example: In type theory the collection of all types is a category; the morphisms are again just
the functions between the types.

Example: if we fix a field `k` and a group `G` then we can make a category whose objects
are `k`-vector spaces equipped with an action of `G` (i.e. representations of `G`) and
whose morphisms are the `G`-linear maps. Note that here the morphisms are *certain* maps
between the objects, but not *all* the maps.

Let's get back to the definition of a category. I need to explain the extra
structure and the axioms of a category. The extra structure is:

S1) For every object `X` of the category, there has to be an identity morphism `id_X : X → X`
S2) If we have three objects `X`, `Y`, and `Z` in the category, and two morphisms
`f : X → Y` and `g : Y → Z` then there's a way of composing them to get `g ∘ f : X → Z`.

For example, in the representation theory example above, the category theoretic composition
is just defined to be function composition, and ensuring that this gives a valid morphism
boils down to checking that the composite of two `G`-linear maps is `G`-linear.

The axioms are:

A1) If `f : X → Y` then `id_Y ∘ f = f` and `f ∘ id_X = f`
A2) If `f : W → X`, `g : X → Y` and `h : Y → Z` then `(f ∘ g) ∘ h = f ∘ (g ∘ h)`

The reason I mention these is that they inform us about what we should be proving
about `RepMap`!

-/
namespace RepMap

def id (ρ : Representation k G V) : RepMap ρ ρ where
  toLinearMap := LinearMap.id
  map_apply _ _ := rfl

variable {X : Type} [AddCommGroup X] [Module k X]

variable {ρ σ}

def comp {τ : Representation k G X}
    (ψ : RepMap σ τ) (φ : RepMap ρ σ) : RepMap ρ τ where
  toLinearMap := ψ.toLinearMap.comp φ.toLinearMap
  map_apply := by
    intros
    simp [φ.map_apply, ψ.map_apply]

theorem comp_id (φ : RepMap ρ σ) : φ.comp (id ρ) = φ := by
  ext; rfl

theorem id_comp (φ : RepMap ρ σ) : (id σ).comp φ = φ := by
  ext; rfl

theorem comp_assoc
    {τ : Representation k G X} {Y : Type} [AddCommGroup Y] [Module k Y]
    {υ : Representation k G Y}
    (ξ : RepMap τ υ) (ψ : RepMap σ τ) (φ : RepMap ρ σ) :
    (ξ.comp ψ).comp φ = ξ.comp (ψ.comp φ) := by
  rfl

end RepMap

end Section20Sheet2Solutions
