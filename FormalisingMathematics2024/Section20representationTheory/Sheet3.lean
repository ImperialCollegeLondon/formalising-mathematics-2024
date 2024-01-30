/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke
-- Maschke's theorem

/-

# Representation theory via k[G]-modules

It might have struck you as odd that we have a definition of `representation`
but not a definition of map between representations. One reason for this
is that there's another way of thinking about representations, which is
that they are `k[G]-modules`. Here `k[G]` is the so-called group ring associated
to `k` and `G`; it's a vector space with basis indexed by `G`, and multiplication
given by multiplication on `G` and extended linearly, so (∑ aᵢgᵢ)(∑ bⱼhⱼ) := ∑ᵢⱼ(aᵢbⱼ)(gᵢhⱼ)
for `aᵢ, bⱼ : k` and `gᵢ, hⱼ : G`.

Because the construction works with monoids (note that there's no mention of inverses
in the definition of the group ring), it's called `MonoidAlgebra` in Lean.

-/

variable (k : Type) [Field k] (G : Type) [Group G]

example : Type :=
  MonoidAlgebra k G

noncomputable section

-- Lean moans about various things if you don't switch this on
-- Note that this doesn't matter for mathematicians, this is a computer science thing
example : Ring (MonoidAlgebra k G) :=
  inferInstance

-- Turns out that there's a bijection between modules for the group ring k[G],
-- and representations of G on k-vector spaces. The dictionary works like this.
-- Let ρ be a representation of G on a k-vector space V
variable (V : Type) [AddCommGroup V] [Module k V] (ρ : Representation k G V)

-- Here's the underlying type of the module.
example : Type :=
  ρ.asModule

-- Note that `ρ.as_module` is definitionally equal to `V`, but it knows about `ρ` because `ρ` is in its name.
-- As a result, this works:
example : Module (MonoidAlgebra k G) ρ.asModule :=
  inferInstance

-- This wouldn't work with `ρ.asModule` replaced by `V`, because type class inference wouldn't
-- be able to find `ρ`
-- The other way: let `M` be a `k[G]`-module
variable (M : Type) [AddCommGroup M] [Module (MonoidAlgebra k G) M]

-- Here's the representation
example : Representation k G (RestrictScalars k (MonoidAlgebra k G) M) :=
  Representation.ofModule M
-- What's going on here? The issue is that type class inference can't by default find the k-module
-- structure on `M`, so this `restrict_scalars k (monoid_algebra k G) M` thing means "`M`, but with
-- the `k`-action coming from the monoid_algebra k G action"
-- It's defeq to `M`:
example : RestrictScalars k (MonoidAlgebra k G) M = M :=
  rfl

-- So another way of doing morphisms between representations is as `MonoidAlgebra k G` morphisms.
-- Let σ be another representation
variable (W : Type) [AddCommGroup W] [Module k W] (σ : Representation k G W)

-- The type of G-morphisms between `ρ` and `σ`
example : Type :=
  ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule

-- If you do it this way, then you don't have to make G-morphisms.
-- Let φ be a G-morphism
variable (φ : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule)

-- Then you can evaluate it at elements of `V`
example (v : V) : W :=
  φ v

-- This works because `V = ρ.asModule` definitionally.
-- The k[G]-module language is how Lean expresses Maschke's theorem.
-- Assume `G` is finite, and its order is invertible in `k`
variable [Fintype G] [Invertible (Fintype.card G : k)]

-- Assume `V` and `W` are k[G]-modules (with the k[G]-action compatible with the k-action)
variable [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V]
  [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]

-- Then every injective k[G]-linear map from `V` to `W` has a one-sided inverse
-- (and hence a complement, namely the kernel of the inverse)
example (φ : V →ₗ[MonoidAlgebra k G] W) (hφ : LinearMap.ker φ = ⊥) :
    ∃ ψ : W →ₗ[MonoidAlgebra k G] V, ψ.comp φ = LinearMap.id :=
  MonoidAlgebra.exists_leftInverse_of_injective φ hφ
