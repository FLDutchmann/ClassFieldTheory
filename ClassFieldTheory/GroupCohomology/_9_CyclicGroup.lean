import Mathlib
import ClassFieldTheory.GroupCohomology._6_LeftRegular
import ClassFieldTheory.GroupCohomology._8_DimensionShift

/-!
Let `M : Rep R G`, where `G` is a finite cyclic group.
We construct an exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

Using this sequence, we construct an isomorphism

  `dimensionShift.up.obj M ≅ dimensionShift.down.obj M`.

Using this, construct isomorphisms

  `Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)`.

-/

open
  Finsupp
  Rep
  leftRegular
  dimensionShift
  CategoryTheory
  ConcreteCategory
  Limits
  BigOperators
  groupCohomology


variable {R : Type} [CommRing R]
variable (G : Type) [Group G] [instCyclic :IsCyclic G] [Finite G] [DecidableEq G]
variable (M : Rep R G)

noncomputable section

/--
`gen G` is a generator of the cyclic group `G`.
-/
abbrev gen : G := IsCyclic.exists_generator.choose

variable {G}

@[simp] lemma ofHom_sub (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ - f₂) : A ⟶ B) = ofHom f₁ - ofHom f₂ := rfl

@[simp] lemma ofHom_add (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ + f₂) : A ⟶ B) = ofHom f₁ + ofHom f₂ := rfl

@[simp] lemma ofHom_zero (A B : ModuleCat R) :
  (ofHom 0 : A ⟶ B) = 0 := rfl

@[simp] lemma ofHom_one (A : ModuleCat R) :
  (ofHom 1 : A ⟶ A) = 𝟙 A := rfl

omit [IsCyclic G] [Finite G] [DecidableEq G] in
@[simp] lemma Rep.ρ_mul_eq_comp (M : Rep R G) (x y : G) :
    Action.ρ M (x * y) = (Action.ρ M y) ≫ (Action.ρ M x) := map_mul (Action.ρ M) x y

namespace Representation

variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

@[simps] def map₁ : (G → A) →ₗ[R] (G → A) where
  toFun f x := f x - f ((gen G)⁻¹ * x)
  map_add' := sorry
  map_smul' := sorry

omit [Finite G] [DecidableEq G] in
lemma map₁_comm (g : G) :
    map₁ ∘ₗ ρ.coind₁' g = ρ.coind₁' g ∘ₗ map₁  := by
  apply LinearMap.ext
  intro
  apply funext
  intro
  simp [mul_assoc]

omit [Finite G] [DecidableEq G] in
lemma map₁_comp_coind_ι :
    map₁ (R := R) (G := G) (A := A) ∘ₗ coind₁'_ι = 0 := by
  ext; simp

omit [Finite G] [DecidableEq G] in
lemma map₁_ker :
    LinearMap.ker (map₁ (R := R) (G := G) (A := A)) = LinearMap.range coind₁'_ι :=
  sorry

@[simps!] def map₂ : (G →₀ A) →ₗ[R] (G →₀ A) :=
  LinearMap.id - lmapDomain _ _ (fun x ↦ gen G * x)

omit [Finite G] [DecidableEq G] in
@[simp] lemma map₂_comp_lsingle (x : G) :
    map₂ (R := R) (G := G) (A := A) ∘ₗ lsingle x = lsingle x - lsingle (gen G * x) := by
  ext
  simp [map₂, LinearMap.sub_comp]

omit [Finite G] [DecidableEq G] in
lemma map₂_comm (g : G) :
    map₂ ∘ₗ ρ.ind₁' g = ρ.ind₁' g ∘ₗ map₂ := by
  ext x : 1
  rw [LinearMap.comp_assoc, ind₁'_comp_lsingle, LinearMap.comp_assoc, map₂_comp_lsingle,
    LinearMap.comp_sub, ind₁'_comp_lsingle, ←LinearMap.comp_assoc, map₂_comp_lsingle,
    LinearMap.sub_comp, ind₁'_comp_lsingle, mul_assoc]

omit [Finite G] [DecidableEq G] in
lemma ind₁'_π_comp_map₂ :
    ind₁'_π ∘ₗ map₂ (R := R) (G := G) (A := A) = 0 := by
  ext : 1
  rw [LinearMap.comp_assoc, map₂_comp_lsingle, LinearMap.comp_sub,
    LinearMap.zero_comp, sub_eq_zero, ind₁'_π_comp_lsingle, ind₁'_π_comp_lsingle]

omit [DecidableEq G] in
lemma npowIsSurjective (x : G) : ∃ n : Fin (Nat.card G) , (gen G) ^ n.1 = x := by
  let n := (IsCyclic.exists_generator.choose_spec x).choose
  let hn : (gen G) ^ n = x := (IsCyclic.exists_generator.choose_spec x).choose_spec

  let n' : ℤ  := ( n % Nat.card G )

  have : 0 < Nat.card G := by
    exact @Nat.card_pos _ (Nonempty.intro x) _

  have isPosN': 0 ≤ ( n % Nat.card G ) := by
    apply Int.emod_nonneg n
    apply Int.natCast_ne_zero_iff_pos.mpr this

  use ⟨( n % Nat.card G ).toNat, ?_⟩
  · have : ((n % ↑(Nat.card G)).toNat : ℤ) = (n % ↑(Nat.card G)) := by
      exact Int.toNat_of_nonneg isPosN'
    have : gen G ^ (n % ↑(Nat.card G)).toNat = gen G ^ (n % ↑(Nat.card G)) := by
      calc gen G ^ (n % ↑(Nat.card G)).toNat = gen G ^ ((n % ↑(Nat.card G)).toNat : ℤ) := by
            exact Eq.symm (zpow_natCast (gen G) (n % ↑(Nat.card G)).toNat)
          _ = gen G ^ (n % ↑(Nat.card G)) := by rw [this]

    rw [← hn, this]
    exact zpow_mod_natCard (gen G) n
  · simp only [Nat.card_pos, Int.toNat_lt']
    exact Int.emod_lt_of_pos ((IsCyclic.exists_generator.choose_spec x).choose) <| Int.natCast_pos.mpr (@Nat.card_pos _ (Nonempty.intro x) _)



lemma map₂_range :
    LinearMap.range (map₂ (R := R) (G := G) (A := A)) = LinearMap.ker ind₁'_π := by
  ext f
  constructor
  · intro hf
    apply LinearMap.mem_ker.mpr

    let f' := Classical.choose (LinearMap.mem_range.1 hf)
    let hf' : map₂ f' = f :=  Classical.choose_spec (LinearMap.mem_range.1 hf)

    suffices (ind₁'_π ∘ₗ map₂ (R := R) (G := G) (A := A)).toFun f' = 0 by
      rw [← hf', ← this]
      simp
    rw [ind₁'_π_comp_map₂]
    simp
  · intro hf
    apply LinearMap.mem_range.2

    have y' : Fin (Nat.card G) → A := fun r => ∑ i ∈ Finset.range r.1 , (f.toFun <| (gen G) ^ i)
    have y : G → A := fun x => y' (npowIsSurjective x).choose

    use Finsupp.equivFunOnFinite.invFun y
    ext x
    simp [map₂, mapDomain]
    let n := (npowIsSurjective x).choose
    let hn : (gen G) ^ n.1 = x := (npowIsSurjective x).choose_spec
    rw [← hn]
    simp
    sorry

end Representation

namespace Rep

/--
The map `coind₁'.obj M ⟶ coind₁' M` which takes a function `f : G → M.V` to
`x ↦ f x - f (gen G * x)`.
-/
def map₁ : coind₁' (R := R) (G := G) ⟶ coind₁' where
  app M := {
    hom := ofHom Representation.map₁
    comm g := by
      ext : 1
      apply Representation.map₁_comm
  }
  naturality := sorry

omit [Finite G] [DecidableEq G] in
lemma coind_ι_gg_map₁_app : coind₁'_ι.app M ≫ map₁.app M = 0 := by
  ext : 2
  apply Representation.map₁_comp_coind_ι

omit [Finite G] [DecidableEq G] in
lemma coind_ι_gg_map₁ : coind₁'_ι ≫ map₁ (R := R) (G := G) = 0 := by
  ext : 2
  apply coind_ι_gg_map₁_app


def map₂ : ind₁' (R := R) (G := G) ⟶ ind₁' where
  app M := {
    hom := ofHom Representation.map₂
    comm g := by
      ext : 1
      apply Representation.map₂_comm
  }
  naturality := sorry

omit [Finite G] [DecidableEq G] in
lemma map₂_app_gg_ind₁'_π_app :  map₂.app M ≫ ind₁'_π.app M = 0 := by
  ext : 2
  apply Representation.ind₁'_π_comp_map₂

omit [Finite G] [DecidableEq G] in
lemma map₂_gg_ind₁'_π : map₂ (R := R) (G := G) ≫ ind₁'_π = 0 := by
  ext : 2
  apply map₂_app_gg_ind₁'_π_app

/--
Let `M` be a representation of a finite cyclic group `G`.
Then the following square commutes

  ` coind₁'.obj M -------> coind₁'.obj M `
  `      |                      |        `
  `      |                      |        `
  `      ↓                      ↓        `
  `   ind₁'.obj M ------->   ind₁'.obj M `

The vertical maps are the canonical isomorphism `ind₁'_iso_coind₁`
and the horizontal maps are `map₁` and `map₂`.
-/
lemma map₁_comp_ind₁'_iso_coind₁' :
    map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv = (ind₁'_iso_coind₁'.app M).inv ≫ map₂.app M :=
  sorry


/--
For a cyclic group `G`, this is the sequence of representations of a cyclic group:

` 0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0 `.

The middle map is `map₁ ≫ ind₁'_iso_coind₁'.inv`, which is
equal to `ind₁'_iso_coind₁'.inv ≫ map₂`. The sequence is exact.

It might be sensible to make this into a functor.
-/
def periodicitySequence : CochainComplex (Rep R G) (Fin 4) where
  X
  | 0 => M
  | 1 => coind₁'.obj M
  | 2 => ind₁'.obj M
  | 3 => M
  d
  | 0,1 => coind₁'_ι.app M
  | 1,2 => map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv
  | 2,3 => ind₁'_π.app M
  | _,_ => 0
  d_comp_d' :=
    /-
    Proved in lemmas above in the non-trivial cases.
    -/
    sorry

lemma periodicitySequence_exactAt_one : (periodicitySequence M).ExactAt 1 := sorry

lemma periodicitySequence_exactAt_two : (periodicitySequence M).ExactAt 2 := sorry

include instCyclic in
def up_obj_iso_down_obj : up.obj M ≅ down.obj M :=
  have := instCyclic
  /-
  `up.obj M` is the cokernel of the first map is `periodicitySequence`,
  so is isomorphic to the image of the second map. This in turn is isomorphic to the
  kernel of the last map, which is `down.obj M`.
  -/
  sorry

def up_iso_down : up (R := R) (G := G) ≅ down where
  hom := {
    app M := (up_obj_iso_down_obj M).hom
    naturality := sorry
  }
  inv := {
    app M := (up_obj_iso_down_obj M).inv
    naturality := sorry
  }

def periodicCohomology (n : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 3) := by
  apply Iso.trans (down_δiso_natTrans n)
  apply Iso.trans (Functor.isoWhiskerRight up_iso_down.symm _)
  apply up_δiso_natTrans

def periodicCohomology' (n m : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 1 + 2 * m) := by
  induction m with
  | zero =>
    apply Iso.refl
  | succ m ih =>
    apply Iso.trans ih
    rw [mul_add, mul_one, ←add_assoc, add_assoc, add_comm 1, ←add_assoc]
    apply periodicCohomology


omit [DecidableEq G] in
/--
Let `M` be a representation of a finite cyclic group `G`. Suppose there are even
and positive integers `e` and `o` with `e` even and `o` odd, such that
`Hᵉ(G,M)` and `Hᵒ(G,M)` are both zero.
Then `Hⁿ(G,M)` is zero for all `n > 0`.
-/
lemma isZero_ofEven_ofOdd {M : Rep R G} {a b : ℕ}
    (hₑ : IsZero (groupCohomology M (2 * a + 2)))
    (hₒ : IsZero (groupCohomology M (2 * b + 1))) (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) := by
  sorry


end Rep

end
