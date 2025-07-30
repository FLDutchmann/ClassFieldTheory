/-
Copyright (c) 2025 Yaël Dillies, Nailin Guan, Gareth Ma, Arend Mellendijk, Yannis Monbru,
Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Nailin Guan, Gareth Ma, Arend Mellendijk, Yannis Monbru, Michał Mrugała
-/
import ClassFieldTheory.GroupCohomology._05_TrivialCohomology
import ClassFieldTheory.GroupCohomology._07_coind1_and_ind1
import ClassFieldTheory.Mathlib.Algebra.Category.ModuleCat.Basic
import ClassFieldTheory.Mathlib.Algebra.Module.Submodule.Range
import ClassFieldTheory.Mathlib.LinearAlgebra.Finsupp.Defs
import ClassFieldTheory.Mathlib.RepresentationTheory.Rep

/-!
# (Co)induced modules have trivial (co)homology

Let `G` be a group. We prove that `coind₁.obj A` has trivial cohomology and `ind₁.obj A` has trivial
homology.
We prove that `ind₁'.obj M` is isomorphic to `(ind₁ G).obj M.V`, and therefore has trivial homology.
Similarly we show that `coind₁'.obj M` is isomorphic to `(coind₁ G).obj M.V` and therefore has
trivial cohomology. In the case that `G` is a finite group, we show that all four of these
representations have trivial Tate cohomology.
-/

noncomputable section

open
  Finsupp
  Rep
  CategoryTheory
  groupHomology
  groupCohomology

section FINDMEINMATHLIB
variable {G S : Type} [Group G] [Group S]

@[simps snd]
/- a coset decomposition of x, acording -/
def cosetDec (φ : S →* G) (sec : G ⧸ φ.range → G) (secSpec : ∀ x, QuotientGroup.mk (sec x) = x)
    (x : G) : S × (G ⧸ φ.range) := by
  refine ⟨ ?_, (QuotientGroup.mk x)⟩
  let x' : G := sec (QuotientGroup.mk x : G ⧸ φ.range)
  let y : G := x'⁻¹ * x
  have : y ∈ φ.range := by
    apply QuotientGroup.leftRel_apply.mp
    exact Quotient.eq''.mp (secSpec ↑x)
  exact Classical.choose <| MonoidHom.mem_range.1 this

lemma cosetDecSpec {S : Type} [Group S] (φ : S →* G) (sec : G ⧸ φ.range → G)
    (secSpec : ∀ x, QuotientGroup.mk (sec x) = x) (x : G) :
    sec (cosetDec φ sec secSpec x).2 * φ (cosetDec φ sec secSpec x).1 = x := by
  apply mul_eq_of_eq_inv_mul
  -- Lean does not infer the motive by itself
  let p := fun z => (φ z = (sec ↑x)⁻¹ * x)
  apply @Classical.choose_spec _ p

lemma cosetDec_inj {S : Type} [Group S] (φ : S →* G) (sec : G ⧸ φ.range → G)
    (inj : Function.Injective φ) (secSpec : ∀ x, QuotientGroup.mk (sec x) = x ) (s : S)
    (r : G ⧸ φ.range) :
    cosetDec φ sec secSpec (sec r * φ s) = (s, r) := by
  have eq2 : (cosetDec φ sec secSpec (sec r * φ s)).2 = r := by
    calc
    _ = QuotientGroup.mk (sec r * φ s) := by simp [secSpec]
    _ = r := by simp [secSpec]
  have := cosetDecSpec φ sec secSpec (sec r * φ s)
  simp only [eq2, mul_right_inj] at this
  ext
  · exact inj this
  · exact eq2

@[simps]
def prodQuotEquiv {φ : S →* G} (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (sec_spec : ∀ g, sec g = g) : S × G ⧸ φ.range ≃ G where
  toFun p := sec p.2 * φ p.1
  invFun h := cosetDec φ sec sec_spec h
  left_inv p := by simp only [cosetDec_inj, hφ]
  right_inv h := by simp [-cosetDec_snd, cosetDecSpec]

end FINDMEINMATHLIB

variable {R G S A : Type} [CommRing R] [Group G] [Group S] {M : Rep R G} {A : ModuleCat R}

namespace Rep

def resInd₁AsFinsuppModuleIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    (G →₀ A) ≃ₗ[R] (S →₀ (G ⧸ φ.range →₀ A)) :=
  open scoped Classical in
  (Finsupp.domLCongr (prodQuotEquiv hφ sec hsec).symm).trans (Finsupp.finsuppProdLEquiv R)

def resCoind₁AsPiModuleIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) : (G → A) ≃ₗ[R] (S → G ⧸ φ.range → A) :=
  .trans (.funCongrLeft _ _ <| prodQuotEquiv hφ sec hsec) (.curry R ..)

@[simp]
theorem resInd₁AsFinsuppModuleIso_apply {φ : S →* G} (hφ : Function.Injective φ)
    (sec : G ⧸ φ.range → G) (hsec : ∀ g, sec g = g) (f : G →₀ A) (s : S) (h : G ⧸ φ.range) :
    (resInd₁AsFinsuppModuleIso φ hφ sec hsec f s h) = f (sec h * φ s) := by
  simp [resInd₁AsFinsuppModuleIso, prodQuotEquiv]

@[simp]
theorem resCoind₁AsPiModuleIso_apply {φ : S →* G} (hφ : Function.Injective φ)
    (sec : G ⧸ φ.range → G) (hsec : ∀ g, sec g = g) (f : G → A) (s : S) (h : G ⧸ φ.range) :
    resCoind₁AsPiModuleIso φ hφ sec hsec f s h = f (sec h * φ s) := rfl

def resInd₁AsFinsuppIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    ind₁AsFinsupp G A ↓ φ ≅ ind₁AsFinsupp S (.of R <| G ⧸ φ.range →₀ A) :=
  Rep.mkIso _ _ (resInd₁AsFinsuppModuleIso φ hφ sec hsec).toModuleIso fun g f ↦ by
    ext; simp [mul_assoc]

def resCoind₁AsPiIso (φ : S →* G) (hφ : Function.Injective φ) (sec : G ⧸ φ.range → G)
    (hsec : ∀ g, sec g = g) :
    coind₁AsPi G A ↓ φ ≅ coind₁AsPi S (.of R <| G ⧸ φ.range → A) :=
  Rep.mkIso _ _ (resCoind₁AsPiModuleIso φ hφ sec hsec).toModuleIso fun g f ↦ by
    ext; simp [mul_assoc]

instance trivialHomology_ind₁AsFinsupp : TrivialHomology (ind₁AsFinsupp G A) := by
  classical
  -- Let `S` be a subgroup of `G`.
  refine ⟨fun S _ φ hφ n ↦ ?_⟩
  -- The restriction to `S` of `ind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `ind₁^S (G ⧸ S →₀ A)`.
  -- By Shapiro's lemma, this has trivial homology.
  exact (isZero_of_trivialHomology ..).of_iso  <| ((groupHomology.functor _ _ _).mapIso <|
    (resInd₁AsFinsuppIso φ hφ Quotient.out (by simp)).trans (ind₁AsFinsuppIso _)).trans (indIso ..)

instance trivialCohomology_coind₁AsPi : TrivialCohomology (coind₁AsPi G A) := by
  classical
  -- Let `S` be a subgroup of `G`.
  refine ⟨fun S _ φ hφ n ↦ ?_⟩
  -- The restriction to `S` of `coind₁ᴳ A` is isomorphic (after choosing coset representatives)
  -- to `coind₁^S (G ⧸ S → A)`.
  -- By Shapiro's lemma, this has trivial cohomology.
  exact (isZero_of_trivialCohomology ..).of_iso  <| ((groupCohomology.functor _ _ _).mapIso <|
    (resCoind₁AsPiIso φ hφ Quotient.out (by simp)).trans (coind₁AsPiIso _)).trans
      (groupCohomology.coindIso ..)

instance trivialHomology_ind₁ (A : ModuleCat R) : TrivialHomology ((ind₁ G).obj A) :=
  .of_iso (ind₁AsFinsuppIso _).symm

instance trivialCohomology_coind₁ (A : ModuleCat R) : TrivialCohomology ((coind₁ G).obj A) :=
  .of_iso (coind₁AsPiIso _).symm

instance trivialHomology_ind₁' : (ind₁'.obj M).TrivialHomology :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialCohomology_coind₁' : (coind₁'.obj M).TrivialCohomology :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

variable [Finite G]

instance trivialCohomology_ind₁ : TrivialCohomology ((ind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A)

instance trivialHomology_coind₁ : TrivialHomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance trivialHomology_coind₁' : TrivialHomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

instance trivialCohomology_ind₁AsFinsupp : TrivialCohomology (ind₁AsFinsupp G A) :=
  .of_iso (ind₁AsFinsuppIso _)

instance trivialHomology_coind₁AsPi : TrivialHomology (coind₁AsPi G A) :=
  .of_iso (coind₁AsPiIso _)

unif_hint {H : Type} [Group H] (φ : H →* G) where ⊢
  ↑(coind₁'.obj M ↓ φ).V ≟ G → M.V

instance coind₁AsPi_trivialTateCohomology [Finite G] [DecidableEq G] :
    TrivialtateCohomology (Rep.coind₁AsPi G A) := by
  -- convert Rep.TrivialTateCohomology.of_iso (coind₁'_obj_iso_coind₁ M)
  apply TrivialtateCohomology.of_cases
  intro H _ _ φ hφ
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype H := @Fintype.ofFinite _ <| Finite.of_injective _ hφ
  letI : Fintype (G ⧸ φ.range) := @Fintype.ofFinite _ <| Subgroup.finite_quotient_of_finiteIndex
  constructor
  · stop
    refine Limits.IsZero.of_iso ?_ (tateCohomology.zeroIso _)
    convert @ModuleCat.isZero_of_subsingleton _ _ _ ?_
    apply Submodule.subsingleton_quotient_iff_eq_top.mpr
    rw [Submodule.submoduleOf]
    -- convert Submodule.comap_top _; swap; infer_instance
    apply SetLike.coe_injective
    simp_rw [Submodule.comap_coe, Submodule.coe_subtype, Submodule.top_coe,
      Set.preimage_eq_univ_iff, Subtype.range_coe_subtype, Representation.mem_invariants]
    intro (f : G → A) (hf : ∀ h : H, _)
    -- TODO: rename range_coe to coe_range
    simp_rw [res_obj_ρ, LinearMap.range_coe, Set.mem_range]
    use ∑ g : G ⧸ φ.range, Pi.single g.out (f g.out), ?_
    change (_ : G → A) = _
    ext x
    have h_aux (g : G ⧸ φ.range) : x⁻¹ * g.out ∈ Set.range φ ↔ ⟦x⟧ = g := by
      trans x⁻¹ * g.out ∈ φ.range
      · simp
      constructor <;> intro h
      · apply Quotient.mk_eq_iff_out.mpr (_ : QuotientGroup.leftRel _ _ _)
        rwa [QuotientGroup.leftRel_apply]
      · subst h
        rw [← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv, ← QuotientGroup.leftRel_apply]
        apply Quotient.mk_out
    calc
      _ = ∑ g : G ⧸ φ.range, ∑ s : H, (if x * φ s = g.out then f g.out else 0) := by
        simp [Representation.norm, Pi.single_apply]
        simp_rw [eq_mul_inv_iff_mul_eq]
      _ = ∑ g : G ⧸ φ.range, ∑ s ∈ Finset.univ.map ⟨φ, hφ⟩, (if s = x⁻¹ * g.out then f g.out else 0) := by
        simp_rw [Finset.sum_map, eq_inv_mul_iff_mul_eq, Function.Embedding.coeFn_mk]
      _ = ∑ g : G ⧸ φ.range, ∑ s : G, (if s = x⁻¹ * g.out then if s ∈ Set.range φ then f g.out else 0 else 0) := by
        apply Finset.sum_congr rfl fun g _ ↦ ?_
        nth_rw 1 [← Finset.univ_inter (Finset.univ.map ⟨φ, hφ⟩)]
        simp_rw [← ite_and, ← Finset.sum_ite_mem, Finset.mem_map, Finset.mem_univ,
          true_and, Function.Embedding.coeFn_mk, ← ite_and, Set.mem_range, and_comm]
      _ = _ := by
        simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        conv_lhs => enter [2, g, 1]; rw [h_aux, eq_comm]
        convert Finset.sum_ite_eq' _ _ _
        simp_rw [Finset.mem_univ, ite_true]
        replace hf := fun h ↦ congrFun (hf h)
        have (g : G) (hg : g ∈ φ.range) (a : G) : f (a * g) = f a := by
          obtain ⟨h, rfl⟩ := hg
          simpa using hf h a
        convert (this (x⁻¹ * ⟦x⟧.out) ?_ x).symm
        · simp; rfl
        · apply (h_aux _).mpr rfl
  · refine Limits.IsZero.of_iso ?_ (tateCohomology.negOneIso _)
    convert @ModuleCat.isZero_of_subsingleton _ _ _ ?_
    apply Submodule.subsingleton_quotient_iff_eq_top.mpr
    rw [Submodule.submoduleOf]
    apply SetLike.coe_injective
    simp_rw [Submodule.comap_coe, Submodule.coe_subtype, Submodule.top_coe,
      Set.preimage_eq_univ_iff, Subtype.range_coe_subtype, LinearMap.mem_ker]
    intro (f : G → A) (hf : (coind₁AsPi G A ↓ φ).ρ.norm f = (0 : G → A))
    replace hf := fun g ↦ congrFun hf g
    simp_rw [Representation.norm, res_ρ_apply, coind₁AsPi, of_ρ,
      Representation.coind₁AsPi, Pi.zero_apply, Action.res_obj_V, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coeFn_sum, Finset.sum_apply, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply, Equiv.coe_mulRight, LinearMap.funLeft_apply] at hf

    -- each single "piece" is in the kernel
    have part (g : (G ⧸ φ.range) × H) : _ ∈ Representation.Coinvariants.ker (coind₁AsPi G A ↓ φ).ρ :=
      Representation.Coinvariants.sub_mem_ker g.snd (Pi.single g.fst.out (f (g.fst.out * (φ g.snd)⁻¹)) : G → A)
    conv at part =>
      enter [g, 2]
      rw [res_obj_ρ, of_ρ, MonoidHom.coe_comp, Function.comp_apply, Representation.coind₁AsPi_single]
    change f ∈ Representation.Coinvariants.ker _
    rw [Representation.Coinvariants.ker]
    -- then their sum is in the kernel!
    convert Submodule.sum_mem _ (t := Finset.univ) (fun g _ ↦ part g)

    ext w
    rw [Finset.sum_apply]
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib]
    convert (sub_zero (f w)).symm
    · have h_aux (g : G ⧸ φ.range) : w⁻¹ * g.out ∈ Set.range φ ↔ ⟦w⟧ = g := by
        change w⁻¹ * g.out ∈ φ.range ↔ _
        constructor <;> intro h
        · apply Quotient.mk_eq_iff_out.mpr (_ : QuotientGroup.leftRel _ _ _)
          rwa [QuotientGroup.leftRel_apply]
        · subst h
          rw [← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv, ← QuotientGroup.leftRel_apply]
          apply Quotient.mk_out
      have h_iff (x : (G ⧸ φ.range) × H) :
          w = x.fst.out * (φ x.snd)⁻¹ ↔ x = (⟦w⟧, ((h_aux ⟦w⟧).mpr rfl).choose) := by
        constructor <;> rintro rfl
        · have h_quo : ⟦x.fst.out * (φ x.snd)⁻¹⟧ = x.fst := by
            apply Quotient.mk_eq_iff_out.mpr (_ : QuotientGroup.leftRel _ _ _)
            rw [QuotientGroup.leftRel_apply, mul_inv_rev, mul_assoc, inv_mul_cancel,
              mul_one, inv_inv]
            use x.snd
          ext <;> simp only
          · exact h_quo.symm
          · apply hφ
            simp_rw [((h_aux ⟦x.fst.out * (φ x.snd)⁻¹⟧).mpr rfl).choose_spec,
              h_quo, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        · have h_spec := ((h_aux ⟦w⟧).mpr rfl).choose_spec
          simp only
          rw [h_spec, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
      have h_claim : φ ((h_aux ⟦w⟧).mpr rfl).choose⁻¹ = (⟦w⟧ : G ⧸ φ.range).out⁻¹ * w := by
        rw [map_inv, ((h_aux ⟦w⟧).mpr rfl).choose_spec, mul_inv_rev, inv_inv]
      simp [Pi.single_apply, h_iff]
      simp_rw [← map_inv, h_claim, ← mul_assoc, mul_inv_cancel, one_mul]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero fun g _ ↦ ?_
      simp [Pi.single_apply, ← map_inv]
      rintro rfl
      calc
        _ = ∑ x ∈ Finset.univ.map (Equiv.inv H).toEmbedding, f (g.out * φ x) := by
          rw [Finset.sum_map]
          rfl
        _ = 0 := by
          rw [Finset.map_univ_equiv, hf g.out]

instance trivialTateCohomology_ind₁ : TrivialtateCohomology ((ind₁ G).obj A) := by
    refine .of_cases ?_
    rintro H _ _ φ hφ
    have : (ind₁ G).obj A ↓ φ ≅ ind₁AsFinsupp H (.of R <| G ⧸ φ.range →₀ A) := sorry
    constructor
    · sorry
    · sorry

instance trivialTateCohomology_coind₁ : TrivialtateCohomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance trivialTateCohomology_ind₁' : TrivialtateCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance trivialTateCohomology_coind₁' : TrivialtateCohomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

/--
The `H`-invariants of `(coind₁ G).obj A` form an representation of `G ⧸ H` with trivial cohomology.
-/
instance coind₁_quotientToInvariants_trivialCohomology (A : ModuleCat R) {Q : Type} [Group Q]
    {φ : G →* Q} (surj : Function.Surjective φ) :
    ((coind₁ G ⋙ quotientToInvariantsFunctor' surj).obj A).TrivialCohomology :=
  .of_iso (Rep.coind₁_quotientToInvariants_iso A surj)

instance coind₁'_quotientToInvariants_trivialCohomology {Q : Type} [Group Q] {φ : G →* Q}
    (surj : Function.Surjective φ) : ((coind₁'.obj M) ↑ surj).TrivialCohomology := by
  have iso := (quotientToInvariantsFunctor' surj).mapIso (coind₁'_obj_iso_coind₁ M)
  have _ : ((quotientToInvariantsFunctor' surj).obj ((coind₁ G).obj M.V)).TrivialCohomology
  · exact coind₁_quotientToInvariants_trivialCohomology M.V surj
  exact .of_iso iso

end Rep
