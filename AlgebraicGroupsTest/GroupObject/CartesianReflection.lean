/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import AlgebraicGroups.GroupObject.FunctorCategory
import AlgebraicGroups.GroupObject.CartesianReflection

open CategoryTheory MonoidalCategory

universe uC vC uJ vJ w

private theorem reflectGroupValuedDiagrams
    {C : Type uC} [cC : Category.{vC} C]
    [cartC : CartesianMonoidalCategory C]
    {J : Type uJ} [cJ : Category.{vJ} J]
    [P : CartesianMonoidalCategory (J ⥤ Type w)]
    (N : C ⥤ (J ⥤ Type w)) (hN : N.FullyFaithful) (X Y : C)
    (QX QY : J ⥤ GrpCat.{w})
    (eX : N.obj X ≅ QX ⋙ forget GrpCat)
    (eY : N.obj Y ≅ QY ⋙ forget GrpCat)
    (α : QX ⟶ QY) :
    let f : N.obj X ⟶ N.obj Y :=
      eX.hom ≫ Functor.whiskerRight α (forget GrpCat) ≫ eY.inv;
    let g : X ⟶ Y := hN.preimage (X := X) (Y := Y) f;
    ∃ (Γ0X : @GrpObj (J ⥤ Type w) _
          (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
          (N.obj X))
      (Γ0Y : @GrpObj (J ⥤ Type w) _
          (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
          (N.obj Y))
      (ΘX : @GrpObj (J ⥤ Type w) _ P (N.obj X))
      (ΘY : @GrpObj (J ⥤ Type w) _ P (N.obj Y))
      (ΓX : @GrpObj C cC cartC X) (ΓY : @GrpObj C cC cartC Y),
      Γ0X =
        @GrpObj.ofIso (J ⥤ Type w) _
          (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
          (QX ⋙ forget GrpCat) (N.obj X)
          (@CategoryTheory.Grp.grp (J ⥤ Type w) _
            (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
            (Monoidal.GrpFunctorCategory.inverseObj
              (QX ⋙ GrpTypeEquivalenceGrp.inverse))) eX.symm ∧
      Γ0Y =
        @GrpObj.ofIso (J ⥤ Type w) _
          (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
          (QY ⋙ forget GrpCat) (N.obj Y)
          (@CategoryTheory.Grp.grp (J ⥤ Type w) _
            (Functor.cartesianMonoidalCategory (J := J) (C := Type w))
            (Monoidal.GrpFunctorCategory.inverseObj
              (QY ⋙ GrpTypeEquivalenceGrp.inverse))) eY.symm ∧
      ΘX =
        (Functor.FullyFaithful.id (J ⥤ Type w)).grpObjOfCartesian
          (cartC := P)
          (cartD := Functor.cartesianMonoidalCategory
            (J := J) (C := Type w))
          (N.obj X) (Γ := Γ0X) ∧
      ΘY =
        (Functor.FullyFaithful.id (J ⥤ Type w)).grpObjOfCartesian
          (cartC := P)
          (cartD := Functor.cartesianMonoidalCategory
            (J := J) (C := Type w))
          (N.obj Y) (Γ := Γ0Y) ∧
      ΓX = hN.grpObjOfCartesian
        (cartC := cartC) (cartD := P) X (Γ := ΘX) ∧
      ΓY = hN.grpObjOfCartesian
        (cartC := cartC) (cartD := P) Y (Γ := ΘY) ∧
      ΓX.inv = hN.preimage (X := X) (Y := X) ΘX.inv ∧
      ΓY.inv = hN.preimage (X := Y) (Y := Y) ΘY.inv ∧
      (∀ (j : J) (t : (N.obj (𝟙_ C)).obj j),
        eX.hom.app j ((N.map ΓX.toMonObj.one).app j t) =
          (1 : QX.obj j)) ∧
      (∀ (j : J) (t : (N.obj (𝟙_ C)).obj j),
        eY.hom.app j ((N.map ΓY.toMonObj.one).app j t) =
          (1 : QY.obj j)) ∧
      (∀ (j : J) (x : (N.obj X).obj j),
        eX.hom.app j ((N.map ΓX.inv).app j x) =
          (eX.hom.app j x)⁻¹) ∧
      (∀ (j : J) (y : (N.obj Y).obj j),
        eY.hom.app j ((N.map ΓY.inv).app j y) =
          (eY.hom.app j y)⁻¹) ∧
      (∀ (oN : @Functor.OplaxMonoidal
          C cC cartC.toMonoidalCategory
          (J ⥤ Type w) _ P.toMonoidalCategory N),
        ΓX.toMonObj =
          @Functor.FullyFaithful.monObj
            C cC cartC.toMonoidalCategory
            (J ⥤ Type w) _ P.toMonoidalCategory N oN hN X ΘX.toMonObj ∧
        ΓY.toMonObj =
          @Functor.FullyFaithful.monObj
            C cC cartC.toMonoidalCategory
            (J ⥤ Type w) _ P.toMonoidalCategory N oN hN Y ΘY.toMonObj ∧
        (∀ (j : J) (z : (N.obj (X ⊗ X)).obj j),
          eX.hom.app j ((N.map ΓX.toMonObj.mul).app j z) =
            eX.hom.app j
              (((@Functor.OplaxMonoidal.δ
                  C cC cartC.toMonoidalCategory
                  (J ⥤ Type w) _ P.toMonoidalCategory N oN X X) ≫
                CartesianMonoidalCategory.fst (N.obj X) (N.obj X)).app j z) *
            eX.hom.app j
              (((@Functor.OplaxMonoidal.δ
                  C cC cartC.toMonoidalCategory
                  (J ⥤ Type w) _ P.toMonoidalCategory N oN X X) ≫
                CartesianMonoidalCategory.snd (N.obj X) (N.obj X)).app j z)) ∧
        (∀ (j : J) (z : (N.obj (Y ⊗ Y)).obj j),
          eY.hom.app j ((N.map ΓY.toMonObj.mul).app j z) =
            eY.hom.app j
              (((@Functor.OplaxMonoidal.δ
                  C cC cartC.toMonoidalCategory
                  (J ⥤ Type w) _ P.toMonoidalCategory N oN Y Y) ≫
                CartesianMonoidalCategory.fst (N.obj Y) (N.obj Y)).app j z) *
            eY.hom.app j
              (((@Functor.OplaxMonoidal.δ
                  C cC cartC.toMonoidalCategory
                  (J ⥤ Type w) _ P.toMonoidalCategory N oN Y Y) ≫
                CartesianMonoidalCategory.snd (N.obj Y) (N.obj Y)).app j z))) ∧
      @IsMonHom (J ⥤ Type w) _ P.toMonoidalCategory (N.obj X) (N.obj Y)
        ΘX.toMonObj ΘY.toMonObj f ∧
      @IsMonHom C cC cartC.toMonoidalCategory X Y
        ΓX.toMonObj ΓY.toMonObj g ∧
      N.map g = f ∧
      N.map g ≫ eY.hom =
        eX.hom ≫ Functor.whiskerRight α (forget GrpCat) ∧
      (∀ (j : J) (x : (N.obj X).obj j),
        eY.hom.app j ((N.map g).app j x) =
          (α.app j) (eX.hom.app j x)) ∧
      (∀ (g' : X ⟶ Y),
        N.map g' ≫ eY.hom =
          eX.hom ≫ Functor.whiskerRight α (forget GrpCat) →
        g' = g)
 := by
  let D := J ⥤ Type w
  let P0 : CartesianMonoidalCategory D :=
    Functor.cartesianMonoidalCategory (J := J) (C := Type w)
  let m0 := P0.toMonoidalCategory
  let mP := P.toMonoidalCategory
  let mC := cartC.toMonoidalCategory
  -- These ordinary functions select parents; they install no instances.
  let mon0 {A : D} (S : @GrpObj D _ P0 A) : @MonObj D _ m0 A :=
    @GrpObj.toMonObj D _ P0 A S
  let monP {A : D} (S : @GrpObj D _ P A) : @MonObj D _ mP A :=
    @GrpObj.toMonObj D _ P A S
  let monC {A : C} (S : @GrpObj C cC cartC A) : @MonObj C cC mC A :=
    @GrpObj.toMonObj C cC cartC A S
  let I : D ⥤ D := 𝟭 D
  let hI := Functor.FullyFaithful.id D
  let oI : @Functor.OplaxMonoidal D _ mP D _ m0 I :=
    @Functor.OplaxMonoidal.ofChosenFiniteProducts D _ P D _ P0 I
  let oN0 : @Functor.OplaxMonoidal C cC mC D _ mP N :=
    @Functor.OplaxMonoidal.ofChosenFiniteProducts C cC cartC D _ P N
  -- The two directions use exactly the transported monoid parent. This helper has
  -- separate endpoint variables, even when later specialized to equal objects.
  have hIso (A B : D) (S : @GrpObj D _ P0 A) (k : A ≅ B) :
      @IsMonHom D _ m0 A B (mon0 S)
        (mon0 (@GrpObj.ofIso D _ P0 A B S k)) k.hom ∧
      @IsMonHom D _ m0 B A
        (mon0 (@GrpObj.ofIso D _ P0 A B S k)) (mon0 S) k.inv := by
    let : CartesianMonoidalCategory D := P0
    let : MonoidalCategory D := m0
    let : @GrpObj D _ P0 A := S
    let : @GrpObj D _ P0 B := @GrpObj.ofIso D _ P0 A B S k
    have hk : @IsMonHom D _ m0 A B (mon0 S)
        (mon0 (@GrpObj.ofIso D _ P0 A B S k)) k.hom := isMonHom_ofIso k
    let : @IsMonHom D _ m0 A B (mon0 S)
        (mon0 (@GrpObj.ofIso D _ P0 A B S k)) k.hom := hk
    exact ⟨hk, inferInstance⟩
  -- Product projections below use the given Cartesian structure, not P0.
  let : CartesianMonoidalCategory D := P
  -- One calculation is shared by the two independently supplied endpoints.
  -- All lets in this type are ordinary data; none installs an instance.
  have hEndpoint (A : C) (Q : J ⥤ GrpCat.{w})
      (e : N.obj A ≅ Q ⋙ forget GrpCat) :
      let S := Monoidal.GrpFunctorCategory.inverseObj
        (Q ⋙ GrpTypeEquivalenceGrp.inverse);
      let s : @GrpObj D _ P0 (Q ⋙ forget GrpCat) :=
        @CategoryTheory.Grp.grp D _ P0 S;
      let Δ0 : @GrpObj D _ P0 (N.obj A) :=
        @GrpObj.ofIso D _ P0 (Q ⋙ forget GrpCat) (N.obj A) s e.symm;
      let Δ : @GrpObj D _ P (N.obj A) :=
        hI.grpObjOfCartesian (cartC := P) (cartD := P0) (N.obj A) (Γ := Δ0);
      let R : @GrpObj C cC cartC A :=
        hN.grpObjOfCartesian (cartC := cartC) (cartD := P) A (Γ := Δ);
      (∀ (j : J) (t : (N.obj (𝟙_ C)).obj j),
        e.hom.app j ((N.map (@MonObj.one C cC mC A (monC R))).app j t) =
          (1 : Q.obj j)) ∧
      (∀ (j : J) (x : (N.obj A).obj j),
        e.hom.app j ((N.map (@GrpObj.inv C cC cartC A R)).app j x) =
          (e.hom.app j x)⁻¹) ∧
      (∀ (oN : @Functor.OplaxMonoidal C cC mC D _ mP N),
        monC R =
          @Functor.FullyFaithful.monObj C cC mC D _ mP N oN hN A (monP Δ) ∧
        ∀ (j : J) (z : (N.obj (A ⊗ A)).obj j),
          e.hom.app j ((N.map (@MonObj.mul C cC mC A (monC R))).app j z) =
            e.hom.app j
              (((@Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A) ≫
                CartesianMonoidalCategory.fst (N.obj A) (N.obj A)).app j z) *
            e.hom.app j
              (((@Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A) ≫
                CartesianMonoidalCategory.snd (N.obj A) (N.obj A)).app j z)) := by
    let S := Monoidal.GrpFunctorCategory.inverseObj
      (Q ⋙ GrpTypeEquivalenceGrp.inverse)
    let s : @GrpObj D _ P0 (Q ⋙ forget GrpCat) :=
      @CategoryTheory.Grp.grp D _ P0 S
    let Δ0 : @GrpObj D _ P0 (N.obj A) :=
      @GrpObj.ofIso D _ P0 (Q ⋙ forget GrpCat) (N.obj A) s e.symm
    let Δ : @GrpObj D _ P (N.obj A) :=
      hI.grpObjOfCartesian (cartC := P) (cartD := P0) (N.obj A) (Γ := Δ0)
    let R : @GrpObj C cC cartC A :=
      hN.grpObjOfCartesian (cartC := cartC) (cartD := P) A (Γ := Δ)
    change
      (∀ (j : J) (t : (N.obj (𝟙_ C)).obj j),
        e.hom.app j ((N.map (@MonObj.one C cC mC A (monC R))).app j t) =
          (1 : Q.obj j)) ∧
      (∀ (j : J) (x : (N.obj A).obj j),
        e.hom.app j ((N.map (@GrpObj.inv C cC cartC A R)).app j x) =
          (e.hom.app j x)⁻¹) ∧
      (∀ (oN : @Functor.OplaxMonoidal C cC mC D _ mP N),
        monC R =
          @Functor.FullyFaithful.monObj C cC mC D _ mP N oN hN A (monP Δ) ∧
        ∀ (j : J) (z : (N.obj (A ⊗ A)).obj j),
          e.hom.app j ((N.map (@MonObj.mul C cC mC A (monC R))).app j z) =
            e.hom.app j
              (((@Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A) ≫
                CartesianMonoidalCategory.fst (N.obj A) (N.obj A)).app j z) *
            e.hom.app j
              (((@Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A) ≫
                CartesianMonoidalCategory.snd (N.obj A) (N.obj A)).app j z))
    have he : @IsMonHom D _ m0 (N.obj A) (Q ⋙ forget GrpCat)
        (mon0 Δ0) (mon0 s) e.hom := (hIso _ _ s e.symm).2
    have hΔ : monP Δ =
        @Functor.FullyFaithful.monObj D _ mP D _ m0 I oI hI (N.obj A) (mon0 Δ0) :=
      hI.grpObjOfCartesian_toMonObj (cartC := P) (cartD := P0)
        (oF := oI) (N.obj A) (Γ := Δ0)
    have hR (oN : @Functor.OplaxMonoidal C cC mC D _ mP N) : monC R =
        @Functor.FullyFaithful.monObj C cC mC D _ mP N oN hN A (monP Δ) :=
      hN.grpObjOfCartesian_toMonObj (cartC := cartC) (cartD := P)
        (oF := oN) A (Γ := Δ)
    have hΔone : @MonObj.one D _ mP (N.obj A) (monP Δ) =
        (@Functor.OplaxMonoidal.η D _ mP D _ m0 I oI) ≫
          @MonObj.one D _ m0 (N.obj A) (mon0 Δ0) := by
      rw [congrArg (fun M : @MonObj D _ mP (N.obj A) =>
        @MonObj.one D _ mP (N.obj A) M) hΔ]
      change hI.preimage
        ((@Functor.OplaxMonoidal.η D _ mP D _ m0 I oI) ≫
          @MonObj.one D _ m0 (N.obj A) (mon0 Δ0)) = _
      simpa only [Functor.id_map] using
        hI.map_preimage
          ((@Functor.OplaxMonoidal.η D _ mP D _ m0 I oI) ≫
            @MonObj.one D _ m0 (N.obj A) (mon0 Δ0))
    have hΔmul : @MonObj.mul D _ mP (N.obj A) (monP Δ) =
        (@Functor.OplaxMonoidal.δ D _ mP D _ m0 I oI (N.obj A) (N.obj A)) ≫
          @MonObj.mul D _ m0 (N.obj A) (mon0 Δ0) := by
      rw [congrArg (fun M : @MonObj D _ mP (N.obj A) =>
        @MonObj.mul D _ mP (N.obj A) M) hΔ]
      change hI.preimage
        ((@Functor.OplaxMonoidal.δ D _ mP D _ m0 I oI (N.obj A) (N.obj A)) ≫
          @MonObj.mul D _ m0 (N.obj A) (mon0 Δ0)) = _
      simpa only [Functor.id_map] using
        hI.map_preimage
          ((@Functor.OplaxMonoidal.δ D _ mP D _ m0 I oI (N.obj A) (N.obj A)) ≫
            @MonObj.mul D _ m0 (N.obj A) (mon0 Δ0))
    have hΔinv : @GrpObj.inv D _ P (N.obj A) Δ =
        @GrpObj.inv D _ P0 (N.obj A) Δ0 := by
      rw [hI.grpObjOfCartesian_inv (cartC := P) (cartD := P0)
        (N.obj A) (Γ := Δ0)]
      simpa only [Functor.id_map] using
        hI.map_preimage (@GrpObj.inv D _ P0 (N.obj A) Δ0)
    have hmapOne (oN : @Functor.OplaxMonoidal C cC mC D _ mP N) :
        N.map (@MonObj.one C cC mC A (monC R)) =
          (@Functor.OplaxMonoidal.η C cC mC D _ mP N oN) ≫
            @MonObj.one D _ mP (N.obj A) (monP Δ) := by
      rw [congrArg (fun M : @MonObj C cC mC A =>
        @MonObj.one C cC mC A M) (hR oN)]
      exact hN.map_preimage _
    have hmapMul (oN : @Functor.OplaxMonoidal C cC mC D _ mP N) :
        N.map (@MonObj.mul C cC mC A (monC R)) =
          (@Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A) ≫
            @MonObj.mul D _ mP (N.obj A) (monP Δ) := by
      rw [congrArg (fun M : @MonObj C cC mC A =>
        @MonObj.mul C cC mC A M) (hR oN)]
      exact hN.map_preimage _
    have hmapInv : N.map (@GrpObj.inv C cC cartC A R) =
        @GrpObj.inv D _ P0 (N.obj A) Δ0 := by
      rw [hN.grpObjOfCartesian_inv (cartC := cartC) (cartD := P) A (Γ := Δ),
        hN.map_preimage, hΔinv]
    refine ⟨?_, ?_, ?_⟩
    · intro j t
      rw [hmapOne oN0, hΔone]
      have h := congrArg
        (fun k => k.app j
          (((@Functor.OplaxMonoidal.η D _ mP D _ m0 I oI).app j)
            (((@Functor.OplaxMonoidal.η C cC mC D _ mP N oN0).app j) t)))
        (@IsMonHom.one_hom D _ m0 (N.obj A) (Q ⋙ forget GrpCat)
          (mon0 Δ0) (mon0 s) e.hom he)
      -- The supplied conversion's unit component is the given bundled group's unit.
      exact h
    · intro j x
      rw [hmapInv]
      have h := congrArg (fun k => k.app j x)
        (@GrpObj.inv_hom D _ P0 (N.obj A) (Q ⋙ forget GrpCat)
          Δ0 s e.hom he)
      -- Its inverse component is likewise the supplied inverse, on the same carrier.
      exact h
    · intro oN
      refine ⟨hR oN, ?_⟩
      intro j z
      rw [hmapMul oN, hΔmul]
      let δ := @Functor.OplaxMonoidal.δ C cC mC D _ mP N oN A A
      let κ := @Functor.OplaxMonoidal.δ D _ mP D _ m0 I oI (N.obj A) (N.obj A)
      have h := congrArg (fun k => k.app j ((κ.app j) ((δ.app j) z)))
        (@IsMonHom.mul_hom D _ m0 (N.obj A) (Q ⋙ forget GrpCat)
          (mon0 Δ0) (mon0 s) e.hom he)
      -- Only after κ does the input belong to the pointwise product.
      change
        e.hom.app j
            ((@MonObj.mul D _ m0 (N.obj A) (mon0 Δ0)).app j
              ((κ.app j) ((δ.app j) z))) =
          e.hom.app j ((κ.app j ((δ.app j) z)).1) *
            e.hom.app j ((κ.app j ((δ.app j) z)).2) at h
      have hp := @Functor.OplaxMonoidal.δ_fst D _ P D _ P0 I oI
        (N.obj A) (N.obj A)
      have hq := @Functor.OplaxMonoidal.δ_snd D _ P D _ P0 I oI
        (N.obj A) (N.obj A)
      have hpj := congrArg (fun k => k.app j ((δ.app j) z)) hp
      have hqj := congrArg (fun k => k.app j ((δ.app j) z)) hq
      change (κ.app j ((δ.app j) z)).1 =
        (CartesianMonoidalCategory.fst (N.obj A) (N.obj A)).app j ((δ.app j) z)
        at hpj
      change (κ.app j ((δ.app j) z)).2 =
        (CartesianMonoidalCategory.snd (N.obj A) (N.obj A)).app j ((δ.app j) z)
        at hqj
      rw [hpj, hqj] at h
      exact h
  let SX := Monoidal.GrpFunctorCategory.inverseObj (QX ⋙ GrpTypeEquivalenceGrp.inverse)
  let SY := Monoidal.GrpFunctorCategory.inverseObj (QY ⋙ GrpTypeEquivalenceGrp.inverse)
  let sX : @GrpObj D _ P0 (QX ⋙ forget GrpCat) :=
    @CategoryTheory.Grp.grp D _ P0 SX
  let sY : @GrpObj D _ P0 (QY ⋙ forget GrpCat) :=
    @CategoryTheory.Grp.grp D _ P0 SY
  let Γ0X : @GrpObj D _ P0 (N.obj X) :=
    @GrpObj.ofIso D _ P0 (QX ⋙ forget GrpCat) (N.obj X) sX eX.symm
  let Γ0Y : @GrpObj D _ P0 (N.obj Y) :=
    @GrpObj.ofIso D _ P0 (QY ⋙ forget GrpCat) (N.obj Y) sY eY.symm
  let ΘX : @GrpObj D _ P (N.obj X) :=
    hI.grpObjOfCartesian (cartC := P) (cartD := P0) (N.obj X) (Γ := Γ0X)
  let ΘY : @GrpObj D _ P (N.obj Y) :=
    hI.grpObjOfCartesian (cartC := P) (cartD := P0) (N.obj Y) (Γ := Γ0Y)
  let ΓX : @GrpObj C cC cartC X :=
    hN.grpObjOfCartesian (cartC := cartC) (cartD := P) X (Γ := ΘX)
  let ΓY : @GrpObj C cC cartC Y :=
    hN.grpObjOfCartesian (cartC := cartC) (cartD := P) Y (Γ := ΘY)
  let a := Functor.whiskerRight α (forget GrpCat)
  let f : N.obj X ⟶ N.obj Y := eX.hom ≫ a ≫ eY.inv
  let g : X ⟶ Y := hN.preimage (X := X) (Y := Y) f
  have hX := hEndpoint X QX eX
  have hY := hEndpoint Y QY eY
  -- This is the existing conversion's map, retaining the actual alpha components.
  let b := (Monoidal.GrpFunctorCategory.inverse (C := J) (D := Type w)).map
    (Functor.whiskerRight α GrpTypeEquivalenceGrp.inverse)
  let BX := @CategoryTheory.Grp.toMon D _ P0 SX
  let BY := @CategoryTheory.Grp.toMon D _ P0 SY
  let bm : @Mon.Hom D _ m0 BX BY := by
    -- This local parent choice is confined to extracting b's stored monoid hom.
    letI : CartesianMonoidalCategory D := P0
    letI : MonoidalCategory D := m0
    exact b.hom
  have hb : @Mon.Hom.hom D _ m0 BX BY bm = a := by
    ext j x
    rfl
  have ha : @IsMonHom D _ m0 (QX ⋙ forget GrpCat) (QY ⋙ forget GrpCat)
      (mon0 sX) (mon0 sY) a := by
    rw [← hb]
    exact @Mon.Hom.isMonHom_hom D _ m0 BX BY bm
  have heX : @IsMonHom D _ m0 (N.obj X) (QX ⋙ forget GrpCat)
      (mon0 Γ0X) (mon0 sX) eX.hom := (hIso _ _ sX eX.symm).2
  have heY : @IsMonHom D _ m0 (QY ⋙ forget GrpCat) (N.obj Y)
      (mon0 sY) (mon0 Γ0Y) eY.inv := (hIso _ _ sY eY.symm).1
  have hf0 : @IsMonHom D _ m0 (N.obj X) (N.obj Y)
      (mon0 Γ0X) (mon0 Γ0Y) f := by
    exact @instIsMonHomComp D _ m0 (N.obj X) (QX ⋙ forget GrpCat) (N.obj Y)
      (mon0 Γ0X) (mon0 sX) (mon0 Γ0Y) eX.hom (a ≫ eY.inv) heX
      (@instIsMonHomComp D _ m0 (QX ⋙ forget GrpCat) (QY ⋙ forget GrpCat) (N.obj Y)
        (mon0 sX) (mon0 sY) (mon0 Γ0Y) a eY.inv ha heY)
  have hΘX : monP ΘX =
      @Functor.FullyFaithful.monObj D _ mP D _ m0 I oI hI (N.obj X) (mon0 Γ0X) :=
    hI.grpObjOfCartesian_toMonObj (cartC := P) (cartD := P0)
      (oF := oI) (N.obj X) (Γ := Γ0X)
  have hΘY : monP ΘY =
      @Functor.FullyFaithful.monObj D _ mP D _ m0 I oI hI (N.obj Y) (mon0 Γ0Y) :=
    hI.grpObjOfCartesian_toMonObj (cartC := P) (cartD := P0)
      (oF := oI) (N.obj Y) (Γ := Γ0Y)
  have hf : @IsMonHom D _ mP (N.obj X) (N.obj Y)
      (monP ΘX) (monP ΘY) f := by
    rw [hΘX, hΘY]
    have h := @Functor.FullyFaithful.isMonHom_preimage_monObj
      D _ mP D _ m0 I oI hI (N.obj X) (N.obj Y) (mon0 Γ0X) (mon0 Γ0Y) f hf0
    have hid : hI.preimage f = f := by
      simpa only [Functor.id_map] using hI.map_preimage f
    simpa only [hid] using h
  have hg : @IsMonHom C cC mC X Y (monC ΓX) (monC ΓY) g := by
    rw [(hX.2.2 oN0).1, (hY.2.2 oN0).1]
    exact @Functor.FullyFaithful.isMonHom_preimage_monObj
      C cC mC D _ mP N oN0 hN X Y (monP ΘX) (monP ΘY) f hf
  have hmap : N.map g = f := hN.map_preimage f
  have hsquare : N.map g ≫ eY.hom = eX.hom ≫ a := by
    rw [hmap]
    dsimp only [f]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have haapp (j : J) : a.app j = (forget GrpCat).map (α.app j) := by
    change (Functor.whiskerRight α (forget GrpCat)).app j = _
    rw [← Functor.hcomp_id]
    exact NatTrans.hcomp_id_app α j
  refine ⟨Γ0X, Γ0Y, ΘX, ΘY, ΓX, ΓY,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hX.1, hY.1, hX.2.1, hY.2.1,
    ?_, hf, hg, hmap, hsquare, ?_, ?_⟩
  · exact hN.grpObjOfCartesian_inv (cartC := cartC) (cartD := P) X (Γ := ΘX)
  · exact hN.grpObjOfCartesian_inv (cartC := cartC) (cartD := P) Y (Γ := ΘY)
  · intro oN
    exact ⟨(hX.2.2 oN).1, (hY.2.2 oN).1, (hX.2.2 oN).2, (hY.2.2 oN).2⟩
  · intro j x
    have h := congrArg (fun k => k.app j x) hsquare
    change eY.hom.app j ((N.map g).app j x) = a.app j (eX.hom.app j x) at h
    rw [haapp] at h
    exact h
  · intro g' h'
    apply hN.map_injective
    have h := congrArg (fun k => k ≫ eY.inv) (h'.trans hsquare.symm)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-!
# Reflecting supplied group-valued diagrams

The construction on the given representing objects retains the supplied group operations
and the given natural transformation. An identity-functor reflection first changes from
the pointwise Cartesian structure to the given Cartesian structure. The comparison formulas
retain each supplied Oplax structure and its projections.

This use follows Mathlib's Type-group and monoid-functor-category conversions and
`AlgebraicGroups.GroupObject.FunctorCategory`, and uses fully faithful Cartesian group
reflection through its monoid-parent and inverse characteristics.
-/
