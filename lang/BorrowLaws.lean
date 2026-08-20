import Lang.Abstractions

open Iris Std ProgramLogic Statement


variable [BorrowGS hlc GF]
variable {s : Stuckness} {φ : Unit -> IProp GF}
variable {b : Block} {k : Kontinuation}


theorem wp_move (L L' : Location) (HMov : Typ.Movable τ) :
  ▷ L ↦ v -∗
  ▷ ⟦τ⟧ L' -∗
  ▷ (⟦τ⟧ L -∗ (∃ v, L' ↦ v) -∗ WP (b, k) @ s; N {{ φ }}) -∗
  WP (sb(L := copy L'; b), k) @ s; N {{ φ }}
:= by
  iintro >HL >HL' Hφ
  ihave ⟨%v, HL', Hv⟩ := split_movable _ HMov $$ HL'

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ HL'
  iintro !> HL'

  iapply Statement.wp_assign $$ HL
  iintro !> HL

  iapply Hφ $$ [Hv HL] [HL']
  · iapply split_movable
    iexists _
    iframe
  · iexists _
    iframe

-- admittedly, this lemma is a bit useless
theorem wp_move' (L : Location) (HMov : τ.Movable) :
  ▷ ⟦τ⟧ L -∗
  ▷ (⟦τ⟧ L -∗ WP (b, k) @s; N {{ φ }}) -∗
  WP (sb(L := copy L; b), k) @ s; N {{ φ }}
:= by
  iintro >HL Hφ
  ihave ⟨%v, HL, Hv⟩ := split_movable _ HMov $$ HL

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ HL
  iintro !> HL

  iapply Statement.wp_assign $$ HL
  iintro !> HL

  iapply Hφ
  iapply split_movable
  iexists v
  iframe


theorem wp_brw (L L' : Location) :
  ▷ L ↦ v -∗
  ▷ ⟦τ⟧ L' -∗
  ▷ (∀ l, ⟦.MB l τ⟧ L -∗ ⟦.ML l T⟧ L' -∗ inv N (I l) -∗ WP (b, k) @ s; N {{ φ }}) -∗
  WP (sb(L := L'; b), k) @ s; N {{ φ }}
:= by
  iintro HL HL' Hwp
  iapply Statement.wp_assign $$ HL
  iintro !> HL

  iapply fupd_wp
  ihave >⟨%l, HL, HL', HI⟩ := brw_alloc $$ [HL' HL]
  · iframe
    unfold basicTimelessConstraint
    ipureintro
    infer_instance
  imodintro

  simp [Typ.interp]
  iapply Hwp $$ HL HL' HI


-- let pi : &mut int // L
-- let x // L'
-- x = *pi
-- now x : int
theorem wp_brw_copy (L L' : Location) :
  ▷ L ↦ v -∗
  ▷ ⟦.MB l .Int⟧ L' -∗
  inv N (I l) -∗
  ▷ (⟦.MB l .Int⟧ L' -∗ ⟦.Int⟧ L -∗ WP (b, k) @ s; N {{ φ }}) -∗
  WP (sb(L := copy *L'; b), k) @ s; N {{ φ }}
:= by
  unfold Typ.interp
  iintro HL >HL' #HI Hwp
  iapply fupd_wp
  ihave >⟨%L0', ⟨HL0', HL', HC, Hacc⟩⟩ := brw_open $$ HI HL'
  imodintro

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_place' .Copy
  iapply Place.wp_deref $$ HL'
  iintro !> HL'

  simp [Typ.interp]; icases HL0' with ⟨%i, HL0'⟩
  iapply RValue.wp_copy $$ HL0'
  iintro !> HL0'
  simp!

  iapply Statement.wp_assign (v := .Int _) $$ HL
  iintro !> HL
  iapply fupd_wp
  imod Hacc $$ %⟦.Int⟧ [HL' HL0']
  · iframe
    isplitl [HL0']; simp!; iexists _; iassumption
    unfold basicTimelessConstraint; ipureintro; infer_instance
  imodintro
  simp [Typ.interp]
  iapply Hwp $$ Hacc [HL]
  iexists _; iassumption



theorem wp_brw_mut :
  ▷ ⟦.MB l .Int⟧ L -∗
  inv N (I l) -∗
  ▷ (⟦.MB l .Int⟧ L -∗ WP (b, k) @ s; N {{ φ }}) -∗
  WP (sb(*L := int i; b), k) @ s; N {{ φ }}
:= by
  iintro >HL #HI Hwp
  simp [Typ.interp]

  iapply fupd_wp
  ihave >⟨%L', ⟨⟨%_, HL'⟩, HL, HC, Hacc⟩⟩ := brw_open $$ HI HL
  imodintro

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ HL
  iintro !> HL

  iapply Statement.wp_assign (v := .Int _) $$ HL'
  iintro !> HL'

  iapply fupd_wp
  imod Hacc $$ %⟦.Int⟧ [HL' HL]
  · iframe
    isplitl [HL']; simp!; iexists i; iassumption
    unfold basicTimelessConstraint; ipureintro; infer_instance
  imodintro
  simp [Typ.interp]
  iapply Hwp $$ Hacc





theorem wp_rebrw :
  ▷ L' ↦ v -∗
  ▷ ⟦.MB l τ⟧ L -∗
  inv N (I l) -∗
  ▷ (∀ l', ⟦.MB l (.ML l' T)⟧ L -∗ ⟦.MB l' τ⟧ L' -∗ inv N (I l') -∗ WP (b, k) @ s; N {{ φ }}) -∗
  WP (sb(L' := copy L; b), k) @ s; N {{ φ }}
:= by
  unfold Typ.interp
  iintro HL' >HL HI Hwp

  iapply fupd_wp
  ihave >⟨%L0, HL0, HL, HC, Hacc⟩ := brw_open $$ HI HL
  imodintro

  iapply Statement.wp_rvalue' (RCi := .Assign _)
  iapply RValue.wp_copy $$ HL
  iintro !> HL

  iapply Statement.wp_assign $$ HL'
  iintro !> HL'

  iapply fupd_wp
  ihave >⟨%l', HL', HL0, HI'⟩ := brw_alloc $$ [HL0 HL']
  · iframe
    unfold basicTimelessConstraint
    ipureintro
    infer_instance
  imod Hacc $$ %(ML l') [HL0 HL]
  · iframe
    iintro %_ -
    rw [basicTimelessConstraint]
    ipureintro
    infer_instance
  imodintro

  simp [Typ.interp]
  iapply Hwp $$ Hacc HL' HI'




-- // b ↦ Bool, x ↦ MB lx Int, y ↦ MB ly Int
-- if b {
--   z := x
--   // b ↦ True, x ↦ ⊥, y ↦ MB ly Int, z ↦ MB lx Int
-- } else {
--   z := y
--   // b ↦ False, x ↦ MB lx Int, y ↦ ⊥, z ↦ MB ly Int
-- }
-- // b ↦ Bool, z ↦ MB l Int, A { MB lx Int, MB ly Int, ML l }, x ↦ ⊥, y ↦ ⊥
-- there is no notion of move at the base language, so we copy isntead
-- theorem test (b : Bool) :
--   ⟦.Bool⟧ Lb ∗ ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ Lz ↦ v ⊢
--   WP ↑(s(if b then Lz := copy Lx else Lz := copy Ly) : Configuration) @ s; N
--   {{__, ∃ lz, ⟦.Bool⟧ Lb ∗ ⟦.MB lz .Int⟧ Lz ∗
--     (∃ τ, ⟦.MB lz τ⟧ Lz -∗ (∃ Lx, ⟦.MB lx .Int⟧ Lx) ∗ (∃ Ly, ⟦.MB ly .Int⟧ Ly))}}
-- := by
--   iintro ⟨Hb, Hx, Hy, Hz⟩
--   cases b
--   · iapply Statement.wp_IfThenElseFalse
--     inext
--     iapply wp_wand $$ [Hy Hz]
--     iapply wp_move_MB $$ Hz Hy
--     iintro %_ Hz
--     iexists _
--     iframe
--     iexists .Int
--     iintro _
--     isplitl [Hx]; iexists _; iassumption
--     iexists _; iassumption
--   · iapply Statement.wp_IfThenElseTrue
--     inext
--     iapply wp_wand $$ [Hx Hz]
--     iapply wp_move_MB $$ Hz Hx
--     iintro %_ Hz
--     iexists lx
--     iframe
--     iexists .Int
--     iintro _
--     isplitr [Hy]; iexists _; iassumption
--     iexists _; iassumption




-- // b ↦ Bool, x ↦ MB lx Int, y ↦ MB ly Int, x' ↦ ML lx, y' ↦ ML ly
-- if b {
--   z := x
--   // b ↦ True, x ↦ MB lx (ML lz), y ↦ MB ly Int, z ↦ MB lz Int
-- } else {
--   z := y
--   // b ↦ True, x ↦ MB lx Int, y ↦ MB ly (ML lz), z ↦ MB lz Int
-- }
-- // b ↦ Bool, z ↦ MB l Int, A { MB lx Int, MB ly Int, ML l }, x ↦ ⊥, y ↦ ⊥
-- there is no notion of move at the base language, so we copy isntead
-- theorem test1 (b : Bool) :
--   ⟦.Bool⟧ Lb ∗ ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ Lz ↦ v ⊢
--   WP ↑(s(if b then Lz := copy Lx else Lz := copy Ly) : Configuration) @ s; N
--   {{__, ∃ lz, ⟦.Bool⟧ Lb ∗ ⟦.MB lz .Int⟧ Lz ∗
--     ((∃ τ Lz, ⟦.MB lz τ⟧ Lz) ={N}=∗ (∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly))}}
-- -- can even be strengthened to
-- -- (∀ τ, ⟦.MB lz τ⟧ Lz ={N}=∗ Lz ↦ (-:Location) ∗ (∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly)))
-- := by
--   iintro ⟨Hb, Hx, Hy, #HIx, #HIy, Hz⟩
--   cases b
--   · iapply Statement.wp_IfThenElseFalse
--     inext
--     iapply wp_wand $$ [Hy HIy Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hy HIy
--     iintro %_ ⟨%lz, Hy, Hz, #HIz⟩
--     iexists lz
--     iframe
--     iintro ⟨%τ, %Lz, Hz⟩
--     ihave >⟨Hy, HLz⟩ := brw_rebrw_end (l := ly) (l' := lz) (P := ⟦τ⟧) $$ [HIy HIz] [Hy Hz]
--     · iintro %_ %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     · isplitl []; iassumption; iassumption
--     · simp [Typ.interp]; iframe
--     imodintro
--     isplitl [Hx]; iexists _, _; iassumption
--     iexists _, _; unfold Typ.interp; iassumption
--   · iapply Statement.wp_IfThenElseTrue
--     inext
--     iapply wp_wand $$ [Hx HIy Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hx HIx
--     iintro %_ ⟨%lz, Hx, Hz, #HIz⟩
--     iexists lz
--     iframe
--     iintro ⟨%τ, %Lz, Hz⟩
--     ihave >⟨Hx, HLz⟩ := brw_rebrw_end (l := lx) (l' := lz) (P := ⟦τ⟧) $$ [HIx HIz] [Hx Hz]
--     · iintro %_ %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     · isplitl []; iassumption; iassumption
--     · simp [Typ.interp]; iframe
--     imodintro
--     isplitl [Hx]; iexists _, _; unfold Typ.interp; iassumption
--     iexists _, _; iassumption



-- theorem test2 (b : Bool) :
--   ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ Lz ↦ v ⊢
--   WP ↑(s(if b then Lz := copy Lx else Lz := copy Ly) : Configuration) @s; N
--   {{__, ∃ lz, ⟦.MB lz .Int⟧ Lz ∗
--     |={N}=> (∃ Lz, ⟦.ML lz .Int⟧ Lz ∗ (⟦.ML lz .Int⟧ Lz ={N}=∗ ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly))))}}
-- := by
--   iintro ⟨Hx, Hy, #HIx, #HIy, Hz⟩
--   cases b
--   · iapply Statement.wp_IfThenElseFalse
--     inext
--     iapply wp_wand $$ [Hy HIy Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hy HIy
--     iintro %_ ⟨%lz, Hy, Hz, #HIz⟩
--     iexists lz
--     iframe
--     ihave >⟨%Lz', Hz, HLy, HC, Hacc⟩ := brw_open (l := ly) $$ [HIy] [Hy]; iassumption; simp [Typ.interp]; iassumption
--     imodintro
--     iexists Lz'
--     isplitl [Hz]; unfold Typ.interp; iassumption
--     iintro Hz
--     imod Hacc $$ %⟦.ML lz .Int⟧ [Hz HLy]
--     · iframe
--       iintro %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     isplitl [Hx]; iexists _, _; iassumption
--     iexists _, _; unfold Typ.interp; iassumption
--   · iapply Statement.wp_IfThenElseTrue
--     inext
--     iapply wp_wand $$ [Hx HIx Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hx HIx
--     iintro %_ ⟨%lz, Hx, Hz, #HIz⟩
--     iexists lz
--     iframe
--     ihave >⟨%Lz', Hz, HLx, HC, Hacc⟩ := brw_open (l := lx) $$ [HIx] [Hx]; iassumption; simp [Typ.interp]; iassumption
--     imodintro
--     iexists Lz'
--     isplitl [Hz]; unfold Typ.interp; iassumption
--     iintro Hz
--     imod Hacc $$ %⟦.ML lz .Int⟧ [Hz HLx]
--     · iframe
--       iintro %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     isplitl [Hacc]; iexists _, _; unfold Typ.interp; iassumption
--     iexists _, _; iassumption

-- theorem test3 :
--   iprop(|={N}=> (∃ Lz, ⟦.ML lz .Int⟧ Lz ∗ (⟦.ML lz .Int⟧ Lz ={N}=∗ ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly))))) ⊢
--   |={N}=> ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly))
-- := by
--   iintro >⟨%Lz, Hz, H⟩
--   imod H $$ [Hz]; iassumption
--   iassumption


-- this one is a bit odd, we just threw out some info
-- theorem test4 (b : Bool) :
--   ⟦.Bool⟧ Lb ∗ ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ Lz ↦ v ⊢
--   WP ↑(s(if b then Lz := copy Lx else Lz := copy Ly) : Configuration) @s; N
--   {{__, ∃ lz, ⟦.Bool⟧ Lb ∗ ⟦.MB lz .Int⟧ Lz ∗
--     |={N}=> (∃ Lz, ⟦.ML lz .Int⟧ Lz ={N}=∗ ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly)))}}
-- := by
--   iintro ⟨Hb, Hx, Hy, #HIx, #HIy, Hz⟩
--   cases b
--   · iapply Statement.wp_IfThenElseFalse
--     inext
--     iapply wp_wand $$ [Hy HIy Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hy HIy
--     iintro %_ ⟨%lz, Hy, Hz, #HIz⟩
--     iexists lz
--     iframe
--     ihave >⟨%Lz', Hz, HLy, HC, Hacc⟩ := brw_open (l := ly) $$ [HIy] [Hy]; iassumption; simp [Typ.interp]; iassumption
--     imodintro
--     iexists Lz'
--     iintro Hz
--     imod Hacc $$ %⟦.ML lz .Int⟧ [Hz HLy]
--     · iframe
--       iintro %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     isplitl [Hx]; iexists _, _; iassumption
--     iexists _, _; unfold Typ.interp; iassumption
--   · iapply Statement.wp_IfThenElseTrue
--     inext
--     iapply wp_wand $$ [Hx HIx Hz]
--     iapply wp_rebrw (T := .Int) $$ Hz Hx HIx
--     iintro %_ ⟨%lz, Hx, Hz, #HIz⟩
--     iexists lz
--     iframe
--     ihave >⟨%Lz', Hz, HLx, HC, Hacc⟩ := brw_open (l := lx) $$ [HIx] [Hx]; iassumption; simp [Typ.interp]; iassumption
--     imodintro
--     iexists Lz'
--     iintro Hz
--     imod Hacc $$ %⟦.ML lz .Int⟧ [Hz HLx]
--     · iframe
--       iintro %_ -
--       unfold basicTimelessConstraint
--       ipureintro
--       infer_instance
--     isplitl [Hacc]; iexists _, _; unfold Typ.interp; iassumption
--     iexists _, _; iassumption

-- this show we can end a borrow of an abstraction
-- A {..., ML l}, MB l τ ==> A {..., τ}
theorem test5 :
  (∃ Lz, ⟦.ML lz .Int⟧ Lz ∗ (⟦.ML lz .Int⟧ Lz ={N}=∗ ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly)))) ∗
  ⟦.MB lz τ⟧ Lz'
  ={N}=∗
  ((∃ τx Lx, ⟦.MB lx τx⟧ Lx) ∗ (∃ τy Ly, ⟦.MB ly τy⟧ Ly) ∗ (∃ Lz, ⟦.MB lz τ⟧ Lz))
:= by
  iintro ⟨⟨%Lz, HLz, HAbs⟩, _⟩
  imod HAbs $$ [HLz //] with ⟨_, _⟩
  imodintro
  iframe


-- theorem test6 (b : Bool) :
--   ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ (∃ v, Lz ↦ v) ⊢
--   wp N s(if b then v(Lz) := copy v(Lx) else v(Lz) := copy v(Ly))
--   iprop(∃ lz, ⟦.MB lz .Int⟧ Lz ∗ A {[.ML lz, .MB lx .Int, .MB ly .Int]})
-- := by
--   iintro H
--   iapply wp_wand $$ [H]
--   iapply test2 $$ [H]; iframe
--   iintro ⟨%lz, HLz, >⟨%Lz, Hlz, Habs⟩⟩ !>
--   iexists lz
--   iframe
--   simp!
--   iexists Lz
--   iframe
--   iintro ⟨HML, -⟩
--   imod Habs $$ [HML] with ⟨⟨%_, %Lx, HLx⟩, ⟨%_, %Ly, HLy⟩⟩; iassumption
--   imodintro
--   isplitl [HLx]; iexists _, _; iassumption
--   isplitl [HLy]; iexists _, _; iassumption
--   iempintro

-- theorem test6_hoare (b : Bool) : ⊢
--   {{ ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ (∃ v, Lz ↦ v) }}
--   if b then v(Lz) := copy v(Lx) else v(Lz) := copy v(Ly)
--   {{ ∃ lz, ⟦.MB lz .Int⟧ Lz ∗ A {[.ML lz, .MB lx .Int, .MB ly .Int]} }}
--   @ N
-- := by
--   unfold hoare
--   iapply test6

-- for the following function
-- choose<'a>(b : Bool, x : &'a mut Int, y : &'a mut Int) -> &'a mut Int {
-- if b { z := x } else { z := y}
-- return z
-- }
-- we have to prove
-- { A { MB _lx _, MB _ly _, ML lx, ML ly} ∗ ⟦MB lx .Int⟧ Lx ∗ ⟦MB ly .Int⟧ Ly }
-- [the code]
-- { A { MB _lx _, MB _ly _, ML lz} ∗ ⟦MB lz .Int⟧ }
-- which is essentially what we prove, up to 1 abstraction merging




-- MB l (ML l' : Int) -< A { MB l (_ : Int), (ML l' : Int) }       ⟦MB l' ?⟧ ={N}=∗ ⟦MB l Int⟧
-- A { MB l0 Int, (ML l : Int)}                            ⟦MB l Int⟧ ={N}=∗ ⟦MB l0 Int⟧
-- >=
-- A { MB l0 Int, ML l' }
-- MB l0 Int



theorem test7 (b : Bool) :
  ⟦.MB lx .Int⟧ Lx ∗ ⟦.MB ly .Int⟧ Ly ∗ inv N (I lx) ∗ inv N (I ly) ∗ Lz ↦ v ⊢
  WP (sb(if b then Lz := copy Lx else Lz := copy Ly), (∅ : Kontinuation)) @ s; N
  {{__, ∃ lz, ⟦.MB lz .Int⟧ Lz ∗ A {[.ML lz .Int, .MB lx .Int, .MB ly .Int]}}}
:= by
  iintro ⟨HLx, HLy, #HIx, #HIy, HLz⟩
  cases b
  · iapply Statement.wp_IfThenElseFalse
    inext
    simp
    iapply wp_rebrw (T := .Int) $$ HLz HLy HIy
    iintro !> %lz HLy HLz #HIz
    iapply wp_value' (v := ())
    iexists lz
    iframe
    simp [Abstraction.interp]
    iintro ⟨HLz, -⟩
    ihave >⟨HLy⟩ := weak.brw_rebrw_end (P := ⟦.Int⟧) (l := ly) (l' := lz) $$ [HIz] [HLz HLy]
    · iintro %_ %_ -
      unfold basicTimelessConstraint
      ipureintro
      infer_instance
    · isplitl<;>iassumption
    · simp!
      iframe
      iapply MB.toWeak
      iassumption
    simp!
    iframe
    imodintro
    iapply MB.toWeak
    iassumption
  · iapply Statement.wp_IfThenElseTrue
    inext
    simp
    iapply wp_rebrw (T := .Int) $$ HLz HLx HIx
    iintro !> %lz HLx HLz #HIz
    iapply wp_value' (v := ())
    iexists lz
    iframe
    simp! [Abstraction.interp]
    iintro ⟨HLz, -⟩
    ihave >⟨HLx⟩ := weak.brw_rebrw_end (P := ⟦.Int⟧) (l := lx) (l' := lz) $$ [HIz] [HLz HLx]
    · iintro %_ %_ -
      unfold basicTimelessConstraint
      ipureintro
      infer_instance
    · isplitl<;>iassumption
    · simp!
      iframe
      iapply MB.toWeak
      iassumption
    simp!
    iframe
    imodintro
    isplitl [HLy]; iapply MB.toWeak; iassumption
    iempintro


-- MB l (ML l' : Int) -< A {MB l Int, (ML l' : Int)}

theorem test8 :
  ⟦.MB l (.ML l' .Int)⟧ L0 ∗ inv N (I l) ∗ inv N (I l') ⊢ ((∃ L', ⟦.MB l' .Int⟧ L') ={N}=∗ (∃ L, ⟦.MB l .Int⟧ L))
:= by
  simp!
  iintro ⟨HL0, #IHl, #IHl'⟩ ⟨%L', HL'⟩
  ihave >⟨%L0', HL0', HL0, HC, Hacc⟩ := brw_open (l := l) $$ [IHl] [HL0]; iassumption; iassumption
  ihave >⟨HL0', HL'⟩ := brw_end (l := l') $$ [IHl'] [HL' HL0']; iassumption; iframe
  imod Hacc $$ %⟦.Int⟧ [HL0' HC HL0]
  · simp!
    iframe
    iintro %_ -
    unfold basicTimelessConstraint
    ipureintro
    infer_instance
  imodintro
  iexists _
  simp!
  iassumption


theorem test9 :
  ⦃.MB l (.ML l' τ)⦄ ∗ inv N (I l) ∗ inv N (I l') ⊢ A {[ .ML l' τ, .MB l τ]}
:= by
  simp! [Abstraction.interp]
  iintro ⟨HMB, #IHl, #IHl'⟩ ⟨HL, -⟩
  ihave >HMB := weak.brw_rebrw_end (P := τ.interp') (l := l) (l' := l') $$ [IHl IHl'] [HMB HL]
  · iintro %_ %_ -
    unfold basicTimelessConstraint
    ipureintro
    infer_instance
  · isplitl; iassumption
    iassumption
  · iframe
  imodintro
  isplitl; iassumption
  iempintro

theorem test10 :
  A {[ .ML l σ, .MB l' τ]} ∗ A {[.MB l σ]} ⊢ A {[ .MB l' τ]}
:= by
  simp! [Abstraction.interp]
  iintro ⟨Habs, Habs'⟩ -
  imod Habs' $$ [] with ⟨HMBl, -⟩; iempintro
  imod Habs $$ [HMBl]; iframe
  iframe


theorem test11 :
  A {[ .MB l τ ]} ={N}=∗ ⦃.MB l τ⦄
:= by
  simp! [Abstraction.interp]
  iintro Habs
  imod Habs $$ [] with ⟨_, -⟩; iempintro
  iassumption


-- this is a more ad hoc proof, a simpler proof using wp_move is below
theorem wp_swap (HMov1 : τ1.Movable) (HMov2 : τ2.Movable) :
  ⟦.MB lx τ1⟧ x ∗ inv N (I lx) ∗
  ⟦.MB ly τ2⟧ y ∗ inv N (I ly) ∗
  x0 ↦ vx ∗
  y0 ↦ vy ⊢
  WP (sb(
    x0 := copy *x;
    y0 := copy *y;
    *x := copy y0;
    *y := copy x0
  ), (∅ : Kontinuation)) @ s; N
  {{__,
    ⟦.MB lx τ2⟧ x ∗
    ⟦.MB ly τ1⟧ y ∗
    (∃ v, x0 ↦ v) ∗
    (∃ v, y0 ↦ v)
  }}
:= by
  iintro ⟨Hx, #HIx, Hy, #HIy, Hx0, Hy0⟩
  simp [Typ.interp]

  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy
  -- opening L1
  iapply fupd_wp
  ihave >⟨%x', Hx', Hx, HCx, Haccx⟩ := brw_open_strong $$ HIx Hx
  imod Haccx $$ HCx
  imodintro

  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  -- we split ⟦τ⟧ L1' into the data and permission
  ihave ⟨%vx, Hx', Hx'p⟩ := split_movable _ HMov1 $$ Hx'
  iapply Statement.wp_rvalue'
  iapply RValue.wp_copy $$ Hx'
  iintro !> Hx'

  iapply Statement.wp_assign $$ Hx0
  iintro !> Hx0

  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy

  -- opening L2
  iapply fupd_wp
  ihave >⟨%y', Hy', Hy, HCy, Haccy⟩ := brw_open_strong $$ HIy Hy
  imod Haccy $$ HCy
  imodintro

  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  -- we split ⟦τ⟧ L2' into the data and permission
  ihave ⟨%vy, Hy', Hy'p⟩ := split_movable _ HMov2 $$ Hy'
  iapply Statement.wp_rvalue'
  iapply RValue.wp_copy $$ Hy'
  iintro !> Hy'

  iapply Statement.wp_assign $$ Hy0
  iintro !> Hy0

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ Hy0
  iintro !> Hy0

  iapply Statement.wp_assign $$ Hx'
  iintro !> Hx'

  ---------------------------------------------------------- *y := copy x0

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ Hx0
  iintro !> Hx0

  iapply Statement.wp_assign $$ Hy'
  iintro !> Hy'


  -- we must close the borrows now
  iapply fupd_wp
  ihave >Hx := Haccx $$ [Hx' Hy'p Hx]
  iframe
  isplitl [Hx' Hy'p]; iapply split_movable _ HMov2; iexists _; iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  ihave >Hy := Haccy $$ [Hy' Hx'p Hy]
  iframe
  isplitl [Hy' Hx'p]; iapply split_movable _ HMov1; iexists _; iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  imodintro

  iapply wp_value' (v := ())
  iframe

-- this is a simpler proof
theorem wp_swap' (HMov1 : τ1.Movable) (HMov2 : τ2.Movable) :
  ⟦.MB lx τ1⟧ x ∗ inv N (I lx) ∗
  ⟦.MB ly τ2⟧ y ∗ inv N (I ly) ∗
  x0 ↦ vx ∗
  y0 ↦ vy ⊢
  WP (sb(
    x0 := copy *x;
    y0 := copy *y;
    *x := copy y0;
    *y := copy x0
  ), (∅ : Kontinuation)) @ s; N
  {{__,
    ⟦.MB lx τ2⟧ x ∗
    ⟦.MB ly τ1⟧ y ∗
    (∃ v, x0 ↦ v) ∗
    (∃ v, y0 ↦ v)
  }}
:= by
  iintro ⟨Hx, #HIx, Hy, #HIy, Hx0, Hy0⟩
  simp [Typ.interp]

  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy

  -- opening L1
  iapply fupd_wp
  ihave >⟨%x', Hx', Hx, HCx, Haccx⟩ := brw_open_strong $$ HIx Hx
  imod Haccx $$ HCx
  imodintro

  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  simp [Statement.RValueEctxtItem.fillItem, RValue.PlaceEctxtItem.fillItem]
  iapply wp_move _ _ HMov1 $$ Hx0 Hx'
  iintro !> Hx0 ⟨%_, Hx'⟩


  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy

  -- opening L2
  iapply fupd_wp
  ihave >⟨%y', Hy', Hy, HCy, Haccy⟩ := brw_open_strong $$ HIy Hy
  imod Haccy $$ HCy
  imodintro

  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  -- we split ⟦τ⟧ L2' into the data and permission
  iapply wp_move _ _ HMov2 $$ Hy0 Hy'
  iintro !> Hy0 ⟨%_, Hy'⟩


  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  iapply wp_move _ _ HMov2 $$ Hx' Hy0
  iintro !> Hx' Hy0

  ---------------------------------------------------------- *y := copy x0

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  iapply wp_move _ _ HMov1 $$ Hy' Hx0
  iintro !> Hy' Hx0


  -- we must close the borrows now
  iapply fupd_wp
  ihave >Hx := Haccx $$ [Hx' Hx]
  iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  ihave >HLy := Haccy $$ [Hy' Hy]
  iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  imodintro

  iapply wp_value' (v := ())
  iframe

theorem wp_swap_raw :
  x ↦ .Loc x' ∗ x' ↦ vx ∗
  y ↦ .Loc y' ∗ y' ↦ vy ∗
  x0 ↦ vx0 ∗
  y0 ↦ vy0 ⊢
  WP (sb(
    x0 := copy *x;
    y0 := copy *y;
    *x := copy y0;
    *y := copy x0
  ), (∅ : Kontinuation)) @ s; N
  {{__,
    x ↦ .Loc x' ∗ x' ↦ vy ∗
    y ↦ .Loc y' ∗ y' ↦ vx ∗
    (∃ v, x0 ↦ v) ∗
    (∃ v, y0 ↦ v)
  }}
:= by
  iintro ⟨Hx, Hx', Hy, Hy', Hx0, Hy0⟩

  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy
  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  simp [Statement.RValueEctxtItem.fillItem, RValue.PlaceEctxtItem.fillItem]
  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ Hx'
  iintro !> Hx'

  iapply Statement.wp_assign $$ Hx0
  iintro !> Hx0


  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy
  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  iapply Statement.wp_rvalue'
  iapply RValue.wp_copy $$ Hy'
  iintro !> Hy'

  iapply Statement.wp_assign $$ Hy0
  iintro !> Hy0


  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ Hy0
  iintro !> Hy0

  iapply Statement.wp_assign $$ Hx'
  iintro !> Hx'


  ---------------------------------------------------------- *y := copy x0

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  iapply Statement.wp_rvalue' (.Assign _)
  iapply RValue.wp_copy $$ Hx0
  iintro !> Hx0

  iapply Statement.wp_assign $$ Hy'
  iintro !> Hy'

  iapply wp_value' (v := ())
  iframe


theorem wp_swap_from_raw (HMov1 : τ1.Movable) (HMov2 : τ2.Movable) :
  ⟦.MB lx τ1⟧ x ∗ inv N (I lx) ∗
  ⟦.MB ly τ2⟧ y ∗ inv N (I ly) ∗
  x0 ↦ vx ∗
  y0 ↦ vy ⊢
  WP (sb(
    x0 := copy *x;
    y0 := copy *y;
    *x := copy y0;
    *y := copy x0
  ), (∅ : Kontinuation)) @ s; N
  {{__,
    ⟦.MB lx τ2⟧ x ∗
    ⟦.MB ly τ1⟧ y ∗
    (∃ v, x0 ↦ v) ∗
    (∃ v, y0 ↦ v)
  }}
:= by
  iintro ⟨Hx, #HIx, Hy, #HIy, Hx0, Hy0⟩
  simp [Typ.interp]

  iapply fupd_wp

  ihave >⟨%x', Hx', Hx, HCx, Haccx⟩  := brw_open_strong $$ HIx Hx
  imod Haccx $$ HCx
  ihave >⟨%y', Hy', Hy, HCy, Haccy⟩  := brw_open_strong $$ HIy Hy
  imod Haccy $$ HCy

  ihave ⟨%vx, Hx', Hvx⟩ := split_movable _ HMov1 $$ Hx'
  ihave ⟨%vy, Hy', Hvy⟩ := split_movable _ HMov2 $$ Hy'

  imodintro

  iapply wp_fupd

  iapply wp_wand $$ [Hx Hx' Hy Hy' Hx0 Hy0]
  iapply wp_swap_raw (x' := x') (y' := y'); iframe
  iintro %_ ⟨Hx, Hx', Hy, Hy', Hx0, Hy0⟩
  iframe

  isplitl [Haccx Hx Hx' Hvy]
  iapply Haccx
  iframe
  isplitl
  iapply split_movable
  iexists _; iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  iapply Haccy
  iframe
  isplitl
  iapply split_movable

  iexists _; iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance

def fn_swap : Statement.FunDef := {
  body := sb(
    "x0" := copy *"x";
    "y0" := copy *"y";
    *"x" := copy "y0";
    *"y" := copy "x0";
    return int 0
  ),
  args := ["x", "y"],
  locals := ["x0", "y0"],
}


theorem fn_test1 (HMov1 : τ1.Movable) (HMov2 : τ2.Movable) :
  "swap" ⋗ fn_swap ∗
  ret ↦ v ∗
  ⟦.MB lx τ1⟧ x ∗ inv N (I lx) ∗
  ⟦.MB ly τ2⟧ y ∗ inv N (I ly) ⊢
  WP (sb(ret := call "swap" (copy x, copy y)), (∅ : Kontinuation)) @ s; N
  {{__,
    ret ↦ Value.Int 0 ∗
    ⟦.MB lx τ2⟧ x ∗
    ⟦.MB ly τ1⟧ y
  }}
:= by
  iintro ⟨Hswap, Hret, Hx, #HIx, Hy, #HIy⟩

  -- we need to open the borrows BEFORE the call
  -- essentially, we transmute to byte arrays now
  iapply fupd_wp
  simp [Typ.interp]
  ihave >⟨%x', Hx', Hx, HCx, Haccx⟩  := brw_open_strong $$ HIx Hx
  imod Haccx $$ HCx
  ihave >⟨%y', Hy', Hy, HCy, Haccy⟩  := brw_open_strong $$ HIy Hy
  imod Haccy $$ HCy
  imodintro

  ihave this := Statement.wp_rvalue' (.Call _ _ [] [_])
  simp; iapply this; iclear this
  iapply RValue.wp_copy $$ Hx
  iintro !> Hxold

  ihave this := Statement.wp_rvalue' (.Call _ _ [_] [])
  simp; iapply this; iclear this
  iapply RValue.wp_copy $$ Hy
  iintro !> Hyold

  ihave this := Statement.wp_call ret [↑x', ↑y'] fn_swap _ (by rfl)
  simp; iapply this $$ Hswap; iclear this
  iintro !> - %Largs %Llocals - - - %HargsLen %HlocalsLen
  simp [fn_swap] at HargsLen HlocalsLen
  let [x, y] := Largs
  let [x0, y0] := Llocals
  clear HargsLen HlocalsLen
  simp [Statement.FunDef.substVars, fn_swap, BI.bigSepL2]
  iintro ⟨Hx, Hy, -⟩ ⟨Hx0, Hy0, -⟩


  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy

  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  simp
  iapply wp_move _ _ HMov1 $$ Hx0 Hx'
  iintro !> Hx0 ⟨%_, Hx'⟩

  iapply Statement.wp_rvalue'_place' (.Assign _) .Copy

  iapply Place.wp_deref $$ Hy
  iintro !> Hy

  iapply wp_move _ _ HMov2 $$ Hy0 Hy'
  iintro !> Hy0 ⟨%_, Hy'⟩

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hx
  iintro !> Hx

  iapply wp_move _ _ HMov2 $$ Hx' Hy0
  iintro !> Hx' Hy0

  ---------------------------------------------------------- *y := copy x0

  iapply Statement.wp_place' (.Assign _)
  iapply Place.wp_deref $$ Hy
  iintro !> Hy
  simp

  iapply wp_move _ _ HMov1 $$ Hy' Hx0
  iintro !> Hy' Hx0

  iapply wp_return (Value.Int 0) _ _ (by rfl)
  inext

  -- we the call has ended, we put back the borrows together
  iapply fupd_wp
  ihave >Hx := Haccx $$ [Hx' Hxold]
  iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  ihave >HLy := Haccy $$ [Hy' Hyold]
  iframe
  iintro %_ -; unfold basicTimelessConstraint; ipureintro; infer_instance
  imodintro


  iapply wp_assign $$ Hret
  iintro !> Hret

  iapply wp_value' (v := ())
  iframe


def fn_fact : FunDef := {
  body := sb(
    if copy "n" <= int 0 then
      return int 1
    else
      "temp" := call "fact" (copy "n" - int 1);
      return copy "n" * copy "temp"
  ),
  args := ["n"],
  locals := ["temp"],
}

def fact (n : Int) : Int := if n > 0 then n * (fact (n-1)) else 1
termination_by n.natAbs

theorem fact_spec1 (n : Int) : n > 0 -> fact n = n * (fact (n-1)) := by
  induction n.natAbs <;> grind [fact]

theorem fact_spec2 (n : Int) : n <= 0 -> fact n = 1 := by grind [fact]

-- having k as an implicit drives iloeb crazy for some reason
theorem wp_fact {k : Kontinuation} :
  ▷ "fact" ⋗ fn_fact -∗
  ▷ ret ↦ v -∗
  ▷ (ret ↦ Value.Int (fact n) -∗ WP (next, k) @ s; E {{ φ }}) -∗
  WP (sb(ret := call "fact" (int n); next), k) @ s; E {{ φ }}
:= by
  iintro >Hfact >Hret Hwp
  iloeb as IH generalizing %ret %n %k %v %next

  have' := wp_call (GF := GF) ret [Value.Int n] fn_fact k (by rfl)
  simp at this; iapply this $$ Hfact; clear this
  iintro !> Hfact %Largs %Llocals - - - %HlenArgs %HlenLocals
  simp [fn_fact] at HlenArgs HlenLocals
  let [_n,] := Largs; clear HlenArgs
  let [temp,] := Llocals; clear HlenLocals
  simp [BI.bigSepL2]
  iintro ⟨H_n, -⟩ ⟨Htemp, -⟩
  ispecialize IH $$ %temp %(n-1) %(k.push {ret, next}) %_ %([s(return copy _n * copy temp)]) Hfact Htemp
  simp [fn_fact, FunDef.substVars]

  have' := wp_rvalue (GF := GF) (.IfThenElse _ _) [RValue.EctxItem.LeqL _]
  simp at this; iapply this; clear this
  iapply RValue.wp_copy $$ H_n
  iintro !> H_n
  simp [fillItem, RValue.ofVal]

  iapply wp_rvalue' (.IfThenElse _ _)
  iapply RValue.wp_leq
  inext

  cases _: decide (n <= 0)
  · iapply wp_value' (v := Value.Bool «false»)
    simp
    iapply wp_IfThenElseFalse
    inext

    ihave this := wp_rvalue (.Call _ _ [] []) [.SubL _]
    simp; iapply this; iclear this
    iapply RValue.wp_copy $$ H_n
    iintro !> H_n

    ihave this := wp_rvalue' (.Call _ _ [] [])
    simp; iapply this; iclear this
    simp [fillItem]
    iapply RValue.wp_sub
    inext
    iapply wp_value' (v := Value.Int (n-1))

    iapply IH
    iintro !> Htemp

    ihave this := wp_rvalue .Return [.MulL _]
    simp; iapply this; iclear this
    iapply RValue.wp_copy $$ H_n
    iintro !> H_n
    simp [fillItem]

    ihave this := wp_rvalue .Return [.MulR _]
    simp; iapply this; iclear this
    iapply RValue.wp_copy $$ Htemp
    iintro !> Htemp
    simp [fillItem]

    iapply wp_rvalue' .Return
    iapply RValue.wp_mul
    inext

    rw [<-fact_spec1 n (by grind)]
    iapply wp_value' (v := Value.Int (fact n))
    simp
    iapply wp_return _ k _ rfl
    inext

    iapply wp_assign $$ Hret
    iintro !> Hret

    iapply Hwp $$ Hret

  · iapply wp_value' (v := Value.Bool «true»)
    simp
    iapply wp_IfThenElseTrue
    inext

    rw [<-fact_spec2 n (by grind)]
    simp
    iapply wp_return (Value.Int (fact n)) k _ rfl
    inext

    iapply wp_assign $$ Hret
    iintro !> Hret

    iapply Hwp $$ Hret
