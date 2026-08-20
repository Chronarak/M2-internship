import Iris
import Lib.RA


open Iris OFE RA Excl ExclAuth BI


class ConstrainedPredBox (GF : outParam BundledGFunctors) (X : outParam <| Type _) [OFE X]
(C : outParam <| X -> (X -> IProp GF) -> IProp GF) where
  elem : ElemG GF (constOF (FullRA (X := X) (Y := IProp GF)))

attribute [reducible, instance] ConstrainedPredBox.elem

namespace ConstrainedPredBox.Notations

scoped notation "[" P "{{" x "}}" "at" γ "]" => iOwn γ (E := ConstrainedPredBox.elem) (getter_token P x)
scoped notation "[" "end" "{{" x "}}" "at" γ "]" => iOwn γ (E := ConstrainedPredBox.elem) (ender_token x)
scoped notation "[" "partial" "write" P "{{" x" }}" "at" γ "]" => iOwn γ (E := ConstrainedPredBox.elem) (partial_writer_token P x)
scoped notation "[" "full" "write" P "{{" x" }}" "at" γ "]" => iOwn γ (E := ConstrainedPredBox.elem) (full_writer_token P x)
scoped notation "[" "stored" "{{" x "}}" "at" γ "]" => iOwn γ (E := ConstrainedPredBox.elem) (stored_getter_token x)

end ConstrainedPredBox.Notations

open ConstrainedPredBox.Notations

variable [OFE X]
variable {C : X -> (X -> IProp GF) -> IProp GF}
variable [ConstrainedPredBox GF X C]


theorem iOwn_getter_ender_agree (P : X -> IProp GF) (x x' : X) [Discrete X] :
  [P{{x}} at γ] ∗ [end{{x'}} at γ] ⊢ ⌜x = x'⌝
:= by
  iintro ⟨HP, Hend⟩
  ihave %_: ⌜✓{0}getter_token P x • ender_token x'⌝ $$ [HP Hend]
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply getter_ender_agree
  assumption
  done

theorem iOwn_getter_partial_writer_agree (x x' : X) (P P' : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ] ∗ [partial write P'{{x'}} at γ] ⊢ ⌜P = P' ∧ x = x'⌝
:= by
  iintro ⟨Hget, Hwrite⟩
  ihave %_: ⌜✓{0}getter_token P x • partial_writer_token P' x'⌝ $$ [Hget Hwrite]
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply getter_partial_writer_agree
  assumption
  done

theorem iOwn_partial_writer_ender_agree (P : X -> IProp GF) (x x' : X) [Discrete X] :
  [partial write P{{x}} at γ] ∗ [end{{x'}} at γ] ⊢ ⌜x = x'⌝
:= by
  iintro ⟨HP, Hend⟩
  ihave %_: ⌜✓{0}partial_writer_token P x • ender_token x'⌝ $$ [HP Hend]
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply partial_writer_ender_agree
  assumption
  done

theorem iOwn_getter_getter_absurd (x x' : X) (P P' : X -> IProp GF) :
  ([P{{x}} at γ]) ∗ [P'{{x'}} at γ] ⊢ False
:= by
  iintro ⟨HP, HP'⟩
  ihave %_: ⌜✓{0} getter_token P x • getter_token P' x'⌝ $$ [HP HP']
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply getter_getter_absurd (X := X)
  assumption
  done

theorem iOwn_getter_stored_getter_absurd(P : X -> IProp GF) (x x' : X) :
  [P{{x}} at γ] ∗ [stored {{x'}} at γ] ⊢ False
:= by
  iintro ⟨HP, Hstore⟩
  ihave %_: ⌜✓{0} getter_token P x • stored_getter_token x'⌝ $$ [HP Hstore]
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply getter_stored_getter_absurd (X := X)
  assumption
  done

theorem iOwn_partial_writer_full_writer_absurd (P P' : X -> IProp GF) (x x' : X) :
  [partial write P{{x}} at γ] ∗ [full write P'{{x'}} at γ] ⊢ False
:= by
  iintro ⟨Hpwrite, Hfwrite⟩
  ihave %_: ⌜✓{0} partial_writer_token P x • full_writer_token P' x'⌝ $$ [Hpwrite Hfwrite]
  · iapply internalCmraValid_elim
    iapply iOwn_cmraValid_op (E := ConstrainedPredBox.elem)
    iframe
  ipureintro
  apply partial_writer_full_writer_absurd (X := X)
  assumption
  done






class TimelessConstraint (C : X -> (X -> IProp GF) -> IProp GF) where
  isTimeless : Timeless iprop(C x P)
  impliesTimeless : C x P ⊢ ⌜Timeless iprop(P x)⌝

attribute [instance] TimelessConstraint.isTimeless

class ConstraintIsPersistent (C : X -> (X -> IProp GF) -> IProp GF) where
  isPersistent : Persistent (C x P)

attribute [instance] ConstraintIsPersistent.isPersistent



def basicTimelessConstraint (x : X) (P : X -> IProp GF) : IProp GF := iprop(⌜Timeless (P x)⌝)

instance : TimelessConstraint (basicTimelessConstraint (X := X) (GF := GF)) where
  isTimeless := by unfold basicTimelessConstraint; infer_instance
  impliesTimeless := by unfold basicTimelessConstraint; iintro %_ %_ _; iassumption

instance : ConstraintIsPersistent (basicTimelessConstraint (X := X) (GF := GF)) where
  isPersistent := by unfold basicTimelessConstraint; infer_instance



def I.pre (γ : GName) (x : X) (P : X -> IProp GF) : IProp GF := iprop(
 C x P ∗ (
    (P x ∗ [partial write P{{x}} at γ]) ∨
    [stored {{x}} at γ]
  ) ∨
    ([P{{x}} at γ] ∗ [end {{x}} at γ] ∗ [partial write P{{x}} at γ])
)

def I (γ : GName) : IProp GF := iprop(
  ∃ (x : X) (P : X -> IProp GF), I.pre γ x P)


instance [Discrete X] : Timeless (iOwn (E := ConstrainedPredBox.elem) γ (getter_token P x)) := by infer_instance

instance [Discrete X] : Timeless (iOwn (E := ConstrainedPredBox.elem) γ (ender_token x)) := by infer_instance

instance [Discrete X] : Timeless (iOwn (E := ConstrainedPredBox.elem) γ (partial_writer_token P x)) := by infer_instance

instance [Discrete X] [TimelessConstraint C] : Timeless (I.pre (GF := GF) γ x P) := by
  unfold I.pre
  constructor
  rw [later_or.to_eq]
  iintro (⟨HC, HI⟩ | HI)
  · ileft
    ihave >HC : ◇ C x P $$ [HC]
    · iapply Timeless.timeless
      iassumption
    ihave %_ : ⌜Timeless (P x)⌝ $$ [HC]
    · iapply TimelessConstraint.impliesTimeless (C := C)
      iassumption
    iapply except0_sep.mpr
    isplitl [HC]; iassumption
    apply Timeless.timeless
  · iright
    apply Timeless.timeless

instance [Discrete X] [TimelessConstraint C] : Timeless (I γ) := by
  unfold I
  infer_instance






theorem alloc (x : X) (P : X -> IProp GF) :
  P x ∗ C x P ⊢ |==> ∃ γ, [P{{x}} at γ] ∗ [end {{x}} at γ] ∗ I γ
:= by
  iintro ⟨HP, HC⟩
  ihave >⟨%γ, H⟩ : |==> ∃ γ, iOwn (E := ConstrainedPredBox.elem) γ ((getter_token P x • ender_token x) • partial_writer_token P x) $$ []
  · iapply iOwn_alloc
    unfold getter_token ender_token partial_writer_token
    simp [CMRA.op, optionOp, Prod.op]
    simp [CMRA.Valid, Prod.Valid, -View.Valid]
    constructor
    · apply Auth.auth_both_valid_2
      · simp [CMRA.Valid]
      · rfl
    · simp [Agree.op_idemp]
      apply Agree.toAgree_valid
  ihave ⟨H, Hwrite⟩ : iOwn (E := ConstrainedPredBox.elem) γ (getter_token P x • ender_token x) ∗ iOwn (E := ConstrainedPredBox.elem) γ (partial_writer_token P x) $$ [H]
  · iapply iOwn_op.mp
    iexact H
  ihave ⟨HPtok, Hend⟩ : iOwn (E := ConstrainedPredBox.elem) γ (getter_token P x) ∗ iOwn (E := ConstrainedPredBox.elem) γ (ender_token x) $$ [H]
  · iapply iOwn_op.mp
    iassumption
  imodintro
  iexists γ
  iframe
  unfold I I.pre
  iexists x, P
  iframe
  ileft
  iframe
  ileft
  iframe
  done

theorem full_write (P Q : X -> IProp GF) [Discrete X] :
  Q x ∗ (∀ P, C x P -∗ C x Q) ∗ [full write P{{x}} at γ] ∗ I γ ⊢
  |==> ([Q{{x}} at γ] ∗ I γ)
:= by
  rw (occs := [1]) [I]
  unfold I.pre
  iintro ⟨HQ, HCwand, H, ⟨%x', %P', HI⟩⟩
  icases HI with (⟨HC, (⟨-, HW⟩ | Hstored)⟩ | ⟨-, -, HW⟩)
  · iexfalso
    iapply iOwn_partial_writer_full_writer_absurd
    iframe
  · ihave H : iOwn (E := ConstrainedPredBox.elem) γ ((some (excl ()), none, some (excl ())), some (CMRA.op (●E P) (◯E P)), toAgree x • toAgree x') $$ [H Hstored]
    · ihave _ : iOwn (E := ConstrainedPredBox.elem) γ ((full_writer_token P x) • (stored_getter_token x')) $$ [H Hstored]
      · iapply iOwn_op.mpr
        iframe
      simp [stored_getter_token, full_writer_token]
      simp [CMRA.op, Prod.op]
      iassumption
    ihave %Hvalid : ⌜✓{0}((some (excl ()), none, some (excl ())), some (CMRA.op (●E P) (◯E P)), toAgree x • toAgree x')⌝  $$ [H]
    · iapply internalCmraValid_elim
      iapply iOwn_cmraValid (E := ConstrainedPredBox.elem)
      iassumption
    simp [CMRA.ValidN, Prod.ValidN, -View.ValidN] at Hvalid
    have ⟨H, Hagree⟩ := Hvalid; clear Hvalid H
    have Heq : x = x' := by
      apply Discrete.discrete_0
      apply Agree.toAgree_op_validN_iff_dist.mp
      assumption
    subst Heq
    ihave >H : |==> iOwn (E := ConstrainedPredBox.elem) γ ((some (excl ()), none, some (excl ())), some (CMRA.op (●E Q) (◯E Q)), toAgree x • toAgree x) $$ [H]
    · iapply iOwn_update (a := (_, some (CMRA.op (●E P) (◯E P)), _))
      apply Update.prod; simp; intro _ _ _; assumption
      apply Update.prod <;> simp
      · apply Update.option
        apply Auth.auth_update
        apply LocalUpdate.option
        apply LocalUpdate.replace
        trivial
      · intro _ _ _; assumption
      iassumption
    ihave H : iOwn (E := ConstrainedPredBox.elem) γ (getter_token Q x • partial_writer_token Q x) $$ [H]
    · simp [getter_token, partial_writer_token, CMRA.op, Prod.op]
      iassumption
    ihave ⟨Hget, HI⟩ : iOwn (E := ConstrainedPredBox.elem) γ (getter_token Q x) ∗ iOwn (E := ConstrainedPredBox.elem) γ (partial_writer_token Q x) $$ [H]
    · iapply iOwn_op.mp
      iassumption
    imodintro
    iframe
    unfold I I.pre
    iexists x, Q
    ispecialize HCwand $$ %P' [HC]; iassumption
    iframe
    ileft
    iframe
    ileft
    iframe
  · iexfalso
    iapply iOwn_partial_writer_full_writer_absurd
    iframe
  done

theorem getter_strong (P : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ] ∗ I γ ⊢
    P x ∗ C x P ∗
    (∀ Q, Q x ∗ (∀ P, C x P -∗ C x Q) ∗ I γ ==∗ ([Q{{x}} at γ] ∗ I γ)) ∗
    (C x P -∗ I γ)
:= by
  rw (occs := [1]) [I]
  unfold I.pre
  iintro ⟨Hget, ⟨%x', %P', HI⟩⟩
  icases HI with (⟨HC, (⟨HP, Hpwrite⟩ | Hstored)⟩ | ⟨Hget', -, -⟩)
  · ihave %Heqs : ⌜P = P' ∧ x = x'⌝ $$ [Hget Hpwrite]
    · iapply iOwn_getter_partial_writer_agree
      iframe
    have ⟨rfl, rfl⟩ := Heqs
    iframe
    ihave Hboth : iOwn γ (E := ConstrainedPredBox.elem) (getter_token P x • partial_writer_token P x) $$ [Hget Hpwrite]
    · iapply iOwn_op.mpr
      iframe
    ihave ⟨Hfwrite, Hstored⟩ : [full write P{{x}} at γ] ∗ [stored {{x}} at γ] $$ [Hboth]
    · iapply iOwn_op.mp
      unfold getter_token partial_writer_token full_writer_token stored_getter_token
      simp [CMRA.op, Prod.op]
      iassumption
    isplitl [Hfwrite]
    · iintro %Q ⟨HQ, HCwand, HI⟩
      iapply full_write (P := P) (Q := Q)
      iframe
    · iintro HC
      unfold I I.pre
      iexists x, P
      ileft
      iframe
  · iexfalso
    iapply iOwn_getter_stored_getter_absurd
    iframe
  · iexfalso
    iapply iOwn_getter_getter_absurd
    iframe
  done

theorem getter_persistent (P : X -> IProp GF) [Discrete X] [ConstraintIsPersistent C] :
  [P{{x}} at γ] ∗ I γ ⊢
    P x ∗ C x P ∗
    (∀ Q, Q x ∗ (∀ P, C x P -∗ C x Q) ∗ I γ ==∗ ([Q{{x}} at γ] ∗ I γ)) ∗
    I γ
:= by
  iintro ⟨Hget, HI⟩
  ihave ⟨HP, #HC, Hacc, HI⟩ := getter_strong $$ [Hget HI]; iframe
  ispecialize HI $$ [HC]; iassumption
  iframe
  iassumption
  done

theorem getter_constraint (P : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ] ∗ I γ ⊢
    C x P ∗ (C x P -∗ I γ)
:= by
  iintro ⟨Hget, HI⟩
  ihave ⟨HP, HC, Hacc, HI⟩ := getter_strong $$ [Hget HI]; iframe
  iframe
  done

theorem getter_constraint_persistent (P : X -> IProp GF) [Discrete X] [ConstraintIsPersistent C] :
  [P{{x}} at γ] ∗ I γ ⊢ C x P
:= by
  iintro ⟨Hget, HI⟩
  ihave ⟨HP, HC, Hacc, HI⟩ := getter_strong $$ [Hget HI]; iframe
  iframe
  done

theorem ender(P : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ] ∗ [end{{x'}} at γ] ∗ I γ ⊢
  P x ∗ ⌜x = x'⌝ ∗ C x P ∗ I γ
:= by
  rw (occs := [1]) [I]
  unfold I.pre
  iintro ⟨Hget, Hend, ⟨%x'', %P', HI⟩⟩
  icases HI with (⟨HC, (⟨HP, Hwrite⟩ | _)⟩ | ⟨_, _⟩)
  · ihave %Heq : ⌜x'' = x'⌝ $$ [Hwrite Hend]
    · iapply iOwn_partial_writer_ender_agree
      iframe
    subst Heq
    ihave %Heq : ⌜x = x''⌝ $$ [Hget Hend]
    · iapply iOwn_getter_ender_agree
      iframe
    subst Heq
    ihave %Heqs : ⌜P = P' ∧ _⌝ $$ [Hget Hwrite]
    · iapply iOwn_getter_partial_writer_agree
      iframe
    have ⟨rfl, rfl⟩ := Heqs
    iframe
    isplitl []; ipureintro; rfl
    unfold I I.pre
    iexists x, P
    iright
    iframe
  · iexfalso
    iapply iOwn_getter_stored_getter_absurd
    iframe
  · iexfalso
    iapply iOwn_getter_getter_absurd
    iframe
  done
