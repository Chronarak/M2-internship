import Iris
import Lib.RA


open Iris OFE RA Excl ExclAuth BI


abbrev RA [OFE X] := Agree X


class ConstrainedPredBox (GF : outParam BundledGFunctors) (X : outParam <| Type _) [OFE X]
  (CB CL : outParam <| X -> (X -> IProp GF) -> IProp GF) where
  elem : ElemG GF (constOF (RA (X := X)))

attribute [reducible, instance] ConstrainedPredBox.elem

notation "[" P "{{" x "}}" "at" γ "with" CB "]" => iprop(P x ∗ CB x P ∗ iOwn γ (E := ConstrainedPredBox.elem) (toAgree x))
notation "[" "end" "{{" x "}}" "at" γ "with" CL "]" => iprop(∃ P, CL x P ∗ iOwn γ (E := ConstrainedPredBox.elem) (toAgree x))

variable [OFE X]
variable {CB CL : X -> (X -> IProp GF) -> IProp GF}
variable [ConstrainedPredBox GF X CB CL]



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




theorem alloc (x : X) (P : X -> IProp GF) :
  P x ∗ CB x P ∗ CL x P ⊢ |==> ∃ γ, [P{{x}} at γ with CB] ∗ [end {{x}} at γ with CL]
:= by
  iintro ⟨HP, HCB, HCL⟩
  ihave >⟨%γ, H⟩ : |==> ∃ γ, iOwn (E := ConstrainedPredBox.elem) γ (toAgree x • toAgree x) $$ []
  · iapply iOwn_alloc
    simp [CMRA.op, Agree.op_idemp]
  ihave ⟨H, Hwrite⟩ : iOwn (E := ConstrainedPredBox.elem) γ (toAgree x) ∗ iOwn (E := ConstrainedPredBox.elem) γ (toAgree x) $$ [H]
  · iapply iOwn_op.mp
    iexact H
  imodintro
  iexists γ
  iframe



theorem getter_strong (P : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ with CB] ⊢
    P x ∗ CB x P ∗
    (∀ Q, Q x ∗ CB x Q -∗ ([Q{{x}} at γ with CB]))
:= by
  iintro ⟨HP, HCB, Hx⟩
  iframe
  iintro %Q ⟨HQ, HCB⟩
  iframe


theorem ender(P : X -> IProp GF) [Discrete X] :
  [P{{x}} at γ with CB] ∗ [end{{x'}} at γ with CL] ⊢
  P x ∗ CB x P ∗ (∃ P, CL x P) ∗ ⌜x = x'⌝
:= by
  iintro ⟨⟨_, _, Hx⟩, ⟨%_, _, Hx'⟩⟩
  ihave %Heq : ⌜x = x'⌝ $$ [Hx Hx']
  · icombine Hx Hx' as H
    ihave %_: ⌜✓{0} toAgree x • toAgree x'⌝ $$ [H]
    · iapply internalCmraValid_elim
      iapply iOwn_cmraValid (E := ConstrainedPredBox.elem)
      iframe
    ipureintro
    apply toAgree_op_valid_iff_eq.mp
    rw [CMRA.valid_iff_validN']
    assumption
  subst Heq
  iframe
  ipureintro; rfl
