import Iris
import Iris.BI.DerivedLawsLater

open Iris Excl ExclAuth OFE CMRA BI

namespace RA
section RA

variable {X Y : Type _} [OFE X]

instance : OFE (X -> Y) := ofDiscrete (X -> Y)
instance : Discrete (X -> Y) where
  discrete_0 := id

abbrev TokensRA := (Option (Excl Unit) × Option (Excl Unit) × Option (Excl Unit))
abbrev ExclRA := Option (ExclAuthR (A := X -> Y))
abbrev FullRA := TokensRA × ExclRA (X := X) (Y := Y) × Agree X

abbrev F := constOF (FullRA (X := X) (Y := Y))

def getter_token (P : X -> Y) (x : X) : FullRA (X := X) (Y := Y) :=
  ((some (excl ()), none, none), some (●E P), toAgree x)

def stored_getter_token (x : X) : FullRA (X := X) (Y := Y) :=
  ((some (excl ()), none, none), none, toAgree x)

def ender_token (x : X) : FullRA (X := X) (Y := Y) :=
  ((none, some (excl ()), none), none, toAgree x)

def partial_writer_token (P : X -> Y) (x : X) : FullRA (X := X) (Y := Y) :=
  ((none, none, some (excl ())), ◯E P, toAgree x)

def full_writer_token (P : X -> Y) (x : X) : FullRA (X := X) (Y := Y) :=
  (((none, none, some (excl ())), some (CMRA.op (●E P) (◯E P)), toAgree x))

theorem getter_ender_agree (P : X -> Y) (x x' : X) [Discrete X] :
  ✓{0}getter_token P x • ender_token x' -> x = x'
:= by
  simp [getter_token, ender_token]
  simp [CMRA.op, Prod.op]
  simp [CMRA.ValidN, Prod.ValidN, -View.ValidN]
  intro _ _
  apply toAgree_op_valid_iff_eq.mp
  apply Discrete.discrete_valid
  assumption
  done

theorem getter_partial_writer_agree (x x' : X) [Discrete X] :
  ✓{0}getter_token P x • partial_writer_token P' x' -> P = P' ∧ x = x'
:= by
  simp [getter_token, partial_writer_token]
  simp [CMRA.op, Prod.op, -View.Op]
  simp [CMRA.ValidN, Prod.ValidN, -View.ValidN, -View.Op]
  intro H _
  constructor
  ·
    have ⟨H0, H1⟩:= Auth.both_validN.mp H
    have := Option.dist_of_inc_exclusive H0 H1
    simp [Dist] at this
    symm
    assumption
  · apply toAgree_op_valid_iff_eq.mp
    apply Discrete.discrete_valid
    assumption
  done

theorem partial_writer_ender_agree (x x' : X) [Discrete X] :
  ✓{0}partial_writer_token P x • ender_token x' -> x = x'
:= by
  simp [partial_writer_token, ender_token]
  simp [CMRA.op, Prod.op, -View.Op]
  simp [CMRA.ValidN, Prod.ValidN, -View.ValidN, -View.Op]
  intro _ _
  apply toAgree_op_valid_iff_eq.mp
  apply Discrete.discrete_valid
  assumption
  done

theorem getter_getter_absurd (x x' : X) :
  ¬✓{0} getter_token P x • getter_token P' x'
:= by
  simp [getter_token]
  simp [CMRA.op, Prod.op, -View.Op]
  simp [CMRA.ValidN]

theorem getter_stored_getter_absurd (x x' : X) :
  ¬✓{0} getter_token P x • stored_getter_token x'
:= by
  simp [getter_token, stored_getter_token]
  simp [CMRA.op, Prod.op, -View.Op]
  simp [CMRA.ValidN]

theorem partial_writer_full_writer_absurd (x x' : X) :
  ¬✓{0} partial_writer_token P x • full_writer_token P' x'
:= by
  simp [partial_writer_token, full_writer_token]
  simp [CMRA.op, Prod.op, -View.Op]
  simp [CMRA.ValidN]
