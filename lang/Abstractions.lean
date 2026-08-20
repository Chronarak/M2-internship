import Lang.Statement
import MBLogic.ConstrainedFiniteLoans

open Iris Std BI

class BorrowGS (hlc : outParam HasLC) (GF : outParam BundledGFunctors)
extends
  Statement.FullGS hlc GF,
  ConstrainedFiniteLoans hlc N GF Location basicTimelessConstraint

variable [BorrowGS hlc GF]


def BaseLayout.interp.pre (L : Location) (T : BaseLayout) (v :Value) : Prop :=
  match T with
  | .Int => ∃ i, v = .Int i
  | .Bool => ∃ b, v = .Bool b
  | .Ptr => ∃ L, v = .Loc L

def Layout.interp.pre (L : Location) (T : Layout) (v : Value) : Prop :=
  match T with
  | Base T => BaseLayout.interp.pre L T v
  | Prod T1 T2 => ∃ v1 v2, v = .Pair v1 v2 ∧ pre L.Fst T1 v1 ∧ pre L.Snd T2 v2

def Layout.interp (L : Location) (T : Layout) : IProp GF :=
  iprop(∀ v, L ↦ v -∗ ⌜Layout.interp.pre L T v⌝)

instance : Timeless (Layout.interp T L) := by
  unfold Layout.interp
  infer_instance



inductive Typ
  | Int
  | Bool
  | Ptr
  | Prod (τ1 τ2 : Typ)
  | MB (l : LoanIdent) (τ : Typ)
  | ML (l : LoanIdent) (τ : Typ)

@[reducible]
def toTyp (T : Layout) : Typ := match T with
    | .Base .Int => .Int
    | .Base .Bool => .Bool
    | .Base .Ptr => .Ptr
    | .Prod T1 T2 => .Prod (toTyp T1) (toTyp T2)

instance : Coe Layout Typ where
  coe := toTyp

def Typ.layout (τ : Typ) : Layout := match τ with
  | Typ.Int => .Base .Int
  | Typ.Bool => .Base .Bool
  | Typ.Ptr => .Base .Ptr
  | Typ.Prod τ1 τ2 => .Prod τ1.layout τ2.layout
  | Typ.MB _ _ => .Base .Ptr
  | Typ.ML _ τ => τ.layout

inductive Typ.Movable : Typ -> Prop
  | Int : Movable Int
  | Bool : Movable Bool
  | Ptr : Movable Ptr
  | Prod (τ1 τ2 : Typ) :
    Movable τ1 ->
    Movable τ2 ->
    Movable (Prod τ1 τ2)
  | MB l τ : Movable (MB l τ)

def Typ.interp (τ : Typ) (L : Location) : IProp GF := match τ with
  | Int => ∃ i, L ↦ .Int i
  | Bool => ∃ b, L ↦ .Bool b
  | Ptr => ∃ (L' : Location), L ↦ L'
  | Prod τ1 τ2 => iprop(interp τ1 L.Fst ∗ interp τ2 L.Snd)
  | MB l τ => _root_.MB l (interp τ) L
  | ML l _ => _root_.ML l L

notation "⟦" τ "⟧" => Typ.interp τ

instance : Timeless (⟦τ⟧ L) := by
  induction τ generalizing L <;>
  unfold Typ.interp <;> infer_instance

-- movable types admit a value intepretation
-- actually that is kind of the whole point, is it not?

def Typ.val_interp (τ : Typ) (HMov : τ.Movable) (v : Value) : IProp GF := match τ with
  | .Int => iprop(∃ i, ⌜v = .Int i⌝)
  | .Bool => iprop(∃ b, ⌜v = .Bool b⌝)
  | .Ptr => iprop(∃ L, ⌜v = .Loc L⌝)
  | .Prod τ1 τ2 =>
    have HMov1 : τ1.Movable := by grind [cases Typ.Movable]
    have HMov2 : τ2.Movable := by grind [cases Typ.Movable]
    iprop(∃ v1 v2, ⌜v = .Pair v1 v2⌝ ∗ τ1.val_interp HMov1 v1 ∗ τ2.val_interp HMov2 v2)
  | .MB l τ =>  iprop(∃ L, ⌜v = .Loc L⌝ ∗ _root_.MB.weak.pre l (interp τ) L)


theorem split_movable (τ : Typ) (HMov : τ.Movable) (L : Location) :
  ⟦τ⟧ L ⊣⊢ ∃ v, L ↦ v ∗ Typ.val_interp τ HMov v
:= by
  induction HMov generalizing L <;> simp [Typ.interp, Typ.val_interp]
  all_goals try
    constructor
    · iintro ⟨%_, _⟩
      iexists _
      iframe
      iexists _
      ipureintro
      rfl
    · iintro ⟨%_, _, ⟨%_, %Heq⟩⟩
      subst Heq
      iexists _
      iframe
  case Prod IH1 IH2 =>
    constructor
    · iintro ⟨H1, H2⟩
      ihave ⟨%v1, _, _⟩ := IH1 $$ H1
      ihave ⟨%v2, _, _⟩ := IH2 $$ H2
      iexists (.Pair v1 v2)
      isplitr; sorry -- product issues
      iexists v1, v2
      isplitr; ipureintro; rfl
      iframe
    · iintro ⟨%_, _, ⟨%_, %_, %Heq, _, _⟩⟩
      subst Heq
      sorry -- product issues
  case MB =>
    unfold MB MB.weak.pre
    constructor
    · iintro ⟨%_, _, _⟩
      iexists _
      iframe
      ipureintro; rfl
    · iintro ⟨%_, _, ⟨%_, %Heq, _⟩⟩
      subst Heq
      iexists _
      iframe


-- this interpretation is used for MB in particular
-- it is essential interp, except every MB l has l existentially quantified
-- the idea is that in an abstraction with an MB under an MB
-- you are guaranteed to get another MB, but there is no reason for it to
-- be the same
-- TODO : maybe this can be streamlined by a level of indirection
def Typ.interp' (τ : Typ) (L : Location) : IProp GF := match τ with
  | MB _ τ => ∃ l, _root_.MB l (interp' τ) L
  | _ => ⟦τ⟧ L

instance : Timeless (Typ.interp' τ L) := by
  unfold Typ.interp'
  cases τ <;> infer_instance


def Typ.weak_interp (τ : Typ) : IProp GF := match τ with
  | ML _ T => iprop(∃ L, ⟦T⟧ L)
  | MB l τ => _root_.MB.weak l (Typ.interp' τ)
  | _ => iprop(∃ L, ⟦τ⟧ L) -- this should kind of be nothing, really

notation "⦃" τ "⦄" => Typ.weak_interp τ

instance : Timeless ⦃τ⦄ := by cases τ <;> simp! <;> infer_instance


abbrev Abstraction := List Typ

-- A {ML l₁, ..., ML lₙ, τ₁, ..., τₖ} (where the τs are not MLs)
-- is interpreted into
--     (⦃MB l₁ _⦄ ∗ ... ⦃MB lₙ⦄) ={N}=∗ (⦃τ₁⦄ ∗ ... ∗ ⦃τₖ⦄)
-- do note we use weak interpretation
def Abstraction.interp (A : Abstraction) : IProp GF :=
  let MLs : List Typ := A.filterMap (fun | Typ.ML l T => some (Typ.MB l T) | _ => none)
  let others : List Typ := A.filter (fun | Typ.ML _ _ => Bool.false | _ => Bool.true )
  let MLs : IProp GF := ([∗list] τ ∈ MLs, ⦃τ⦄)
  let others : IProp GF := ([∗list] τ ∈ others, ⦃τ⦄)
  iprop(MLs ={N}=∗ others)

declare_syntax_cat abstraction

syntax "abs(" abstraction ")" : term
syntax term : abstraction
syntax term "," abstraction : abstraction
syntax "A" "{[" abstraction "]}" : term
syntax "A" "{" term "}" : term
syntax "A" "{" "}" : term

macro_rules
  | `(abs($t:term , $ts:abstraction)) => `($t :: abs($ts))
  | `(abs($t:term)) => `([$t])
  | `(A{ }) => `(Abstraction.interp [])
  | `(A {[ $a:abstraction ]}) => `(Abstraction.interp abs($a))
  | `(A { $t:term }) => `(Abstraction.interp $t)


theorem List.filterMap_Perm (hP : List.Perm l1 l2) : List.Perm (l1.filterMap f) (l2.filterMap f) := by
  induction hP
  case nil => rfl
  case cons x _ _ _ _ =>
    unfold filterMap
    cases f x <;> simp <;> assumption
  case swap x y _ =>
    unfold filterMap; unfold filterMap
    cases f x <;> cases f y <;> simp
    apply Perm.swap
  case trans =>
    apply Perm.trans <;> assumption

theorem List.filter_Perm (hP : List.Perm l1 l2) : List.Perm (l1.filter f) (l2.filter f) := by
  induction hP
  case nil => rfl
  case cons x _ _ _ _=>
    unfold filter
    cases f x <;> simp <;> assumption
  case swap x y _ =>
    unfold filter; unfold filter
    cases f x <;> cases f y <;> simp
    apply Perm.swap
  case trans =>
    apply Perm.trans <;> assumption


theorem permutation (hp : List.Perm l1 l2) : A { l1 } = A { l2 } := by
  unfold Abstraction.interp
  simp; congr 1
  · apply Algebra.BigOpL.bigOpL_eq_of_perm
    apply List.filterMap_Perm
    assumption
  · congr 1
    apply Algebra.BigOpL.bigOpL_eq_of_perm
    apply List.filter_Perm
    assumption

-- Le-ClearAbs
theorem abstraction_emp : A {} ⊣⊢ emp := by
  constructor
  · iintro - //
  · simp [Abstraction.interp]
    iintro - - !> //
