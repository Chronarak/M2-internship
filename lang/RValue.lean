import Lang.Place
import Lang.ContextItem

open Iris Std ProgramLogic Language.Notation


inductive RValue
  | Int (i : Int)
  | Bool (b : Bool)
  | Loc (L : Location)
  | Pair (rv1 rv2 : RValue)
  | Poison
  | Ptr (P : Place)
  | Copy (P : Place)
  | Add (rv1 rv2 : RValue)
  | Sub (rv1 rv2 : RValue)
  | Mul (rv1 rv2 : RValue)
  | Leq (rv1 rv2 : RValue)
  | Alloc
deriving BEq, DecidableEq

namespace RValue

def copy (P : Place) (T : Layout) : RValue := match T with
  | .Base _ => Copy P
  | .Prod T1 T2 => Pair (copy P.Fst T1) (copy P.Snd T2)

@[reducible]
def toVal (rv : RValue) : Option Value := match rv with
  | .Int i => return .Int i
  | .Bool b => return .Bool b
  | .Loc L => return .Loc L
  | .Pair rv1 rv2 => do
    let v1 <- toVal rv1
    let v2 <- toVal rv2
    return .Pair v1 v2
  | .Poison => return .Poison
  | _ => none

@[reducible]
def ofVal (v : Value) : RValue := match v with
  | .Int i => .Int i
  | .Bool b => .Bool b
  | .Loc L => .Loc L
  | .Pair v1 v2 => .Pair (ofVal v1) (ofVal v2)
  | .Poison => .Poison

theorem toVal_coe : toVal (ofVal v) = some v := by
  induction v <;> grind

@[grind inj]
theorem ofVal_inj : Function.Injective ofVal := by
  intros v1 v2
  induction v1 generalizing v2 <;>
  induction v2 <;>
  grind

instance : Coe Value RValue where
  coe := ofVal

@[simp]
def subst (rv : RValue) (x : TermVar) (P : Place) : RValue := match rv with
  | Int _ | Bool _ | Loc _ | Poison => rv
  | Pair rv1 rv2 => Pair (rv1.subst x P) (rv2.subst x P)
  | Ptr P' => Ptr (P'.subst x P)
  | Copy P' => Copy (P'.subst x P)
  | Add rv1 rv2 => Add (rv1.subst x P) (rv2.subst x P)
  | Sub rv1 rv2 => Sub (rv1.subst x P) (rv2.subst x P)
  | Mul rv1 rv2 => Mul (rv1.subst x P) (rv2.subst x P)
  | Leq rv1 rv2 => Leq (rv1.subst x P) (rv2.subst x P)
  | Alloc => Alloc

inductive EctxItem
  | AddL (rv : RValue)
  | AddR (v : Value)
  | SubL (rv : RValue)
  | SubR (v : Value)
  | MulL (rv : RValue)
  | MulR (v : Value)
  | LeqL (rv : RValue)
  | LeqR (v : Value)
  | PairL (rv2 : RValue)
  | PairR (v : Value)

@[reducible, simp]
def EctxItem.fillItem (C : EctxItem) (rv : RValue) : RValue := match C with
  | AddL rv' => .Add rv rv'
  | AddR v => .Add (ofVal v) rv
  | SubL rv' => .Sub rv rv'
  | SubR v => .Sub (ofVal v) rv
  | MulL rv' => .Mul rv rv'
  | MulR v => .Mul (ofVal v) rv
  | LeqL rv' => .Leq rv rv'
  | LeqR v => .Leq (ofVal v) rv
  | PairL rv2 => .Pair rv rv2
  | PairR v => .Pair (ofVal v) rv

theorem EctxItem.fillItem.inj (C : EctxItem) : Function.Injective C.fillItem := by
  intros _ _
  cases C <;> simp!

@[grind cases]
inductive PlaceEctxtItem
  | Ptr
  | Copy

@[reducible, simp]
def PlaceEctxtItem.fillItem (PC : PlaceEctxtItem) (P : Place) : RValue := match PC with
  | Ptr => .Ptr P
  | Copy => .Copy P


inductive baseStep : RValue × State -> RValue × State -> Prop
  | Add :
    -- (i) + (j) -rv> (i+j)
    k = i + j ->
    baseStep ((Add (Int i) (Int j)), σ) (Int k, σ)
  | Sub :
    -- (i) - (j) -rv> (i-j)
    k = i - j ->
    baseStep ((Sub (Int i) (Int j)), σ) (Int k, σ)
  | Mul :
    -- (i) * (j) -rv> (i*j)
    k = i * j ->
    baseStep ((Mul (Int i) (Int j)), σ) (Int k, σ)
  | Leq :
    b = decide (i <= j) ->
    baseStep (Leq (Int i) (Int j), σ) (Bool b, σ)
  | Copy (L : Location) (v : Value) :
    -- copy L -rv> m(L)
    σ.heap[L]? = some v ->
    rv = ofVal v ->
    baseStep ((Copy ↑L), σ) (rv, σ)
  | Ptr :
    -- ptr L -rv> L
    baseStep ((Ptr (.Loc L)), σ) (.Loc L, σ)
  | PContext (PC : PlaceEctxtItem) (P P' : Place) :
    (P, σ) -<[]>-> (P', σ, []) ->
    -- P -p> P' => PC[P] -rv PC[P']
    rv  = PC.fillItem P  ->
    rv' = PC.fillItem P' ->
    baseStep (rv, σ) (rv', σ)
  | Alloc (L : Location) :
    σ.heap[L]? = none ->
    σ' = {σ with heap := Std.insert σ.heap L Value.Poison} ->
    baseStep (Alloc, σ) (↑L, σ')


theorem Option.isSome_true_iff : o.isSome = true <-> ∃ x, o = some x := by
  cases o <;> grind

instance EctxItemLanguage : EctxItemLanguage RValue EctxItem State Unit Value where
  toVal := toVal
  ofVal := ofVal
  coe_of_toVal_eq_some {rv v} _ := by
    induction rv generalizing v <;>
    cases v <;>
    simp [toVal, Option.bind_eq_some_iff] at * <;>
    grind
  toVal_coe v := toVal_coe
  baseStep c obs c' :=
    let (rv', σ', rvs) := c'
    baseStep c (rv', σ') ∧
    rvs = [] ∧
    obs = []
  fillItem := EctxItem.fillItem
  fillItem_inj _ := by
    apply EctxItem.fillItem.inj
    assumption
  fillItem_val rv C _ := by
    cases rv <;>
    cases C <;>
    simp [toVal, Option.isSome_true_iff, Option.bind_eq_some_iff] at * <;>
    grind
  fillItem_no_val_inj {rv rv'} C C' _ _ heq := by
    cases C <;>
    cases C' <;>
    simp at * <;>
    (repeat' rcases heq with ⟨_⟩) <;>
    subst_eqs <;>
    grind [toVal_coe]
  val_stuck Hred := by
    rcases Hred with ⟨Hred, _, _, _⟩
    cases Hred with
    | PContext PC _ _ _ => cases PC <;> subst_eqs <;> simp! at * <;> grind
    | _ =>
      subst_eqs
      simp
  base_ctx_step_val {C} := by
    intro rv σ obs rv' σ' rvs Hred
    rcases Hred with ⟨Hred, _, _, _⟩
    generalize H : C.fillItem rv = rv0 at Hred
    cases Hred with
    | PContext PC _ _ _ =>
      cases C <;> cases rv <;> cases PC <;> simp! at * <;> grind
    | _ => cases C <;> cases rv <;> simp! at * <;> grind

abbrev Ectx := List EctxItem

instance EctxLanguage : EctxLanguage RValue Ectx State Unit Value := by infer_instance

instance Language : Language RValue State Unit Value := by infer_instance



section Notations

open Lean PrettyPrinter Delaborator


declare_syntax_cat rvalue

syntax "rv(" rvalue ")" : term

syntax num : rvalue
syntax "true" : rvalue
syntax "false" : rvalue
syntax "poison" : rvalue
syntax "ptr " place : rvalue
syntax "copy " place : rvalue
syntax rvalue " + " rvalue : rvalue
syntax rvalue " - " rvalue : rvalue
syntax rvalue " * " rvalue : rvalue
syntax rvalue " <= " rvalue : rvalue
syntax "(" rvalue ")" : rvalue
syntax ident : rvalue -- allow for escaping ident
syntax "int " term : rvalue
syntax "bool " term : rvalue
syntax "loc " term : rvalue
syntax "val " term : rvalue
syntax "pair(" rvalue "," rvalue ")" : rvalue

macro_rules
  | `(rv($i:num)) => `(RValue.Int $i)
  | `(rv(true)) => `(RValue.Bool «true»)
  | `(rv(false)) => `(RValue.Bool «false»)
  | `(rv(poison)) => `(RValue.Poison)
  | `(rv(ptr $p:place)) => `(RValue.Ptr p($p))
  | `(rv(copy $p:place)) => `(RValue.Copy p($p))
  | `(rv($rv1:rvalue + $rv2:rvalue)) => `(RValue.Add rv($rv1) rv($rv2))
  | `(rv($rv1:rvalue - $rv2:rvalue)) => `(RValue.Sub rv($rv1) rv($rv2))
  | `(rv($rv1:rvalue * $rv2:rvalue)) => `(RValue.Mul rv($rv1) rv($rv2))
  | `(rv($rv1:rvalue <= $rv2:rvalue)) => `(RValue.Leq rv($rv1) rv($rv2))
  | `(rv(($rv:rvalue))) => `(rv($rv))
  | `(rv($id:ident)) => `($id)
  | `(rv(int $i:term)) => `(RValue.Int $i)
  | `(rv(bool $i:term)) => `(RValue.Bool $i)
  | `(rv(loc $L:term)) => `(RValue.Loc $L)
  | `(rv(val $v:term)) => `(↑$v)
  | `(rv(pair($rv1:rvalue, $rv2:rvalue))) => `(RValue.Pair rv($rv1) rv($rv2))


delab_rule RValue.ofVal
  | `($_ $v) => `(↑$v)

delab_rule RValue.Bool
  | `($_ «false») => `(rv(false))
  | `($_ «true») => `(rv(true))

delab_rule RValue.Poison
  | `($_) => `(rv(poison))

delab_rule RValue.Ptr
  | `($_ p($p)) => `(rv(ptr $p))

delab_rule RValue.Copy
  | `($_ p($p)) => `(rv(copy $p))

delab_rule RValue.Add
  | `($_ rv($rv1) rv($rv2)) => `(rv($rv1 + $rv2))

delab_rule RValue.Sub
  | `($_ rv($rv1) rv($rv2)) => `(rv($rv1 - $rv2))

delab_rule RValue.Mul
  | `($_ rv($rv1) rv($rv2)) => `(rv($rv1 * $rv2))

delab_rule RValue.Leq
  | `($_ rv($rv1) rv($rv2)) => `(rv($rv1 <= $rv2))

delab_rule RValue.Int
  | `($_ $i) => `(rv(int $i))

delab_rule RValue.Loc
  | `($_ $i) => `(rv(loc $i))

delab_rule RValue.ofVal
  | `($_ ↑$i) => `(rv(val $i))

delab_rule RValue.Pair
  | `($_ rv($rv1) rv($rv2)) => `(rv(pair($rv1, $rv2)))


end Notations

















namespace PlaceEctxtItem


theorem fillItem_inj {PC : PlaceEctxtItem} : Function.Injective PC.fillItem := by
  intro P P' <;> cases PC <;> cases P <;> cases P' <;> simp [PlaceEctxtItem.fillItem]

theorem fillItem_val (P : Place) (PC : PlaceEctxtItem) :
    (toVal (PC.fillItem P)).isSome →
    (Place.toVal P).isSome
:= by
  cases PC <;> cases P <;> simp!

theorem fillItem_no_val_inj {P1 P2 : Place} (PC1 PC2 : PlaceEctxtItem) :
    ProgramLogic.toVal P1 = none → ProgramLogic.toVal P2 = none →
    PC1.fillItem P1 = PC2.fillItem P2 →
    PC1 = PC2
:= by
  cases PC1 <;> cases PC2 <;> cases P1 <;> cases P2 <;> simp [PlaceEctxtItem.fillItem]

theorem toVal_eq_none_fill {P : Place} (PC : PlaceEctxtItem) :
    ProgramLogic.toVal P = none → ProgramLogic.toVal (PC.fillItem P) = none
:= by cases PC <;> simp [ProgramLogic.toVal]

theorem primStep_fill {P : Place} {σ : State} {obs P' σ'} (PC : PlaceEctxtItem) :
    (P, σ) -<obs>-> (P', σ', []) →
    (PC.fillItem P, σ) -<[]>-> (PC.fillItem P', σ, [])
:= by
  intro Hstep
  have ⟨rfl, rfl⟩ : σ = σ' ∧ [] = obs := by
    rcases _:Hstep with ⟨⟨_⟩⟩
    grind
  apply EctxLanguage.primStep_of_baseStep
  constructor <;> try trivial
  apply baseStep.PContext (PC := PC) <;> try trivial

theorem primStep_fill_inv {P : Place} {σ : State} {obs rv' σ'} (PC : PlaceEctxtItem) :
    Place.toVal P = .none →
    (PC.fillItem P, σ) -<obs>-> (rv', σ', Ps) →
    ∃ P', rv' = PC.fillItem P' ∧ (P, σ) -<[]>-> (P', σ, [])
:= by
  intro _ Hstep
  generalize hrv : PC.fillItem P = rv at Hstep
  simp [PrimStep.primStep] at Hstep
  rcases Hstep with ⟨Hstep, rfl, rfl, rfl⟩
  rename_i rv rv' K
  have HK : K = [] := by
    clear Hstep
    induction K generalizing rv
    case nil => trivial
    case cons k K IH =>
      have HK : K = [] := IH hrv
      subst HK
      cases PC <;> cases k <;>
      simp! [fillItem, ProgramLogic.fillItem] at hrv
  subst HK
  simp at *
  cases Hstep with
  | PContext PC' P0 P0' =>
    have Heq : PC = PC' := by
      apply fillItem_no_val_inj (P1 := P) (P2 := P0)
      · trivial
      · apply Place.Language.val_stuck
        assumption
      · cases PC <;> simp [fillItem] <;> grind
    subst Heq
    have Heq : P = P0 := by
      apply fillItem_inj (PC := PC)
      cases PC <;> simp at * <;> grind
    subst Heq
    cases PC <;> simp [PlaceEctxtItem.fillItem] at * <;> grind
  | _ => cases PC <;> simp! at hrv <;> grind

@[grind =>]
theorem fillItem_not_val (PCi : PlaceEctxtItem) (P : Place) : (ToVal.toVal P) = none → (ToVal.toVal (PCi.fillItem P)) = none := by
  simp [ProgramLogic.toVal] at *
  grind only [!fillItem_val, Option.not_isSome_iff_eq_none, ProgramLogic.toVal]

end PlaceEctxtItem










instance AddPureExec : Language.PureExec True 1 rv((int i) + (int j)) rv(int (i + j)) := by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (Int (i + j)), σ, []
    apply EctxLanguage.primStep_of_baseStep
    constructor <;> grind [baseStep]
  · intro σ1 σ2 _ _ _ Hstep
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
    · grind [cases baseStep]
    · apply EctxItemLanguage.subredexes_are_values
      intro C s H
      cases C <;> simp! [fillItem] at * <;> cases H <;> subst_eqs <;> simp [ProgramLogic.toVal, RValue.toVal]

instance SubPureExec : Language.PureExec True 1 rv((int i) - (int j)) rv(int (i - j)) := by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (Int (i - j)), σ, []
    apply EctxLanguage.primStep_of_baseStep
    constructor <;> grind [baseStep]
  · intro σ1 σ2 _ _ _ Hstep
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
    · grind [cases baseStep]
    · apply EctxItemLanguage.subredexes_are_values
      intro C s H
      cases C <;> simp! [fillItem] at * <;> cases H <;> subst_eqs <;> simp [ProgramLogic.toVal, RValue.toVal]

instance MulPureExec : Language.PureExec True 1 rv((int i) * (int j)) rv(int (i * j)) := by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (Int (i * j)), σ, []
    apply EctxLanguage.primStep_of_baseStep
    constructor <;> grind [baseStep]
  · intro σ1 σ2 _ _ _ Hstep
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
    · grind [cases baseStep]
    · apply EctxItemLanguage.subredexes_are_values
      intro C s H
      cases C <;> simp! [fillItem] at * <;> cases H <;> subst_eqs <;> simp [ProgramLogic.toVal, RValue.toVal]

instance LeqPureExec : Language.PureExec True 1 rv((int i) <= (int j)) rv(bool (decide (i <= j))) := by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists rv(bool (decide (i <= j))), σ, []
    apply EctxLanguage.primStep_of_baseStep
    constructor <;> grind [baseStep]
  · intro σ1 σ2 _ _ _ Hstep
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
    · grind [cases baseStep]
    · apply EctxItemLanguage.subredexes_are_values
      intro C s H
      cases C <;> simp! [fillItem] at * <;> cases H <;> subst_eqs <;> simp [ProgramLogic.toVal, RValue.toVal]

instance PtrPureExec (L : Location) : Language.PureExec True 1 rv(ptr L) rv(loc L) := by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (RValue.Loc L), σ, []
    apply EctxLanguage.primStep_of_baseStep
    constructor <;> grind [baseStep]
  · intro σ1 σ2 _ _ _ Hstep
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
    · cases Hstep with
      | PContext PC P _ Hstep Heq =>
        cases PC <;> cases P <;> cases Heq
        have ⟨Hstep, _, _, _⟩ := EctxLanguage.baseStep_of_primStep Hstep ?_
        · cases Hstep <;> cases PC <;> simp! at *
        · apply EctxItemLanguage.subredexes_are_values
          intro PC P Heq
          cases PC <;> cases P <;> cases Heq
      | _ =>
        subst_eqs <;>
        simp
    · apply EctxItemLanguage.subredexes_are_values
      intro C s H
      cases C <;> simp [fillItem, EctxItem.fillItem] at *




variable [CommonGS hlc GF]

instance : IrisGS_gen hlc RValue GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

variable {s : Stuckness} {E : CoPset} {φ : Value -> IProp GF}


theorem wp_add (i j : _root_.Int) :
  ▷ WP rv(int (i + j)) @ s; E {{ φ }} ⊢ WP rv((int i) + (int j)) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_sub (i j : _root_.Int) :
  ▷ WP rv(int (i - j)) @ s; E {{ φ }} ⊢ WP rv((int i) - (int j)) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_mul (i j : _root_.Int) :
  ▷ WP rv(int (i * j)) @ s; E {{ φ }} ⊢ WP rv((int i) * (int j)) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_leq (i j : _root_.Int) :
  ▷ WP rv(bool (decide (i <= j))) @ s; E {{ φ }} ⊢ WP rv((int i) <= (int j)) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_ptr (L : Location) :
  ▷ WP rv(loc L) @ s; E {{ φ }} ⊢ WP rv(ptr L) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_copy (L : Location) (v : Value) :
  ▷ L ↦{q} v -∗
  ▷(L ↦{q} v -∗ φ v) -∗
  WP rv(copy L) @ s; E {{ φ }}
:= by
  iintro >HL Hφ
  iapply wp_lift_atomic_step rfl
  iintro %σ %_ %_ %_ %_ Hσ !>
  ihave %_ : ⌜σ.heap[L]? = some v⌝ $$ [HL Hσ]
  · iapply bupd_elim
    iapply genHeap_valid
    simp [Iris.stateInterp]
    iframe
  ihave %Hred : ⌜BaseStep.Reducible (Copy L, σ)⌝ $$ []
  · ipureintro
    exists [], v, σ, []
    constructor <;> try trivial
    constructor <;> trivial
  isplitr
  · ipureintro
    cases s <;> try trivial
    apply EctxLanguage.primStep_reducible_of_baseStep_reducible
    assumption
  · inext
    iintro %rv %σ %rvs %Hstep - !>
    have ⟨Hstep, _, _⟩ := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Hstep
    cases _:Hstep with
    | PContext PC P _ Hstep' =>
      exfalso
      have Hirred : PrimStep.Irreducible (Place.Loc L, σ) := by
        apply EctxLanguage.primStep_irreducible_of_baseStep_irreducible
        · intro _ _ _ _ Hstep'
          have ⟨Hstep', _, _, _⟩ := Hstep'
          cases Hstep' <;> simp! at *
        · apply EctxItemLanguage.subredexes_are_values
          intro C P H
          cases C <;> cases H
      cases PC <;> cases P <;> subst_eqs <;> apply Hirred <;> assumption
    | Copy L v' =>
      obtain : v = v' := by grind
      subst_eqs
      iframe
      isplitl [Hφ HL]
      · iexists v
        isplit
        · ipureintro
          simp [ProgramLogic.toVal, toVal_coe]
        · iapply Hφ $$ [HL]; iassumption
      simp
      iempintro


theorem wp_alloc :
  ▷ (∀ (L : Location), L ↦ .Poison -∗ WP rv(loc L) @ s; E {{ φ }}) ⊢
  WP Alloc @ s; E {{ φ }}
:= by
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (by simp); iintro Hclose
  have : BaseStep.Reducible (Alloc, σ) := by
    obtain ⟨L, HL⟩ : ∃ (L : Location), σ.heap[L]? = none := by
      exists (List.fresh σ.heap.keys).choose
      simpa [get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
        using (List.fresh σ.heap.keys).choose_spec
    exists [], rv(loc L), {σ with heap := Std.insert σ.heap L .Poison}, []
    constructor <;> try trivial
    constructor <;> trivial
  isplitr
  · ipureintro
    cases s <;> simp [Stuckness.MaybeReducible]
    apply EctxLanguage.primStep_reducible_of_baseStep_reducible
    assumption
  iintro !> %rv' %σ' %rvs %Hstep -
  obtain ⟨L, HL, rfl, rfl, rfl, rfl⟩ : ∃ L, σ.heap[L]? = none ∧ rv' = rv(loc L) ∧ [] = obs ∧ [] = rvs ∧ σ' = {σ with heap := Std.insert σ.heap L .Poison} := by
    obtain ⟨Hstep', rfl, rfl⟩ := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible (by assumption) Hstep
    cases Hstep' with
    | PContext PCi => cases PCi <;> grind
    | Alloc L => exists L
  ihave >⟨Hσ', HL, -⟩ := genHeap_alloc HL $$ Hσ
  imod Hclose; iclear Hclose; imodintro
  ispecialize Hwp $$ HL
  simp
  iframe



theorem wp_place (PCi : PlaceEctxtItem) (PC : Place.Ectx) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (PCi.fillItem (fill PC ↑L)) @ s; E {{ φ }} ) }} ⊢
  WP (PCi.fillItem (fill PC P)) @ s; E {{ φ }}
:= by
  iloeb as IH generalizing %P
  rw [wp_unfold.to_eq]
  unfold wp.pre
  cases HeqP : (ProgramLogic.toVal P)
  case some L =>
    cases P <;> simp [ProgramLogic.toVal] at HeqP <;> subst HeqP
    iapply fupd_wp
  case none =>
    rw (occs := [1]) [wp_unfold.to_eq]
    have H : ProgramLogic.toVal (PCi.fillItem (fill PC P)) = none := by
      cases PCi <;> simp! [ProgramLogic.toVal]
    simp only [wp.pre, H]
    iintro Hwp %σ %ns %obs %obs' %nt Hσ
    imod Hwp $$ %σ %ns %obs %obs' %nt Hσ with ⟨%HstepP, Hwp⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at *
      rcases HstepP with ⟨obs, P', σ', Ps, HstepP⟩
      apply EctxLanguage.primStep_reducible_of_baseStep_reducible
      have ⟨_, _, _⟩: σ = σ' ∧ obs = [] ∧ Ps = [] := by
        rcases HstepP with ⟨⟨_, _, _, _⟩⟩
        subst_eqs
        simp
      subst_eqs
      exists [], PCi.fillItem (fill PC P'), σ, []
      constructor <;> try trivial
      apply baseStep.PContext PCi (fill PC P) <;> try trivial
      apply Language.Context.primStep_fill
      assumption
    iintro %rv' %σ' %rvs %Hstep creds
    have ⟨rfl, rfl, rfl⟩ : [] = obs ∧ [] = rvs ∧ σ = σ' := by
      generalize hrv : PCi.fillItem _ = rv at *
      have : BaseStep.Reducible (rv, σ) := by
        apply EctxLanguage.baseStep_reducible_of_primStep_reducible
        constructor
        exists rv', σ', rvs
        apply EctxItemLanguage.subredexes_are_values
        intro C _ H
        subst_vars
        cases C <;> cases PCi <;> simp at H
      obtain ⟨Hstep', rfl, rfl⟩ := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible this Hstep
      simp
      cases Hstep' <;> grind
    have HtoVal : ToVal.toVal (fill PC P) = none := by
      apply EctxLanguage.fill_not_val
      assumption
    obtain ⟨_, rfl, Hstep'⟩ := PlaceEctxtItem.primStep_fill_inv (P := fill PC P) PCi HtoVal Hstep
    obtain ⟨P', rfl, Hstep''⟩ := Language.Context.primStep_fill_inv HeqP Hstep'

    ispecialize Hwp $$ %P' %σ %([]) %Hstep'' creds

    simp! [Nat.repeat, IrisGS_gen.numLatersPerStep]
    imod Hwp; imodintro; inext; imod Hwp; imodintro
    imod Hwp with ⟨_, Hwp, -⟩
    ispecialize IH $$ %P' [Hwp //]
    iframe
    imodintro
    iempintro

theorem wp_place' (PCi : PlaceEctxtItem) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (PCi.fillItem ↑L) @ s; E {{ φ }} ) }} ⊢
  WP (PCi.fillItem P) @ s; E {{ φ }}
:= by
  have' Hwp := wp_place (GF := GF) PCi empty
  simp [EvContext.fill_empty] at Hwp
  apply Hwp












theorem adequacy [CommonGS .hasLC GF] (rv : RValue) σ (φ : Value → Prop)
  (Hwp : ∀ [CommonGS .hasLC GF], ⊢@{IProp GF} (WP rv {{ v, ⌜φ v⌝ }})) :
  adequate .NotStuck rv σ (fun v _ => φ v)
:= by
  apply wp_adequacy (GF := GF)
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (.own 1)
      (Std.PartialMap.map (toAgree ⟨·⟩) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (.own 1)
      (Std.PartialMap.map (toAgree ⟨·⟩) ∅))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI : CommonGS .hasLC GF := ⟨γh, γm⟩
  imodintro
  iexists (fun σ _ => Iris.genHeapInterp σ.heap)
  iexists (fun _ => iprop(True))
  simp only
  ihave #Hwp := (@Hwp _)
  iframe Hwp
  simp only [Iris.genHeapInterp]
  iexists ∅
  unfold ghost_map_auth
  iframe Hh Hm
  ipureintro
  intro k hk
  simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk










end RValue
