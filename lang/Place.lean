import Lang.Common

open Iris Std ProgramLogic Language.Notation


inductive Place
  | Var (x : TermVar)
  | Loc (L : Location)
  | Deref (P : Place)
  | Fst (P : Place)
  | Snd (P : Place)
deriving BEq, DecidableEq

namespace Place

@[reducible]
def toVal (P : Place) : Option Location := match P with
  | Loc L => some L
  | _ => none

@[reducible]
def ofVal : Location -> Place := Loc

instance : Coe Location Place where
  coe := ofVal

@[simp]
def subst (P' : Place) (x : TermVar) (P : Place) : Place := match P' with
  | Var y => if x = y then P else P'
  | Loc _ => P'
  | Deref P' => Deref (P'.subst x P)
  | Fst P' => Fst (P'.subst x P)
  | Snd P' => Snd (P'.subst x P)

inductive EctxItem
  | Deref

@[reducible, simp]
def EctxItem.fillItem (C : EctxItem) (P : Place) : Place := match C with
  | Deref => .Deref P

theorem EctxItem.fillItem.inj (C : EctxItem) : Function.Injective (fillItem C) := by
  simp! [Function.Injective]

inductive baseStep (σ : State) : Place -> Place -> Prop
  | Deref :
    -- *L -p> m(l)
    σ.heap[L]? = some (Value.Loc L') ->
    baseStep σ (Deref (Loc L)) (Loc L')
  | Fst (L : Location) :
    baseStep σ (Fst (Loc L)) L.Fst
  | Snd (L : Location) :
    baseStep σ (Snd (Loc L)) L.Snd

instance EctxItemLanguage : EctxItemLanguage Place EctxItem State Unit Location where
  toVal := toVal
  ofVal := ofVal
  coe_of_toVal_eq_some {P L} _ := by
    cases P <;> simp_all!
  toVal_coe _ := by rfl
  baseStep c obs c' :=
    let (P, σ) := c
    let (P', σ', Ps) := c'
    baseStep σ P P' ∧
    σ = σ' ∧
    obs = [] ∧
    Ps = []
  fillItem := EctxItem.fillItem
  fillItem_inj _ := by
    apply EctxItem.fillItem.inj
    assumption
  fillItem_val := by simp!
  fillItem_no_val_inj := by simp!
  val_stuck Hred := by grind [cases baseStep]
  base_ctx_step_val {C} := by
    simp
    intro _ _ Hred
    cases Hred <;> cases C <;> simp! <;> grind [cases baseStep]

abbrev Ectx := List EctxItem

instance EctxLanguage : EctxLanguage Place Ectx State Unit Location := by infer_instance

instance Language : Language Place State Unit Location := by infer_instance



section Notations

declare_syntax_cat place

syntax "p(" place ")" : term
-- identifier are escaped
syntax ident : place
-- strings are interpreted as variables
syntax str : place
syntax "*" place : place
syntax place ".0" : place
syntax place ".1" : place

macro_rules
  | `(p($x:ident)) => `((↑$x : Place))
  | `(p($s:str)) => `(Place.Var $s)
  | `(p(*$p:place)) => `(Place.Deref p($p))
  | `(p($p:place.0)) => `(Place.Fst p($p))
  | `(p($p:place.1)) => `(Place.Snd p($p))

delab_rule Place.ofVal
  | `($_ $L:ident) => `(p($L:ident))

delab_rule Place.Var
  | `($_ $s:str) => `(p($(Lean.mkIdent $ Lean.Name.mkSimple s.getString):ident))

delab_rule Place.Deref
  | `($_ p($p)) => `(p(*$p))

delab_rule Place.Fst
  | `($_ p($p)) => `(p($p.0))

delab_rule Place.Snd
  | `($_ p($p)) => `(p($p.1))

end Notations





theorem keep_state (P : Place) : (P, σ) -<obs>-> (P', σ', Ps) -> σ = σ' := by
  simp [PrimStep.primStep]
  intro Hstep
  rcases Hstep with ⟨⟨_⟩⟩
  grind




variable [CommonGS hlc GF]

instance : IrisGS_gen hlc Place GF where
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Location -> IProp GF}

theorem wp_deref (L L': Location) :
  ▷ L ↦{q} ↑L' -∗
  ▷ (L ↦{q} ↑L' -∗ φ L') -∗
  WP p(*L) @ s; E {{ φ }}
:= by
  iintro >HL Hφ
  iapply wp_lift_atomic_step rfl
  iintro %σ %_ %_ %_ %_ Hσ !>
  ihave %_ : ⌜σ.heap[L]? = some ↑L'⌝ $$ [HL Hσ]
  · iapply bupd_elim
    iapply genHeap_valid
    simp [Iris.stateInterp]
    iframe
  ihave %Hred : ⌜BaseStep.Reducible (p(*L), σ)⌝ $$ []
  · ipureintro
    exists [], (Place.Loc L'), σ, []
    constructor <;> try trivial
    constructor <;> trivial
  isplitr
  · ipureintro
    cases s <;> try trivial
    apply EctxLanguage.primStep_reducible_of_baseStep_reducible
    assumption
  · inext
    iintro %P %σ %Ps %Hstep - !>
    have ⟨Hstep, _, _, _⟩ := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Hstep
    cases Hstep
    rename_i L'' _
    have : L' = L'' := by grind
    subst_eqs
    iframe
    isplitl [Hφ HL]
    · iexists _
      isplit
      · ipureintro
        rfl
      · iapply Hφ $$ [HL]; iassumption
    simp
    iempintro



















theorem adequacy [CommonGS .hasLC GF] (P : Place) σ (φ : Location → Prop)
  (Hwp : ∀ [CommonGS .hasLC GF], ⊢@{IProp GF} (WP P {{ v, ⌜φ v⌝ }})) :
  adequate .NotStuck P σ (fun v _ => φ v)
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
