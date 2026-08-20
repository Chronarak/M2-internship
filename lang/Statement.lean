import Lang.RValue
import Lang.ContextItem

open Iris Std ProgramLogic Language.Notation


abbrev FunName := String


inductive Statement
  | Assign (P : Place) (rv : RValue)
  | IfThenElse (rv : RValue) (b1 b2 : List Statement)
  | Call (P : Place) (f : FunName) (args : List RValue)
  | Return (rv : RValue)
  | Free (P : Place)
deriving BEq

abbrev Block := List Statement








namespace Statement

@[simp]
def subst (s : Statement) (x : TermVar) (P : Place) : Statement := match s with
  | Assign P' rv => Assign (P'.subst x P) (rv.subst x P)
  | IfThenElse rv b1 b2 =>
    let b1 := b1.map (subst · x P)
    let b2 := b2.map (subst · x P)
    IfThenElse (rv.subst x P) b1 b2
  | Call P' f args => Call (P'.subst x P) f (args.map (·.subst x P))
  | Return rv => Return (rv.subst x P)
  | Free P' => Free (P'.subst x P)


-- is the first statement we will execute a return
@[grind, grind cases]
inductive NoReturn : Statement -> Prop where
  | Assign : NoReturn (Assign P r)
  | IfThenElse :
    (∀ s, s ∈ b1 -> NoReturn s) ->
    (∀ s, s ∈ b2 -> NoReturn s) ->
    NoReturn (IfThenElse rv b1 b2)
  | Call : NoReturn (Call P f args)
  | Free : NoReturn (Free P)

-- is the first statement we will execute a call
@[grind, grind cases]
inductive NoCall : Statement -> Prop where
  | Assign : NoCall (Assign P r)
  | IfThenElse :
    (∀ s, s ∈ b1 -> NoCall s) ->
    (∀ s, s ∈ b2 -> NoCall s) ->
    NoCall (IfThenElse rv b1 b2)
  | Return : NoCall (Return rv)
  | Free : NoCall (Free P)



@[grind cases]
inductive RValueEctxtItem
  | Assign (L : Location)
  | IfThenElse (b1 b2 : Block)
  | Call (L : Location) (f : FunName) (argsl : List Value) (argsr : List RValue)
  | Return

@[reducible, simp]
def RValueEctxtItem.fillItem (RC : RValueEctxtItem) (rv : RValue) : Statement := match RC with
  | Assign L => Statement.Assign L rv
  | IfThenElse b1 b2 => Statement.IfThenElse rv b1 b2
  | Call L f argsl argsr => Statement.Call L f (argsl.map (↑·) ++ rv :: argsr)
  | Return => Statement.Return rv

@[grind cases]
inductive PlaceEctxtItem
  | Assign (rv : RValue)
  | Call (f : String) (args : List RValue)
  | RContext (RC : RValueEctxtItem) (PC : RValue.PlaceEctxtItem)
  | Free

@[reducible, simp]
def PlaceEctxtItem.fillItem (PC : PlaceEctxtItem) (P : Place) : Statement := match PC with
  | Assign rv => Statement.Assign P rv
  | Call f args => Statement.Call P f args
  | RContext RC PC => RC.fillItem (PC.fillItem P)
  | Free => Statement.Free P


-- TODO : body should be a List Statement (if we remove skip)
-- or Statement × List Statement otherwise
structure FunDef where
  body : Block
  args : List TermVar
  locals : List TermVar

-- variablex are boxed, so we need an added deref to have intuitive semantics
-- this is not needed for locals, as we just put poison into them
def FunDef.substVars (f : FunDef) (Largs Llocals : List Location) : Block :=
  f.body.map (
    (f.args.zip Largs).foldr (fun (x, L) s => s.subst x L) ∘
    (f.locals.zip Llocals).foldr (fun (x, L) s => s.subst x ↑L)
  )

abbrev _FunDefs := ExtTreeMap FunName
abbrev FunDefs := _FunDefs FunDef

structure StackFrame where
  -- return address
  ret : Location
  -- continuation
  next : Block
deriving Inhabited

structure Kontinuation where
  stack : List StackFrame
deriving Inhabited

instance : EmptyCollection Kontinuation where
  emptyCollection := {stack := ∅}

def Kontinuation.push (k : Kontinuation) (sf : StackFrame) : Kontinuation :=
  {stack := sf :: k.stack}

@[grind unfold]
def Kontinuation.pop? (k : Kontinuation) : Option (StackFrame × Kontinuation) := do
  let sf <- k.stack.head?
  let stack <- k.stack.tail?
  return (sf, {stack})

abbrev Configuration := Block × Kontinuation



inductive baseStep (Γ : FunDefs) : Configuration × State -> Configuration × State -> Prop
  | Assign (b : Block) (L :Location) (v : Value) :
    P = ↑L ->
    rv = ↑v ->
    σ' = {σ with heap := insert σ.heap L v} ->
    baseStep Γ ((Assign P rv :: b, k), σ) ((b, k), σ')
  | IfThenElseTrue (b b1 b2 : Block) :
    baseStep Γ ((IfThenElse Bool.true b1 b2 :: b, k), σ) ((b1 ++ b, k), σ)
  | IfThenElseFalse (b b1 b2 : Block) :
    baseStep Γ ((IfThenElse Bool.false b1 b2 :: b, k), σ) ((b2 ++ b, k), σ)
  | Call (next : Block) (ret : Location) (fn : FunDef) (argsv : List Value) (Largs Llocals : List Location) :
    P = ↑ret ->
    args = argsv.map ToVal.ofVal ->
    Γ[f]? = some fn ->
    argsv.length = fn.args.length ->
    Largs.length = fn.args.length ->
    Llocals.length = fn.locals.length ->
    (∀ L, L ∈ Largs -> get? σ.heap L = none) ->
    (∀ L, L ∈ Llocals -> get? σ.heap L = none) ->
    Largs.Nodup ->
    Llocals.Nodup ->
    Largs.Disjoint Llocals ->
    -- we allocate args and locals
    (σ' : State) = (PartialMap.ofList (Largs.zip argsv ++ Llocals.map (·, Value.Poison)) : Memory) ++ σ ->
    -- we push a stack frame
    k' = k.push {ret, next} ->
    b = fn.substVars Largs Llocals ->
    baseStep Γ ((Call P f args :: next, k), σ) ((b, k'), σ')
  | Return (b next : Block) (ret : Location) (v : Value):
    (rv : RValue) = ↑v ->
    some ({ret, next}, k') = k.pop? ->
    baseStep Γ ((Return rv :: b, k), σ) ((Assign ↑ret rv :: next, k'), σ)
  | Free (L : Location) :
    σ' = {σ with heap := delete σ.heap L} ->
    baseStep Γ ((Free ↑L :: b, k), σ) ((b, k), σ')
  | PContext (b : Block) (PC : PlaceEctxtItem) (P P' : Place) :
    -- P -p> P' => PC[P] -s> PC[P']
    (P, σ) -<[]>-> (P', σ, []) ->
    s  = PC.fillItem P  ->
    s' = PC.fillItem P' ->
    baseStep Γ ((s :: b, k), σ) ((s' :: b, k), σ)
  | RContext (b : Block) (RC : RValueEctxtItem) (rv rv' : RValue) :
    -- rv -rv> rv' => RC[rv] -s> RC[rv']
    (rv, σ) -<[]>-> (rv', σ', []) ->
    s  = RC.fillItem rv  ->
    s' = RC.fillItem rv' ->
    baseStep Γ ((s :: b, k), σ) ((s' :: b, k), σ')


structure StateFn extends State where
  funDefs : FunDefs
deriving Inhabited

instance Language : Language Configuration StateFn Unit Unit where
  toVal := fun (b, k) => match b, k with
    | [] , {stack := []} => some ()
    | _, _ => none
  ofVal := fun () => (∅, ∅)
  coe_of_toVal_eq_some {s v} H := by
    simp [EmptyCollection.emptyCollection]
    grind
  toVal_coe v := by cases v <;> rfl
  primStep c obs c' :=
    let (sk, σ) := c
    let (s'k', σ', ss) := c'
    baseStep σ.funDefs (sk, σ.toState) (s'k', σ'.toState) ∧
    obs = [] ∧
    ss = [] ∧
    σ.funDefs = σ'.funDefs
  val_stuck := by
    simp
    intro _ _ σ _ _ _ _ _ Hred
    cases σ
    cases Hred with
    | PContext PC _ _ _ => cases PC <;> simp! at * <;> grind
    | RContext RC => cases RC <;> simp! at * <;> grind
    | _ => simp


section Notations

declare_syntax_cat statement
declare_syntax_cat stBlock

syntax:max "s(" statement ")" : term

syntax ident : statement -- allow for escaping ident
syntax place " := " rvalue : statement
syntax "if " rvalue " then " stBlock " else" stBlock : statement
syntax "(" statement ")" : statement
syntax place " := " "call " str "(" rvalue,* ")" : statement
syntax "return " rvalue : statement
syntax "free " place : statement


syntax:max "sb(" stBlock ")" : term

syntax ident : stBlock
syntax "skip" : stBlock
syntax statement : stBlock
syntax statement ";" stBlock : stBlock


macro_rules
  | `(s($id:ident)) => `($id)
  | `(s($p:place := $rv:rvalue)) => `(Statement.Assign p($p) rv($rv))
  | `(s(if $rv:rvalue then $b1:stBlock else $b2:stBlock)) => `(Statement.IfThenElse rv($rv) sb($b1) sb($b2))
  | `(s(($s:statement))) => `(s($s))
  | `(s($p:place := call $f:str ($args,*))) => do
    let args <- args.getElems.foldrM
      (fun rv args => do return (<-`(rv($rv) :: $args)))
      (<-`([]))
    `(Statement.Call p($p) $f $args)
  | `(s(return $rv:rvalue)) => `(Statement.Return rv($rv))
  | `(s(free $p:place)) => `(Statement.Free p($p))

macro_rules
  | `(sb($id:ident)) => `($id)
  | `(sb(skip)) => `(([] : Block))
  | `(sb($s:statement)) => `([s($s)])
  | `(sb($s:statement; $sts:stBlock)) => `(s($s) :: sb($sts))

delab_rule Statement.Assign
  | `($_ p($p) rv($rv)) => `(s($p:place := $rv:rvalue))

delab_rule Statement.IfThenElse
  | `($_ rv($rv) sb($b1) sb($b2)) => `(s(if $rv:rvalue then $b1:stBlock else $b2:stBlock))

delab_rule Statement.Call
  | `($_ p($p:place) $f:str $_) => `(s($p:place := call $f:str (copy "TODO : unexpand arglists")))

delab_rule Statement.Return
  | `($_ rv($rv)) => `(s(return $rv))

delab_rule Statement.Free
  | `($_ p($p)) => `(s(free $p))

open Lean PrettyPrinter Delaborator SubExpr Meta

@[app_delab List.nil]
def delabNilBlock : Delab := do
  let b <- getExpr
  let ty <- inferType b
  if <- isDefEq ty (mkConst ``Block) then `(sb(skip))
  else failure

@[app_delab List.cons]
def delabConstBlock : Delab := do
  let b <- getExpr
  guard $ b.isAppOfArity `List.cons 3
  if <- isDefEq (<- inferType b) (mkConst ``Block) then
    let s <- withAppFn (withAppArg delab)
    let b <- withAppArg delab
    let s <- match s with
      | `(s($s:statement)) => pure s
      | _ => failure
    let b <- match b with
      | `(sb($b:stBlock)) => pure b
      | _ => failure
    `(sb($s:statement; $b:stBlock))
  else failure


end Notations









theorem reducible_fill (b1 b2 : Block) (k : Kontinuation) :
  PrimStep.Reducible ((b1, k), σ) → PrimStep.Reducible ((b1 ++ b2, k), σ)
:= by
  intro ⟨obs, ⟨b', k'⟩, σ', sts, Hstep⟩
  rcases Hstep with ⟨Hstep, rfl, rfl, HfunDefs⟩
  exists []
  generalize Hσs : σ.toState = σs at *
  generalize Hs' : b' = b' at *
  generalize Hk' : k' = k' at *
  generalize Hσ' : σ' = σ' at *
  cases Hstep with
  | Call next ret fn argsv Largs Llocals =>
    exists (fn.substVars Largs Llocals, k.push {ret, next := next ++ b2}), ?_, []
    constructor <;> try grind
    apply baseStep.Call (next ++ b2) ret fn argsv Largs Llocals <;> grind
  | Return b next ret v Hrv =>
    subst Hrv
    obtain rfl : σ = σ' := by grind [cases StateFn]
    exists (Assign ↑ret ↑v :: next, k'), σ, []
    constructor <;> try grind
    apply baseStep.Return (b ++ b2) next ret v rfl
    grind
  | PContext b PC P P' =>
    exists (PC.fillItem P' :: b ++ b2, k), σ, []
    constructor <;> try trivial
    apply baseStep.PContext (b ++ b2) PC P P' <;> grind
  | RContext b RC rv rv' =>
    exists (RC.fillItem rv' :: b ++ b2, k), σ', []
    constructor <;> try trivial
    apply baseStep.RContext (b ++ b2) RC rv rv' <;> try grind
  | _ =>
    exists (b' ++ b2, k'), σ', []
    constructor <;> try trivial
    grind [baseStep]























-- some misc lemmas to handle arglists

@[simp]
theorem args_val_unsplittable [ToVal Expr Val]
    {argsv argsl : List Val}
    {arg : Expr} (Harg : ToVal.toVal arg = none)
    {argsr : List Expr} :
  ¬ argsv.map ToVal.ofVal = argsl.map ToVal.ofVal ++ arg :: argsr
:= by
  induction argsv generalizing argsl <;> grind [cases List]

theorem args_val_split_inj [ToVal Expr Val]
    {argsl1 argsl2 : List Val}
    {arg1 arg2 : Expr} (Harg1 : ToVal.toVal arg1 = none) (Harg2 : ToVal.toVal arg2 = none)
    {argsr1 argsr2 : List Expr} :
  argsl1.map ToVal.ofVal ++ arg1 :: argsr1 = argsl2.map ToVal.ofVal ++ arg2 :: argsr2 ->
  argsl1 = argsl2 ∧ arg1 = arg2 ∧ argsr1 = argsr2
:= by
  induction argsl1 generalizing argsl2 <;>
  induction argsl2 <;>
  -- TODO : report typo
  grind [ToVal.TovVal.ofVal_inj]








namespace RValueEctxtItem

@[grind inj]
theorem fillItem_inj {RC : RValueEctxtItem} : Function.Injective RC.fillItem := by
  intro P P' <;> cases RC <;> cases P <;> cases P' <;> simp [fillItem] at *

-- theorem fillItem_val (rv : RValue) {k : Kontinuation} (RC : RValueEctxtItem) :
--     (ToVal.toVal (RC.fillItem rv, k)).isSome →
--     (ToVal.toVal rv).isSome
-- := by
--   cases RC <;> cases rv <;> simp [ToVal.toVal]

theorem fillItem_no_val_inj {rv1 rv2 : RValue} (RC1 RC2 : RValueEctxtItem) :
    ToVal.toVal rv1 = none → ToVal.toVal rv2 = none →
    fillItem RC1 rv1 = fillItem RC2 rv2 →
    RC1 = RC2
:= by
  cases RC1 <;> cases RC2
  case Call.Call _ _ argsl1 argsr1 _ _ argsl2 argsr2 =>
    simp at *
    intro Hrv1 Hrv2 rfl rfl Hargs
    have := args_val_split_inj Hrv1 Hrv2 Hargs
    grind
  all_goals
    cases rv1 <;>
    cases rv2 <;>
    simp [fillItem] <;>
    grind


theorem primStep_fill {rv : RValue} {k : Kontinuation} {σ σ': StateFn} {obs rv'} (RC : RValueEctxtItem) (HfunDefs : σ.funDefs = σ'.funDefs) :
    (rv, σ.toState) -<obs>-> (rv', σ'.toState, []) →
    ((RC.fillItem rv :: b, k), σ) -<[]>-> ((RC.fillItem rv' :: b, k), σ', [])
:= by
  intro Hstep
  obtain rfl : [] = obs := by
    rcases Hstep with ⟨Hstep, _, rfl⟩
    rfl
  constructor <;> try trivial
  apply baseStep.RContext b RC rv rv' Hstep <;> trivial

theorem primStep_fill_inv {rv : RValue} {k k' : Kontinuation} {σ : StateFn} {obs s'b σ'} (RC : RValueEctxtItem) :
    ToVal.toVal rv = .none →
    ((RC.fillItem rv :: b, k), σ) -<obs>-> ((s'b, k'), σ', rvs) →
    ∃ rv', s'b = RC.fillItem rv' :: b  ∧ k = k' ∧ (rv, σ.toState) -<[]>-> (rv', σ'.toState, [])
:= by
  intro _ Hstep
  generalize hs : RC.fillItem rv = s at Hstep
  simp [PrimStep.primStep] at Hstep
  cases σ
  cases σ'
  rcases Hstep with ⟨Hstep, rfl, rfl, rfl, rfl⟩
  cases Hstep with
  | PContext _ PC P0 P0' Hstep' hs' =>
    subst hs
    cases PC with
    | RContext RC' PC' =>
      simp [PlaceEctxtItem.fillItem] at *
      have := RValue.PlaceEctxtItem.primStep_fill PC' Hstep'
      obtain rfl : RC = RC' := by
        apply fillItem_no_val_inj (rv1 := rv) (rv2 := PC'.fillItem P0)
        · assumption
        · apply RValue.PlaceEctxtItem.toVal_eq_none_fill
          apply Language.val_stuck
          assumption
        grind
      obtain rfl : rv = PC'.fillItem P0 := by
        apply fillItem_inj
        assumption
      exists PC'.fillItem P0'
    | _ =>
      have HtoVal : ProgramLogic.toVal P0 = none := by
        apply Language.val_stuck
        assumption
      obtain ⟨_, rfl⟩ : ∃ L, P0 = Place.ofVal L := by grind
      simp at HtoVal
  | RContext _ RC' rv0 rv0' =>
    subst hs
    obtain rfl : RC = RC' := by
      apply fillItem_no_val_inj (rv1 := rv) (rv2 := rv0)
      · assumption
      · apply Language.val_stuck
        assumption
      · assumption
    obtain rfl : rv = rv0 := by
      apply fillItem_inj
      assumption
    subst_eqs
    exists rv0'
  | _ =>
    cases RC <;>
    simp at hs <;>
    (repeat' rcases hs with ⟨_, hs⟩) <;>
    subst_eqs <;>
    simp [ToVal.toVal, RValue.toVal_coe] at * <;>
    exfalso <;>
    apply args_val_unsplittable (Expr := RValue) (by assumption) (by symm; assumption)


end RValueEctxtItem




namespace PlaceEctxtItem

@[grind inj]
theorem fillItem_inj {PC : PlaceEctxtItem} : Function.Injective PC.fillItem := by
  intro _ _ <;> cases PC with
  | RContext RC =>
    cases RC <;> simp <;> grind
  | _ => grind

theorem fillItem_no_val_inj {P1 P2 : Place} (PC1 PC2 : PlaceEctxtItem) :
    ToVal.toVal P1 = none → ToVal.toVal P2 = none →
    fillItem PC1 P1 = fillItem PC2 P2 →
    PC1 = PC2
:= by
  cases PC1 <;> cases PC2
  case RContext.RContext RC1 PC1' RC2 PC2' =>
    intro HtoVal1 HtoVal2 H
    have HtoVal1' : ProgramLogic.toVal (PC1'.fillItem P1) = none :=
      RValue.PlaceEctxtItem.toVal_eq_none_fill PC1' HtoVal1
    have HtoVal2' : ProgramLogic.toVal (PC2'.fillItem P2) = none :=
      RValue.PlaceEctxtItem.toVal_eq_none_fill PC2' HtoVal2
    obtain rfl : RC1 = RC2 :=
      RValueEctxtItem.fillItem_no_val_inj _ _ HtoVal1' HtoVal2' H
    simp [fillItem] at *
    apply RValue.PlaceEctxtItem.fillItem_no_val_inj _ _ HtoVal1 HtoVal2
    apply RValueEctxtItem.fillItem_inj H
  all_goals
    cases P1 <;> cases P2 <;> simp [fillItem] <;> grind

theorem primStep_fill {P : Place} {k : Kontinuation} {σ σ' : StateFn} {obs P'} (PC : PlaceEctxtItem) :
    (P, σ.toState) -<obs>-> (P', σ'.toState, []) →
    ((PC.fillItem P :: b, k), σ) -<[]>-> ((PC.fillItem P' :: b, k), σ, [])
:= by
  intro Hstep
  have ⟨H, rfl⟩ : σ'.toState = σ.toState ∧ [] = obs := by
    rcases _:Hstep with ⟨⟨_⟩⟩
    grind
  rw [H] at Hstep
  constructor <;> try trivial
  apply baseStep.PContext (PC := PC) <;> try trivial

theorem primStep_fill_inv {P : Place} {k : Kontinuation} {σ σ' : StateFn} {obs s'b} (PC : PlaceEctxtItem) :
    Place.toVal P = .none →
    ((PC.fillItem P :: b, k), σ) -<obs>-> ((s'b, k'), σ', Ps) →
    ∃ P', s'b = PC.fillItem P' :: b ∧ σ = σ' ∧ k = k' ∧ (P, σ.toState) -<[]>-> (P', σ.toState, [])
:= by
  intro HtoVal Hstep
  generalize hs : PC.fillItem P = s at Hstep
  simp [PrimStep.primStep] at Hstep
  generalize Hσs : σ.toState = σs at *
  generalize Hσ's : σ'.toState = σ's at *
  rcases Hstep with ⟨Hstep, rfl, rfl, _⟩
  cases Hstep with
  | PContext _ PC' P0 P0' =>
    obtain rfl : PC = PC' := by
      apply fillItem_no_val_inj (P1 := P) (P2 := P0)
      · trivial
      · apply Place.Language.val_stuck
        assumption
      · grind
    obtain rfl : P = P0 := by
      apply fillItem_inj (PC := PC)
      grind
    subst_eqs
    exists P0'
    grind [cases StateFn]
  | RContext _ RC rv rv' Hstep' =>
    cases PC with
    | RContext RC' PC' =>
      obtain rfl : RC = RC' := by
        apply RValueEctxtItem.fillItem_no_val_inj
        · apply Language.val_stuck
          assumption
        · apply RValue.PlaceEctxtItem.toVal_eq_none_fill PC'
          assumption
        grind
      obtain rfl : rv = PC'.fillItem P := by
        subst_eqs
        symm
        apply RValueEctxtItem.fillItem_inj
        assumption
      obtain ⟨P', rfl, Hstep''⟩ := RValue.PlaceEctxtItem.primStep_fill_inv PC' HtoVal Hstep'
      exists P'
      obtain rfl : σs = σ's := by
        have : BaseStep.Reducible (PC'.fillItem P, σs) := by
          constructor
          exists PC'.fillItem P', σs, []
          constructor <;> try trivial
          apply RValue.baseStep.PContext PC' P P' <;> trivial
        have ⟨Hstep''', rfl, rfl⟩:= EctxLanguage.baseStep_of_primStep_of_baseStep_reducible this Hstep'
        cases PC' <;> cases Hstep''' <;> simp
      grind [cases StateFn]
    | _ => grind
  | _ =>
    cases PC with
    | RContext RC' PC' =>
      have : (PC'.fillItem P).toVal = none := by
        apply RValue.PlaceEctxtItem.toVal_eq_none_fill
        assumption
      cases RC' with
      | Call =>
        exfalso
        simp at hs
        repeat rcases hs with ⟨_, hs⟩
        all_goals
          subst_eqs
          apply args_val_unsplittable (Expr := RValue)
          assumption
          symm
          assumption
      | IfThenElse => cases PC' <;> simp at hs
      | _ =>
        simp at *
        all_goals
          try (rcases hs with ⟨_, hs⟩; rw [hs] at this; clear hs)
          try (rw [hs] at this; clear hs)
          subst_vars
          simp [RValue.toVal_coe] at this
    | _ => grind


end PlaceEctxtItem












instance IfThenElseTruePureExec :
  Language.PureExec (Λ := Language) True 1 (sb((if true then b1 else b2); b), k) (b1 ++ b, k)
:= by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (b1 ++ b, k), σ, []
    constructor <;> try simp
    apply baseStep.IfThenElseTrue b b1 b2
  · intro ⟨σ, Γ⟩ ⟨σ', Γ'⟩ _ s _ ⟨Hstep, _, _, _⟩
    cases Hstep with
    | RContext _ RCi rv rv' Hstep Hrv =>
      cases RCi <;> simp at *
      obtain ⟨rfl, rfl, rfl⟩ := Hrv
      have := Language.val_stuck Hstep
      simp at this
    | _ => grind

instance IfThenElseFalsePureExec :
  Language.PureExec (Λ := Language) True 1 (sb((if false then b1 else b2); b), k) (b2 ++ b, k)
:= by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (b2 ++ b, k), σ, []
    constructor <;> try simp
    apply baseStep.IfThenElseFalse
  · intro ⟨σ, Γ⟩ ⟨σ', Γ'⟩ _ s _ ⟨Hstep, _, _, _⟩
    cases Hstep with
    | RContext _ RCi rv rv' Hstep Hrv =>
      cases RCi <;> simp at *
      obtain ⟨rfl, rfl, rfl⟩ := Hrv
      have := Language.val_stuck Hstep
      simp at this
    | _ => grind

instance ReturnPureExec (ret : Location) (v : Value) :
  Language.PureExec (Λ := Language) True 1 (Return ↑v :: b, {stack := {ret, next} :: stack}) (Assign ↑ret ↑v :: next, {stack})
:= by
  constructor
  intro _
  constructor
  constructor
  constructor
  · intro σ
    exists (Assign ↑ret ↑v :: next, {stack}), σ, []
    constructor <;> try simp
    apply baseStep.Return <;> trivial
  · intro ⟨σ, Γ⟩ ⟨σ', Γ'⟩ _ s _ ⟨Hstep, _, _, _⟩
    cases Hstep with
    | PContext _ PC P P' _ Hs' =>
      cases PC with
        | RContext RCi PC =>
          cases RCi with
            | Return =>
              simp [-RValue.PlaceEctxtItem.fillItem] at Hs'
              have : (PC.fillItem P).toVal = none := by
                apply RValue.PlaceEctxtItem.toVal_eq_none_fill
                apply Language.val_stuck
                assumption
              rw [<-Hs'] at this
              simp [RValue.toVal_coe] at this
            | _ => simp at *
        | _ => simp at *
    | RContext _ RC rv rv' _ Hrv' =>
      cases RC with
      | Return =>
        simp at *
        have : toVal rv = none := by
          apply Language.val_stuck
          assumption
        rw [<-Hrv'] at this
        simp [ToVal.toVal, RValue.toVal_coe] at this
      | _ => simp at *
    | _ => grind






section Funs

-- TODO : find a better name than funs...
-- maybe let it be env

/--
we need a map from FunNames to funDef.
In essence, this is a heap, but genHeap really has to be unique.
So we just miraculously obtain the exact same code up to
renaming and simplification, change the notation, et voila!
-/

class genFunsPreS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [Std.LawfulFiniteMap H L] where
  env : GhostMapG GF L V H

class genFunsGS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [Std.LawfulFiniteMap H L]
    extends genFunsPreS L V GF H where
  funsName : GName

attribute [reducible, instance] genFunsPreS.env
attribute [instance] GhostMapG.elem

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable [G : genFunsGS L V GF H]

open Std.FiniteMap Std.PartialMap genFunsGS

def genFunsInterp (σ : H V) : IProp GF := iprop%
  ∃ m : H GName, ⌜∀ k, dom m k → dom σ k⌝ ∗ (funsName ↪●MAP σ)

def defAs (l : L) (v : V) : IProp GF := funsName ↪◯MAP[l] v

notation:50 l:50 " ⋗ " v:50 => defAs l v

instance instTimelessDefAs : BI.Timeless (l ⋗ v) :=
  inferInstanceAs (BI.Timeless (funsName ↪◯MAP[l] v))

theorem genFuns_valid {σ : H V} {l : L} {v : V} :
    genFunsInterp σ ∗ l ⋗ v ==∗ ⌜get? σ l = .some v⌝ := by
  unfold genFunsInterp defAs
  iintro ⟨⟨%m, -, Hσ⟩, Hl⟩
  iapply ghost_map_lookup $$ Hσ Hl

end Funs










class FullGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends CommonGS hlc GF where
  funDefs : genFunsGS FunName FunDef GF _FunDefs

attribute [reducible, instance] FullGS.funDefs

variable [FullGS hlc GF]

instance : IrisGS_gen hlc Configuration GF where
  stateInterp σ n obs m := iprop(genFunsInterp σ.funDefs ∗ StateInterp.stateInterp σ.toState n obs m)
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

variable {s : Stuckness} {E : CoPset} {φ : Unit -> IProp GF}


theorem wp_assign {k : Kontinuation} (L : Location) (v v' : Value) :
  ▷ (L ↦ v') -∗
  ▷ (L ↦ v -∗ WP (b, k) @ s; E {{ φ }}) -∗
  WP (sb(L := val v; b), k) @ s; E {{ φ }}
:= by
  iintro HL H
  iapply wp_lift_step (by rfl)
  iintro %σ %_ %_ %_ %sts Hσ
  have Hred : PrimStep.Reducible ((sb(L := val v; b), k), σ) := by
    exists [], (b, k), {σ with heap := Std.insert σ.heap L v}, []
    constructor <;> try trivial
    constructor <;> trivial
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp [Stuckness.MaybeReducible]
    assumption
  inext
  iintro %s' %σ' %sts %Hstep -
  cases σ
  cases σ'
  obtain ⟨Hstep, rfl, rfl, rfl, rfl⟩ := Hstep
  generalize hrv : (RValue.ofVal v) = rv at Hstep
  cases Hstep with
  | Assign _ _ v' =>
    obtain rfl : v' = v := by grind
    simp at *
    subst_eqs
    simp [Iris.StateInterp.stateInterp]
    icases Hσ with ⟨Hfuns, Hheap⟩
    ihave >⟨Henv, HL⟩ := genHeap_update $$ [Hheap HL]; iframe
    ispecialize H $$ HL
    imod Hclose; iclear Hclose; imodintro
    iframe
  | PContext _ PC P0 =>
    cases PC with
    | RContext RC' PC' =>
      have HtoVal : ToVal.toVal (PC'.fillItem P0) = none := by
        apply RValue.PlaceEctxtItem.fillItem_not_val
        apply Language.val_stuck
        assumption
      have : rv = PC'.fillItem P0 := by grind
      subst hrv
      rw [<-this] at HtoVal
      simp [ProgramLogic.toVal, RValue.toVal_coe] at *
    | Call => simp at *
    | Assign =>
      rename_i H
      obtain ⟨rfl, rfl, rfl⟩ := H
      exfalso
      apply Language.val_irreducible (e := Place.Loc L)
      simp [ProgramLogic.toVal]
      assumption
    | _ => simp at *

  | RContext _ RC rv rv' Hred =>
    cases RC <;> simp! at *
    rename_i H
    obtain ⟨rfl, rfl, rfl⟩ := H
    exfalso
    apply Language.val_irreducible (e := rv)
    subst hrv
    simp [ProgramLogic.toVal, RValue.toVal_coe]
    assumption

-- I require the precondition to disallow stuckness
-- this is maybe not mandatory, I'm not sure
-- htis is required for a sort of technical reason that may disappear when skip is removed
-- theorem wp_seq (b1 b2 : Block) (k : Kontinuation)
--   (Hb1NoCall : ∀ s, s ∈ b1 -> s.NoCall)
--   (Hb1NoReturn : ∀ s, s ∈ b1 -> s.NoReturn) :
--   WP (b1, k) @ E {{__, ▷?(b1 ≠ []) WP ((b2, k) : Configuration) @ s; E {{ φ }} }} ⊢
--   WP (b1 ++ b2, k) @ s; E {{ φ }}
-- := by
--   iintro Hwp
--   iloeb as IH generalizing %b1 %Hb1NoReturn %Hb1NoCall
--   cases hs1: ProgramLogic.toVal (b1 ++ b2, k) with
--   | some u =>
--     obtain rfl : b1 = [] := by cases b1 <;> simp at *
--     obtain rfl : b2 = [] := by cases b2 <;> simp at *
--     simp at *
--     rw [wp_unfold.to_eq, wp_unfold.to_eq]
--     simp [wp.pre, hs1, BI.BIBase.laterIf, BI.BIBase.laterN, Nat.repeat]
--     imod Hwp
--     iassumption
--   | none =>
--     clear hs1
--     rw (occs := [2]) [wp_unfold.to_eq]
--     iapply wp_unfold
--     simp [wp.pre, toVal] at *
--     iintro %σ %ns %obs %obs' %nt Hσ
--     ihave >⟨%Hred, Hwp⟩ := Hwp $$ %σ %ns %obs %obs' %nt Hσ
--     imodintro
--     isplitr
--     · ipureintro
--       cases s
--       case MaybeStuck => simp [Stuckness.MaybeReducible]
--       case NotStuck =>
--         simp [Stuckness.MaybeReducible] at *
--         apply reducible_fill [s1] b2
--         assumption
--     iintro %⟨s', k'⟩ %σ' %sts %Hstep creds

--     obtain ⟨s', rfl, rfl, Hstep'⟩ := primStep_fill_inv b2 k Hs1NoCall Hs1NoReturn Hstep
--     simp [Nat.repeat, IrisGS_gen.numLatersPerStep]
--     imod Hwp $$ %_ %_ %_ %Hstep' creds
--     imodintro; inext
--     imod Hwp; imodintro
--     imod Hwp; imodintro
--     ihave ⟨_, Hwp, Hforked⟩ := Hwp
--     iframe
--     isplitl [Hwp]
--     · iapply IH
--       · ipureintro; assumption
--       · ipureintro; assumption
--       · iassumption
--     · iapply BI.BigSepL.bigSepL_mono $$ Hforked
--       intro _ _ _
--       iapply wp_stuck_mono
--       simp


theorem wp_IfThenElseTrue (b1 b2 : Block) (k : Kontinuation) :
  ▷ WP (b1 ++ b, k) @ s; E {{ φ }} ⊢ WP (sb((if true then b1 else b2); b), k) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //

theorem wp_IfThenElseFalse (b1 b2 : Block) (k : Kontinuation) :
  ▷ WP (b2 ++ b, k) @ s; E {{ φ }} ⊢ WP (sb((if false then b1 else b2); b), k) @ s; E {{ φ }}
:= by
  iintro _
  iapply wp_pure_step_later (by trivial)
  iintro !> - //



theorem List.freshN [InfiniteType A] (X : List A) (n : Nat) :
  ∃ (L : List A), L.length = n ∧ L.Nodup ∧ ∀ a, a ∈ L -> a ∉ X
:= by
  induction n
  case zero => simp
  case succ n IHn =>
    rcases IHn with ⟨L, rfl, HL⟩
    have ⟨a, Ha⟩ := List.fresh (X ++ L)
    exists a :: L
    grind

theorem List.splitAt_nodup_disjoint (L L1 L2 : List A) (Hnodup : L.Nodup) :
  (L1, L2) = L.splitAt n -> L1.Disjoint L2
:= by
  induction n generalizing L L1 L2
  case zero => simp; intro rfl rfl; simp
  case succ n IH =>
    simp
    intro rfl rfl
    apply List.disjoint_take_drop Hnodup (by simp)

theorem List.splitAt_nodup (L L1 L2 : List A) (Hnodup : L.Nodup) :
  (L1, L2) = L.splitAt n -> L1.Nodup ∧ L2.Nodup
:= by grind

theorem List.splitAt_length_fst (L : List A) (n : Nat) :
  n <= L.length -> (L.splitAt n).fst.length = n
:= by grind

theorem List.splitAt_length_snd (L : List A) (n : Nat) :
  n <= L.length -> (L.splitAt n).snd.length = L.length - n
:= by grind


theorem wp_call (L : Location) (argsv : List Value) (fd : FunDef) (k : Kontinuation)
  (Hlen : argsv.length = fd.args.length) :
  ▷ f ⋗ fd -∗
  ▷ (
    f ⋗ fd -∗
    ∀ (Largs Llocals : List Location),
    ⌜Largs.Nodup⌝ -∗
    ⌜Llocals.Nodup⌝ -∗
    ⌜Largs.Disjoint Llocals⌝ -∗
    ⌜Largs.length = fd.args.length⌝ -∗
    ⌜Llocals.length = fd.locals.length⌝ -∗
    ([∗list] L; v ∈ Largs; argsv, L ↦ v) -∗
    ([∗list] L ∈ Llocals, L ↦ Value.Poison) -∗
    WP (fd.substVars Largs Llocals, k.push {ret := L, next}) @ s; E {{ φ }}) -∗
  WP (Call ↑L f (argsv.map ToVal.ofVal) :: next, k) @ s; E {{ φ }}
:= by
  iintro >Hf Hwp
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro (by simp)
  iintro Hclose

  ihave %Hfd : ⌜σ.funDefs[f]? = some fd⌝ $$ [Hf Hσ]
  · iapply bupd_elim
    iapply genFuns_valid
    simp [Iris.stateInterp]
    icases Hσ with ⟨_, _⟩
    iframe

  have Hred : PrimStep.Reducible ((Call ↑L f (argsv.map ToVal.ofVal) :: next, k), σ) := by
    obtain ⟨Largs, Llocals, _, _, _, _, _, _, _⟩ :
      ∃ (Largs Llocals : List Location),
      Largs.Nodup ∧ Llocals.Nodup ∧ Largs.Disjoint Llocals ∧
      Largs.length = fd.args.length ∧
      Llocals.length = fd.locals.length ∧
      (∀ L, L ∈ Largs -> get? σ.heap L = none) ∧
      (∀ L, L ∈ Llocals -> get? σ.heap L = none)
    := by
      obtain ⟨Ls, Hlen, HLsnodup, Hmem⟩ := List.freshN (σ.heap.keys) (Nat.add fd.args.length fd.locals.length)
      have (eq := H) ⟨Largs, Llocals⟩ := Ls.splitAt fd.args.length
      exists Largs, Llocals
      obtain ⟨_, _⟩ : Largs.Nodup ∧ Llocals.Nodup := by
        apply List.splitAt_nodup
        assumption
        symm; assumption
      constructor; assumption
      constructor; assumption
      constructor; apply List.splitAt_nodup_disjoint (Hnodup := HLsnodup); rw [H]
      constructor; have := List.splitAt_length_fst Ls (fd.args.length) (by grind); grind
      constructor; have := List.splitAt_length_snd Ls (fd.locals.length) (by grind); grind
      constructor
      · intro L _
        simp [get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
        grind
      · intro L _
        simp [get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
        grind
    constructor
    exists
      (fd.substVars Largs Llocals, k.push {ret := L, next}),
      ⟨(PartialMap.ofList (Largs.zip argsv ++ Llocals.map (·, Value.Poison)) : Memory) ++ σ.toState, σ.funDefs⟩,
      []
    constructor <;> try trivial
    simp
    constructor <;> try trivial

  isplitr
  ipureintro
  cases s <;> simp [Stuckness.MaybeReducible]
  assumption

  iintro %s' %σ' %sts %Hstep
  inext
  iintro -

  obtain ⟨Hstep, rfl, rfl, HfunDefs⟩ := Hstep
  generalize Hσ's : σ'.toState = σ's at *
  cases Hstep with
  | PContext _ PC P _ _ Heq =>
    cases PC with
    | RContext RCi PC' =>
      cases RCi with
      | Call =>
        simp at *
        rcases Heq with ⟨rfl, rfl, Hargs⟩
        exfalso
        apply args_val_unsplittable (Expr := RValue)
        apply RValue.PlaceEctxtItem.toVal_eq_none_fill PC'
        apply Language.val_stuck
        assumption
        assumption
      | _ => simp at *
    | Call =>
      simp at *
      rcases Heq with ⟨rfl, rfl, rfl⟩
      have : ToVal.toVal (ToVal.ofVal L : Place) = none := by
        apply Language.val_stuck
        assumption
      simp [toVal_coe] at this
    | _ => simp at *
  | RContext _ RC rv _ _ Heq =>
    cases RC with
    | Call =>
      simp at Heq
      rcases Heq with ⟨rfl, rfl,  _⟩
      exfalso
      apply args_val_unsplittable (Expr := RValue)
      apply Language.val_stuck
      assumption
      assumption
    | _ => simp at *
  | Call _ L' fd' argsv' Largs Llocals HL Hargs _ Hlen1 Hlen2 Hlen3 Hfresh1 Hfresh2 Hnodup1 Hnodup2 Hdisjoint Hσ' Hk' Hs' =>
    simp at HL; subst HL
    subst Hσ'
    subst Hk'
    subst Hs'
    obtain rfl : fd = fd' := by grind
    obtain rfl : argsv = argsv' := by
      rw [<-List.map_inj_right]
      assumption
      apply ToVal.TovVal.ofVal_inj
    clear Hargs
    simp [StateInterp.stateInterp]
    icases Hσ with ⟨HfunDefs, Hheap⟩
    obtain HeqfunDefs : σ'.funDefs = σ.funDefs := by grind
    rw [HeqfunDefs]; clear HeqfunDefs
    ihave >⟨Hheap, HargsHeap, HlocalsHeap⟩ : |==> (genHeapInterp σ'.heap ∗ ([∗list] L; v ∈ Largs; argsv, L ↦ v) ∗ [∗list] L ∈ Llocals, L ↦ Value.Poison) $$ [Hheap]
    · ihave >⟨Hσ'heap, Hheap, -⟩ := genHeap_alloc_big (PartialMap.ofList (Largs.zip argsv ++ List.map (·, Value.Poison) Llocals)) $$ Hheap
      · intro L H
        simp [Option.isSome_iff_exists] at H
        rcases H with ⟨⟨_, H1⟩, ⟨_, H2⟩⟩
        have H1 := LawfulFiniteMap.mem_of_mem_ofList H1
        simp [List.mem_append] at H1
        rcases H1 with H1 | ⟨L, HLlocals, rfl, _⟩
        · rw [List.mem_iff_getElem?] at H1
          specialize Hfresh1 L (by grind)
          rw [Hfresh1] at *
          trivial
        · specialize Hfresh2 L (by grind)
          rw [Hfresh2] at *
          trivial
      obtain Hσ'heap : σ'.heap = PartialMap.union (PartialMap.ofList (Largs.zip argsv ++ List.map (fun x => (x, Value.Poison)) Llocals)) σ.heap := by
        rcases σ' with ⟨⟩
        subst Hσ's
        rfl
      rw [Hσ'heap]; clear Hσ'heap
      imodintro
      rw [(BI.BigSepM.bigSepM_ofList ?_).to_eq, BI.BigSepL2.bigSepL2_alt.to_eq, BI.BigSepL.bigSepL_append.to_eq, BI.BigSepL.bigSepL_map]
      icases Hheap with ⟨_, _⟩
      iframe
      ipureintro; grind
      unfold NoDupKeys
      simp [List.map_append, List.nodup_append]
      constructor <;> try constructor
      · rw [List.map_fst_zip ?_]
        assumption
        grind
      · rw [List.map_congr_left (g := id) (by grind)]
        simp
        assumption
      · intro _ _ H _ Hlocals rfl
        obtain ⟨Hargs, _⟩ := List.of_mem_zip H
        apply Hdisjoint Hargs Hlocals
    imod Hclose; iclear Hclose; imodintro
    ispecialize Hwp $$ Hf %Largs %Llocals %(by trivial) %(by trivial) %(by trivial) %(by trivial) %(by trivial) HargsHeap HlocalsHeap
    iframe


theorem wp_return (v : Value) (k' k : Kontinuation) (Hk : some ({ret, next}, k') = k.pop?) :
  ▷ WP (sb(ret := v; next), k') @ s; E {{ φ }} ⊢ WP (sb(return v; b), k) @ s; E {{ φ }}
:= by
  iintro Hwp
  rcases k with ⟨next, (_ | ⟨⟨_, next'⟩, stack⟩)⟩ <;>
  simp [Kontinuation.pop?] at *
  rcases Hk with ⟨rfl, rfl⟩
  iapply wp_pure_step_later
  trivial
  iintro !> - //


theorem wp_place {k : Kontinuation} (PCi : PlaceEctxtItem) (PC : Place.Ectx) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (PCi.fillItem (fill PC ↑L) :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (PCi.fillItem (fill PC P) :: b, k) @ s; E {{ φ }}
:= by
  iloeb as IH generalizing %P
  rw [wp_unfold.to_eq]
  unfold wp.pre
  cases HeqP : (ProgramLogic.toVal P)
  case some L =>
    cases P <;> simp [ProgramLogic.toVal] at HeqP <;> subst HeqP
    simp
    iapply fupd_wp
  case none =>
    have H : ProgramLogic.toVal (PCi.fillItem (fill PC P) :: b, k) = none := by rfl
    rw (occs := [1]) [wp_unfold.to_eq, wp.pre, H]
    simp
    iintro Hwp %σ %ns %obs %obs' %nt Hσ
    simp [StateInterp.stateInterp]
    icases Hσ with ⟨Hfuns, Hσ⟩
    imod Hwp $$ %σ.toState %ns %obs %obs' %nt Hσ with ⟨%HstepP, Hwp⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at *
      rcases HstepP with ⟨obs, P', σ', Ps, HstepP⟩
      have ⟨_, _, _⟩: σ.toState = σ' ∧ obs = [] ∧ Ps = [] := by
        rcases HstepP with ⟨⟨_, _, _, _⟩⟩
        subst_eqs
        simp
      subst_eqs
      exists [], (PCi.fillItem (fill PC P') :: b, k), σ, []
      constructor <;> try trivial
      apply baseStep.PContext b PCi (fill PC P) <;> try trivial
      apply Language.Context.primStep_fill
      assumption
    iintro %⟨s', k'⟩ %σ' %sts %Hstep creds
    have ⟨rfl, rfl⟩ : [] = obs ∧ [] = sts := by
      generalize PCi.fillItem _ = s at *
      rcases Hstep with ⟨_⟩
      grind
    have HtoVal : ToVal.toVal (fill PC P) = none := by
      apply EctxLanguage.fill_not_val
      assumption

    obtain ⟨P', rfl, rfl, rfl, Hstep'⟩ := PlaceEctxtItem.primStep_fill_inv (P := fill PC P) (k := k) (σ := σ) PCi HtoVal Hstep
    obtain ⟨P', rfl, Hstep''⟩ := Language.Context.primStep_fill_inv HeqP Hstep'


    ispecialize Hwp $$ %P' %σ.toState %([]) %Hstep'' creds

    simp [Nat.repeat, IrisGS_gen.numLatersPerStep]
    imod Hwp; imodintro; inext; imod Hwp; imodintro
    imod Hwp with ⟨_, Hwp, -⟩
    iframe
    ispecialize IH $$ %P' [Hwp //]
    iframe
    imodintro
    iempintro

theorem wp_place' {k : Kontinuation} (PCi : PlaceEctxtItem) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (PCi.fillItem ↑L :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (PCi.fillItem P :: b, k) @ s; E {{ φ }}
:= by
  have' Hwp := wp_place (GF := GF) PCi empty
  simp [EvContext.fill_empty] at Hwp
  apply Hwp

theorem wp_rvalue {k : Kontinuation} (RCi : RValueEctxtItem) (RC : RValue.Ectx) (rv : RValue) :
  WP rv @ s;E {{ fun (v : Value) => WP (RCi.fillItem (fill RC ↑v) :: b, k) @ s; E {{ φ }} }} ⊢
  WP (RCi.fillItem (fill RC rv) :: b, k) @ s; E {{ φ }}
:= by
  iloeb as IH generalizing %rv
  rw [wp_unfold.to_eq]
  unfold wp.pre
  cases Hrv : (ProgramLogic.toVal rv)
  case some v =>
    obtain rfl := coe_of_toVal_eq_some Hrv
    iapply fupd_wp
  case none =>
    rw (occs := [1]) [wp_unfold.to_eq, wp.pre]
    obtain HtoVal : ToVal.toVal (RCi.fillItem (fill RC rv) :: b, k) = none := by rfl
    simp only [HtoVal]
    iintro Hwp %σ %ns %obs %obs' %nt Hσ
    simp only [StateInterp.stateInterp]
    icases Hσ with ⟨Hfuns, Hσ⟩
    imod Hwp $$ %σ.toState %ns %obs %obs' %nt Hσ with ⟨%HstepP, Hwp⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at *
      rcases HstepP with ⟨obs, rv', σ', rvs, HstepP⟩
      have ⟨_, _⟩ : obs = [] ∧ rvs = [] := by
        rcases HstepP with ⟨⟨_, _, _, _⟩⟩
        subst_eqs
        simp
      subst_eqs
      exists [], (RCi.fillItem (fill RC rv') :: b, k), ⟨σ', σ.funDefs⟩, []
      constructor <;> try trivial
      apply baseStep.RContext b RCi (fill RC rv) <;> try trivial
      apply Language.Context.primStep_fill
      assumption
    iintro %⟨s', k'⟩ %σ' %sts %Hstep creds
    have ⟨HfunDefs, rfl, rfl⟩ : σ.funDefs = σ'.funDefs ∧ [] = obs ∧ [] = sts := by
      generalize RCi.fillItem _ = s at *
      rcases Hstep with ⟨_⟩
      grind
    rw [HfunDefs]
    have HtoVal : ToVal.toVal (fill RC rv) = none := by
      apply EctxLanguage.fill_not_val
      assumption
    obtain ⟨_, rfl, rfl, Hstep'⟩ := RValueEctxtItem.primStep_fill_inv (rv := fill RC rv) RCi HtoVal Hstep
    obtain ⟨rv', rfl, Hstep''⟩ := Language.Context.primStep_fill_inv Hrv Hstep'

    ispecialize Hwp $$ %rv' %σ'.toState %([]) %Hstep'' creds

    simp only [Nat.repeat, IrisGS_gen.numLatersPerStep]
    imod Hwp; imodintro; inext; imod Hwp; imodintro
    imod Hwp with ⟨_, Hwp, -⟩
    ispecialize IH $$ %rv' [Hwp //]
    imodintro
    iframe
    iempintro

theorem wp_rvalue' {k : Kontinuation} (RCi : RValueEctxtItem) (rv : RValue) :
  WP rv @ s;E {{ fun (v : Value) => WP (RCi.fillItem ↑v :: b, k) @ s; E {{ φ }} }} ⊢
  WP (RCi.fillItem rv :: b, k) @ s; E {{ φ }}
:= by
  have' Hwp := wp_rvalue (GF := GF) RCi empty
  simp [EvContext.fill_empty] at Hwp
  apply Hwp

theorem wp_rvalue_place {k : Kontinuation} (RCi : RValueEctxtItem) (RC : RValue.Ectx)
  (PCi : RValue.PlaceEctxtItem) (PC : Place.Ectx) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (RCi.fillItem (fill RC (PCi.fillItem (fill PC ↑L))) :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (RCi.fillItem (fill RC (PCi.fillItem (fill PC P))) :: b, k) @ s; E {{ φ }}
:= by
  iloeb as IH generalizing %P
  rw [wp_unfold.to_eq]
  unfold wp.pre
  cases HeqP : (ProgramLogic.toVal P)
  case some L =>
    cases P <;> simp [ProgramLogic.toVal] at HeqP <;> subst HeqP
    simp
    iapply fupd_wp
  case none =>
    have H : ProgramLogic.toVal (RCi.fillItem (fill RC (PCi.fillItem (fill PC P))) :: b, k) = none := by rfl
    rw (occs := [1]) [wp_unfold.to_eq, wp.pre, H]
    iintro Hwp %σ %ns %obs %obs' %nt Hσ
    simp only [StateInterp.stateInterp]
    icases Hσ with ⟨Hfuns, Hσ⟩
    imod Hwp $$ %σ.toState %ns %obs %obs' %nt Hσ with ⟨%HstepP, Hwp⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at *
      rcases HstepP with ⟨obs, P', σ', Ps, HstepP⟩
      have ⟨_, _, _⟩: σ.toState = σ' ∧ obs = [] ∧ Ps = [] := by
        rcases HstepP with ⟨⟨_, _, _, _⟩⟩
        subst_eqs
        simp
      subst_eqs
      exists [], (RCi.fillItem (fill RC (PCi.fillItem (fill PC P'))) :: b, k), σ, []
      constructor <;> try trivial
      apply baseStep.RContext b RCi (fill RC (PCi.fillItem (fill PC P))) <;> try trivial
      apply Language.Context.primStep_fill
      apply EctxLanguage.primStep_of_baseStep
      constructor <;> try trivial
      apply RValue.baseStep.PContext PCi (fill PC P) <;> try trivial
      apply Language.Context.primStep_fill
      assumption
    iintro %⟨s', k'⟩ %σ' %sts %Hstep creds
    have ⟨rfl, rfl⟩ : [] = obs ∧ [] = sts := by
      generalize RCi.fillItem _ = s at *
      rcases Hstep with ⟨_⟩
      grind
    have HtoVal'' : ToVal.toVal (fill PC P) = none := by
      apply EctxLanguage.fill_not_val
      assumption
    have HtoVal' : ToVal.toVal (PCi.fillItem (fill PC P)) = none := by
      apply RValue.PlaceEctxtItem.fillItem_not_val
      assumption
    have HtoVal : ToVal.toVal (fill RC (PCi.fillItem (fill PC P))) = none := by
      apply EctxLanguage.fill_not_val
      assumption

    obtain ⟨_, rfl, rfl, Hstep'⟩ := RValueEctxtItem.primStep_fill_inv (rv := (fill RC (PCi.fillItem (fill PC P)))) RCi HtoVal Hstep
    obtain ⟨_, rfl, Hstep''⟩ := Language.Context.primStep_fill_inv HtoVal' Hstep'
    obtain ⟨_, rfl, Hstep'''⟩ := RValue.PlaceEctxtItem.primStep_fill_inv (P := (fill PC P)) PCi HtoVal'' Hstep''
    obtain ⟨P', rfl, Hstep''''⟩ := Language.Context.primStep_fill_inv HeqP Hstep'''

    have H : σ.toState = σ'.toState := by
      generalize σ.toState = σs at *
      generalize hrv : PCi.fillItem (fill PC P) = rv at *
      generalize hrv' : PCi.fillItem (fill PC P') = rv' at *
      have Hred : BaseStep.Reducible (rv, σs) := by
        have _ := RValue.PlaceEctxtItem.primStep_fill PCi Hstep'''
        exists [], rv', σs, []
        constructor <;> try trivial
        apply RValue.baseStep.PContext PCi (fill PC P) (fill PC P') <;> grind
      obtain ⟨Hstepagain, _, _, _⟩ := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Hstep''
      cases Hstepagain with
      | Alloc =>
        cases PCi
        simp at *
        cases hrv
      | _ => simp

    obtain rfl : σ = σ' := by
      cases Hstep
      grind [cases StateFn]

    ispecialize Hwp $$ %P' %σ.toState %([]) %Hstep'''' creds

    simp only [Nat.repeat, IrisGS_gen.numLatersPerStep]
    imod Hwp; imodintro; inext; imod Hwp; imodintro
    imod Hwp with ⟨_, Hwp, -⟩
    iframe
    ispecialize IH $$ %P' [Hwp //]
    iframe
    imodintro
    iempintro

theorem wp_rvalue_place' {k : Kontinuation} (RCi : RValueEctxtItem) (RC : RValue.Ectx)
  (PCi : RValue.PlaceEctxtItem) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (RCi.fillItem (fill RC (PCi.fillItem ↑L)) :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (RCi.fillItem (fill RC (PCi.fillItem P)) :: b, k) @ s; E {{ φ }}
:= by
  have' Hwp := wp_rvalue_place (GF := GF) RCi RC PCi empty
  simp [EvContext.fill_empty] at Hwp
  apply Hwp

theorem wp_rvalue'_place {k : Kontinuation} (RCi : RValueEctxtItem)
  (PCi : RValue.PlaceEctxtItem) (PC : Place.Ectx) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (RCi.fillItem (PCi.fillItem (fill PC ↑L)) :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (RCi.fillItem (PCi.fillItem (fill PC P)) :: b, k) @ s; E {{ φ }}
:= by
  have' Hwp := wp_rvalue_place (GF := GF) RCi empty PCi PC
  simp [EvContext.fill_empty] at Hwp
  apply Hwp

theorem wp_rvalue'_place' {k : Kontinuation} (RCi : RValueEctxtItem)
  (PCi : RValue.PlaceEctxtItem) (P : Place) :
  WP P @ s; E {{ fun (L : Location) => (WP (RCi.fillItem (PCi.fillItem ↑L) :: b, k) @ s; E {{ φ }} ) }} ⊢
  WP (RCi.fillItem (PCi.fillItem P) :: b, k) @ s; E {{ φ }}
:= by
  have' Hwp := wp_rvalue_place (GF := GF) RCi empty PCi []
  simp [EvContext.fill_empty] at Hwp
  apply Hwp



















theorem adequacy [FullGS .hasLC GF] (c : Configuration) σ (φ : Unit → Prop)
  (Hwp : ∀ [FullGS .hasLC GF], ⊢@{IProp GF} (WP c {{ __, ⌜φ v⌝ }})) :
  adequate .NotStuck c σ (fun v _ => φ v)
:= by
  apply wp_adequacy (GF := GF)
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (.own 1)
      (Std.PartialMap.map (toAgree ⟨·⟩) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (.own 1)
      (Std.PartialMap.map (toAgree ⟨·⟩) σ.funDefs))
    HeapView.auth_one_valid with ⟨%γf, Hf⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (.own 1)
      (Std.PartialMap.map (toAgree ⟨·⟩) (∅ : _Memory GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI instFullLangGS : FullGS .hasLC GF := {toCommonGS := ⟨γh, γm⟩, funDefs := ⟨γf⟩}
  imodintro
  iexists (fun σ _ => iprop%  genFunsInterp σ.funDefs ∗ Iris.genHeapInterp σ.heap)
  iexists (fun _ => iprop(True))
  simp only
  ihave #Hwp := (@Hwp _)
  iframe Hwp
  isplitl [Hf]
  · simp only [genFunsInterp]
    iexists ∅
    unfold ghost_map_auth
    iframe Hf
    ipureintro
    intro k hk
    simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
  · simp only [Iris.genHeapInterp]
    iexists ∅
    unfold ghost_map_auth
    iframe Hh Hm
    ipureintro
    intro k hk
    simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk



end Statement
