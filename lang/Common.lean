import Iris
import Iris.BI.Lib.GenHeap

open Iris Std


abbrev BaseLoc := Nat
abbrev TermVar := String

inductive Path
  | Here
  | Fst (p : Path)
  | Snd (p : Path)
deriving BEq, DecidableEq, Inhabited

structure Location where
  base : BaseLoc
  path : Path
deriving BEq, DecidableEq, Inhabited

def Location.Fst (L : Location) : Location :=
  {base := L.base, path := L.path.Fst}

def Location.Snd (L : Location) : Location :=
  {base := L.base, path := L.path.Snd}



instance : Coe BaseLoc Location where
  coe l := {base := l, path := Path.Here}


instance : OFE Location := OFE.ofDiscrete Location

instance : OFE.Discrete Location where
  discrete_0 := id

instance : InfiniteType Location where
  enum n := {base := InfiniteType.enum n, path := Path.Here}
  enum_inj L0 L1 := by grind [InfiniteType.enum_inj]

def Path.compare (p0 p1 : Path) : Ordering := match p0, p1 with
    | Fst p0, Fst p1 => compare p0 p1
    | Snd p0, Snd p1 => compare p0 p1
    | Here, Here => Ordering.eq
    | Fst _, _ => Ordering.lt
    | _, Fst _ => Ordering.gt
    | Snd _, _ => Ordering.gt
    | _, Snd _ => Ordering.lt

instance : Ord Path where
  compare := Path.compare

instance : TransOrd Path where
  eq_swap := by
    intros p0 p1
    unfold compare instOrdPath
    simp
    induction p0 generalizing p1 <;> induction p1 <;> simp! at * <;> grind
  isLE_trans := by
    intros p0 p1 p2
    unfold compare instOrdPath
    simp
    induction p0 generalizing p1 p2 <;>
    induction p1 generalizing p2 <;>
    induction p2 <;>
    simp! at * <;>
    grind

instance : LawfulEqOrd Path where
  eq_of_compare := by
    intro p0 p1
    induction p0 generalizing p1 <;>
    induction p1 <;>
    simp! [compare] at * <;>
    grind

instance : Ord Location where
  compare L0 L1 := match compare L0.base L1.base with
    | Ordering.eq => compare L0.path L1.path
    | o => o

instance : TransOrd Location where
  eq_swap := by
    intros L0 L1
    have ⟨l0, p0⟩ := L0
    have ⟨l1, p1⟩ := L1
    unfold compare instOrdLocation
    simp
    rw [OrientedCmp.eq_swap (cmp := compare) (α := BaseLoc) (a := l1)]
    rw [OrientedCmp.eq_swap (cmp := compare) (α := Path) (a := p1)]
    cases compare l0 l1 <;> simp
  isLE_trans := by
    intros L0 L1 L2
    have ⟨l0, p0⟩ := L0
    have ⟨l1, p1⟩ := L1
    have ⟨l2, p2⟩ := L2
    unfold compare instOrdLocation
    simp
    cases _:compare l0 l1 <;> cases _:compare l1 l2 <;> cases _:compare l0 l2 <;> simp <;> try grind
    exact TransCmp.isLE_trans

instance : LawfulEqOrd Location where
  eq_of_compare := by
    intros L0 L1
    have ⟨l0, p0⟩ := L0
    have ⟨l1, p1⟩ := L1
    unfold compare instOrdLocation
    simp
    cases _:compare l0 l1 <;> simp
    intro rfl
    simp
    apply LawfulEqOrd.eq_of_compare
    assumption

inductive Value
  | Int (i : Int)
  | Bool (b : Bool)
  | Loc (L : Location)
  | Pair (v1 v2 : Value)
  | Poison
deriving BEq, DecidableEq, Inhabited

instance : Coe Location Value where
  coe := .Loc

instance : Coe BaseLoc Value where
  coe l := ↑↑l

instance : Coe Int Value where
  coe := .Int

instance : Coe Bool Value where
  coe := .Bool

inductive BaseLayout
  | Int
  | Bool
  | Ptr
deriving BEq, DecidableEq, Inhabited

inductive Layout
  | Base (T : BaseLayout)
  | Prod (T1 T2 : Layout)
deriving BEq, DecidableEq, Inhabited


abbrev _Memory := ExtTreeMap Location
abbrev Memory := _Memory Value
abbrev _Environnment := ExtTreeMap TermVar
abbrev Environnment := _Environnment Location


structure State where
  heap : Memory
deriving Inhabited

instance : HAppend Memory State State where
  hAppend mem σ := {heap := PartialMap.union mem σ.heap}
instance : HAppend State Memory State where
  hAppend σ mem := {heap := PartialMap.union σ.heap mem}


section Heap

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H Location]
variable [G : genHeapGS Location Value GF H]

def pointsToMany (L : Location) (dq : DFrac) (v : Value) : IProp GF := match v with
  | Value.Pair v1 v2 => iprop(pointsToMany L.Fst dq v1 ∗ pointsToMany L.Snd dq v2)
  | _ => L ↦{dq} v

notation:50 l:50 " ↦{" dq "}∗ " v:50 => pointsToMany l dq v
notation:50 l:50 " ↦∗ " v:50 => pointsToMany l (DFrac.own 1) v

end Heap


class CommonGS (hlc : outParam HasLC) (GF : BundledGFunctors)
extends InvGS_gen hlc GF where
  heap : genHeapGS Location Value GF _Memory

attribute [reducible, instance] CommonGS.heap

variable [CommonGS hlc GF]

instance stateInterp : StateInterp State Unit GF where
  stateInterp σ _ _ _ := genHeapInterp σ.heap
