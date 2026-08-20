import Iris
import Lib.ConstrainedPredBox
import Iris.BI.Lib.GenHeap
-- the idea here is to just give up on having a dynamic amount of loans
-- we just assume that this is really statically defined
-- to make it work, we do LoanIdent = GName (i.e. γ = l)

open Iris Std OFE BI

variable {Location Value} [Coe Location Value]
variable [LawfulFiniteMap H Location] [Iris.genHeapGS Location Value GF H]


class ConstrainedFiniteLoans (hlc : outParam HasLC) (N : outParam Namespace) (GF : outParam BundledGFunctors) (Location : outParam <| Type _)
  (C : outParam <| Location -> (Location -> IProp GF) -> IProp GF)
  [OFE Location] [Discrete Location]
extends InvGS_gen hlc GF where
  constrainedPredBox : ConstrainedPredBox GF Location C

attribute [reducible, instance] ConstrainedFiniteLoans.constrainedPredBox

-- namespace for our invariant
-- I used Pos, but we could have used something else with the proper instances
def N := nroot .@ (1 : Pos)

variable [OFE Location] [Discrete Location]
variable {C : Location -> (Location -> IProp GF) -> IProp GF} [ConstrainedFiniteLoans hlc N GF Location C]


abbrev LoanIdent := GName



def ML (l : LoanIdent) (L : Location) : IProp GF :=
  iOwn (E := ConstrainedPredBox.elem) l (RA.ender_token L)

instance : Timeless (ML l L) := by
  unfold ML
  infer_instance


def MB.weak.pre (l : LoanIdent) (P : Location -> IProp GF) (L' : Location) : IProp GF :=
  iOwn (E := ConstrainedPredBox.elem) l (RA.getter_token P L')

instance:  Timeless (MB.weak.pre l P L') := by
  unfold MB.weak.pre
  infer_instance

def MB.weak (l : LoanIdent) (P : Location -> IProp GF) : IProp GF :=
  ∃ (L' : Location), MB.weak.pre l P L'

instance : Timeless (MB.weak l P) := by
  unfold MB.weak
  infer_instance

-- [|MB l τ|](L)  with P := [|τ|]
def MB (l : LoanIdent) (P : Location -> IProp GF) (L : Location) : IProp GF :=
  iprop(∃ (L' : Location), L ↦ L' ∗ MB.weak.pre l P L')

instance : Timeless (MB l P L) := by
  unfold MB
  infer_instance

theorem MB.toWeak : MB l P L -∗ MB.weak l P := by
  unfold MB MB.weak
  iintro ⟨%L, _, _⟩
  iexists _
  iassumption




theorem brw_alloc (L L' : Location) (P : Location -> IProp GF) :
  P L ∗ C L P ∗ L' ↦ L ={N}=∗ ∃ (l : LoanIdent), MB l P L' ∗ ML l L ∗ inv N (I l)
:= by
  iintro ⟨HP, HC, HL'⟩
  ihave >⟨%l, ⟨Hget, Hend, HI⟩⟩ := alloc $$ [HP HC]; iframe
  ihave >_: |={_}=> inv N (I l) $$ [HI]
  · iapply inv_alloc
    iassumption
  imodintro
  iexists l
  unfold MB MB.weak.pre ML
  iframe

theorem weak.brw_alloc (L : Location) (P : Location -> IProp GF) :
  P L ∗ C L P ={N}=∗ ∃ (l : LoanIdent), MB.weak l P ∗ ML l L ∗ inv N (I l)
:= by
  iintro ⟨HP, HC⟩
  ihave >⟨%l, ⟨Hget, Hend, HI⟩⟩ := alloc $$ [HP HC]; iframe
  ihave >HI := inv_alloc $$ [HI]; iassumption
  imodintro
  iexists l
  unfold MB.weak MB.weak.pre ML
  iframe

theorem brw_end (P : Location -> IProp GF) [Discrete Location] [TimelessConstraint C]:
  inv N (I l) ⊢
    MB l P L ∗ ML l L' ={N}=∗ (P L' ∗ C L' P ∗ L ↦ L')
:= by
  unfold MB MB.weak.pre ML
  iintro #HI ⟨⟨%L'', ⟨HL, Hget⟩⟩, Hend⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  ihave ⟨_, %Heq, HC, HIl⟩ := ender $$ [HIl Hget Hend]; iframe
  subst Heq
  imod Hclose $$ HIl; iclear Hclose
  imodintro
  iframe

theorem weak.brw_end (P : Location -> IProp GF) [Discrete Location] [TimelessConstraint C]:
  inv N (I l) ⊢
    MB.weak l P ∗ ML l L ={N}=∗ P L ∗ C L P
:= by
  unfold MB.weak MB.weak.pre ML
  iintro #HI ⟨⟨%L', Hget⟩, Hend⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  ihave ⟨_, %Heq, HC, HIl⟩ := ender $$ [HIl Hget Hend]; iframe
  subst Heq
  imod Hclose $$ HIl; iclear Hclose
  imodintro
  iframe

theorem brw_open_strong (P : Location -> IProp GF) [TimelessConstraint C] :
  inv N (I l) ⊢
    MB l P L ={N, ∅}=∗ ∃ (L0 : Location),
      P L0 ∗ L ↦ L0 ∗ C L0 P ∗
      (C L0 P ={∅, N}=∗ ∀ Q L', Q L0 ∗ (∀ P, C L0 P -∗ C L0 Q) ∗ L' ↦ L0 ={N}=∗ MB l Q L')
:= by
  unfold MB MB.weak.pre
  iintro #HI ⟨%L0, ⟨HL, Hget⟩⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  imodintro
  ihave ⟨HP, HC, Hacc, HI⟩:= getter_strong $$ [Hget HIl]; iframe
  iexists L0
  iframe
  iintro HC
  ispecialize HI $$ [HC]; iassumption
  imod Hclose $$ [HI]; iassumption; iclear Hclose
  imodintro
  iintro %Q %L' ⟨HQ, HCwand, HL⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  ihave >⟨Hget, HIl⟩ := Hacc $$ %Q [HQ HI HIl HCwand]; iframe
  imod Hclose $$ [HIl]; iassumption; iclear Hclose
  imodintro
  iexists L0
  iframe

theorem weak.brw_open_strong (P : Location -> IProp GF) [TimelessConstraint C] :
  inv N (I l) ⊢
    MB.weak l P ={N, ∅}=∗ ∃ L0,
      P L0 ∗ C L0 P ∗
      (C L0 P ={∅, N}=∗ ∀ Q, Q L0 ∗ (∀ P, C L0 P -∗ C L0 Q) ={N}=∗ MB.weak l Q)
:= by
  unfold MB.weak MB.weak.pre
  iintro #HI ⟨%L0, Hget⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  imodintro
  ihave ⟨HP, HC, Hacc, HI⟩:= getter_strong $$ [Hget HIl]; iframe
  iexists L0
  iframe
  iintro HC
  ispecialize HI $$ [HC]; iassumption
  imod Hclose $$ [HI]; iassumption; iclear Hclose
  imodintro
  iintro %Q ⟨HQ, HCwand⟩
  ihave >⟨HIl, Hclose⟩: |={_}=> I l ∗ (I l ={_}=∗ True) $$ [HI]
  · iapply inv_acc_timeless; trivial; iassumption
  simp
  ihave >⟨Hget, HIl⟩ := Hacc $$ %Q [HQ HI HIl HCwand]; iframe
  imod Hclose $$ [HIl]; iassumption; iclear Hclose
  imodintro
  iexists L0
  iframe


theorem brw_open (P : Location -> IProp GF) [TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ⊢
    MB l P L ={N}=∗ ∃ L',
      P L' ∗ L ↦ L' ∗ C L' P ∗
      (∀ Q, Q L' ∗ (∀ P, C L' P -∗ C L' Q) ∗ L ↦ L' ={N}=∗ MB l Q L)
:= by
  iintro HI HMB
  ihave >⟨%L', HL', HL, #HC, Hacc⟩ := brw_open_strong P $$ HI HMB
  imod Hacc $$ HC
  imodintro
  iexists L'
  iframe
  isplitr; iassumption
  iintro %Q
  ispecialize Hacc $$ %Q %L
  iassumption

theorem weak.brw_open (P : Location -> IProp GF) [TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ⊢
    MB.weak l P ={N}=∗ ∃ L',
      P L' ∗ C L' P ∗
      (∀ Q, Q L' ∗ (∀ P, C L' P -∗ C L' Q) ={N}=∗ MB.weak l Q)
:= by
  iintro HI HMB
  ihave >⟨%L', HL', #HC, Hacc⟩ := weak.brw_open_strong P $$ [HI] [HMB]; iassumption; iassumption
  imod Hacc $$ [HC]; iassumption
  iexists L'
  iframe
  iassumption









-- we should technically be able to lift ∃L0
-- before opening the invariant (we only need to open MB)
-- note the hypothesis on the constraint C
-- TODO : the hypothesis on C is looking increasingly fishy
theorem brw_rebrw (P : Location -> IProp GF) (HC : ∀ L l P, C L P ⊢ C L (ML l))
[TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ⊢
    MB l P L ={N}=∗ ∃ L0, L ↦ L0 ∗ (∀ L', L ↦ L0 ∗ L' ↦ L0 ={N}=∗
      ∃ l',
        MB l (ML l') L ∗
        MB l' P L' ∗
        inv N (I l'))
:= by
  iintro #HI HP
  ihave >⟨%L0, HP, HL, HC, Hstore⟩ := brw_open $$ [HI] [HP]; iassumption; iassumption
  imodintro
  iexists L0
  iframe
  iintro %L' ⟨HL, HL'⟩
  ihave >⟨%l', _, HML, _⟩ := brw_alloc $$ [HP HC HL']; iframe
  ispecialize Hstore $$ %(ML l') [HML HL]; iframe; iintro% _ _; iapply HC; iassumption
  iexists l'
  iframe

theorem weak.brw_rebrw (P : Location -> IProp GF) (HC : ∀ L l P, C L P ⊢ C L (ML l))
[TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ⊢
    MB.weak l P ={N}=∗ ∃ l',
      MB.weak l (ML l') ∗
      MB.weak l' P ∗
      inv N (I l')
:= by
  iintro #HI HP
  ihave >⟨%L0, HP, HC, Hstore⟩ := weak.brw_open $$ [HI] [HP]; iassumption; iassumption
  ihave >⟨%l', HMB, HML, HI'⟩ := weak.brw_alloc $$ [HP HC]; iframe
  imod Hstore $$ %(ML l') [HML]; iframe; iintro% _ _; iapply HC; iassumption
  imodintro
  iexists l'
  iframe

-- note the hypothesis on the constraint C
-- TODO : HC looks too restrictive
theorem brw_rebrw_end (P : Location -> IProp GF) (HC : ∀ L Q, C L Q ⊢ C L P)
[TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ∗ inv N (I l') ⊢
    MB l (ML l') L ∗ MB l' P L'
    ={N}=∗
    MB l P L ∗ ∃ L0, L' ↦ L0
:= by
  iintro ⟨#HI, #HI'⟩ ⟨HMBl, HMBl'⟩
  ihave >⟨%L0, HML, HL, HC, Hstore⟩ := brw_open (l := l) $$ [] [HMBl]; iassumption; iassumption
  ihave >⟨HP, HC, HL'⟩ := brw_end (l := l') $$ [] [HMBl' HML]; iassumption; iframe
  imod Hstore $$ %P [HP HL]; iframe; iintro %_ _; iapply HC; iassumption
  imodintro
  iframe

theorem weak.brw_rebrw_end (P : Location -> IProp GF) (HC : ∀ L Q, C L Q ⊢ C L P)
[TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l) ∗ inv N (I l') ⊢
    MB.weak l (ML l') ∗ MB.weak l' P={N}=∗ MB.weak l P
:= by
  iintro ⟨#HI, #HI'⟩ ⟨HMBl, HMBl'⟩
  ihave >⟨%L0, HML, HC, Hstore⟩ := weak.brw_open (l := l) $$ [] [HMBl]; iassumption; iassumption
  ihave >⟨HP, HC⟩ := weak.brw_end (l := l') $$ [] [HMBl' HML]; iassumption; iframe
  imod Hstore $$ %P [HP]; iframe; iintro %_ _; iapply HC; iassumption
  imodintro
  iframe


-- note the hypothesis on the constraint C
-- TODO : check if this is really the constraint we want
theorem brw_chain (L2 L1 L0 : Location) (P : Location -> IProp GF) (HC : ∀ L l, ⊢ C L (MB l P)) :
  L2 ↦ L1 ∗ L1 ↦ L0 ∗ P L0 ∗ C L0 P ⊢
    |={N}=> ∃ l' l,
  MB l' (MB l P) L2 ∗ ML l' L1 ∗ ML l L0 ∗
  inv N (I l') ∗ inv N (I l)
:= by
  iintro ⟨HL2, HL1, HP, HC⟩
  ihave >⟨%l, HMB, HML, #HI⟩ := brw_alloc $$ [HL1 HP HC]; iframe
  ihave >⟨%l', HMB', HML', #HI'⟩ := brw_alloc $$ [HL2 HMB]; iframe; iapply HC
  imodintro
  iexists _, _
  iframe
  isplitl [HI]; iassumption;
  iassumption

-- TODO : check HC
theorem brw_chain_open (L : Location) (P : Location -> IProp GF) (HC : ∀ L l P Q, C L P ⊢ C L (MB l Q))
[TimelessConstraint C] [ConstraintIsPersistent C] :
  inv N (I l') ∗ inv N (I l) ⊢
    MB l' (MB l P) L ={N}=∗ ∃ (Li L': Location),
      P L' ∗ L ↦ Li ∗ Li ↦ L' ∗
      (∀ Q, Q L' ∗ (∀ P, C L' P -∗ C L' Q) ∗ L ↦ Li ∗ Li ↦ L' ={N}=∗  MB l' (MB l Q) L)
:= by
  iintro ⟨#HI', #HI⟩ HL
  ihave >⟨%Li, HLi, HCLi, HL, Hacc'⟩ := brw_open (l := l') $$ [] [HL]; iassumption; iframe
  ihave >⟨%L', HP, HCL', HLi, Hacc⟩ := brw_open (l := l) $$ [] [HLi]; iassumption; iframe
  imodintro
  iexists Li, L'
  iframe
  iintro %Q ⟨HQ, HCwand, HL, HLi⟩
  imod Hacc $$ %Q [HQ HLi HCwand]; iframe
  imod Hacc' $$ %(MB l Q) [Hacc HL]; iframe; iintro %_ _; iapply HC; iassumption
  imodintro
  iassumption

-- regarding the ad hoc constraints imposed on C for borrwos manipulation
-- they seem to broadly go into the direction of "C L P only depends on L"
-- of course this is not entirely true, some restrictions on P seem needed too
