import Iris

open Iris Std ProgramLogic Language Notation PrimStep



variable [Λ₁ : Language Expr₁ State Obs Val₁]
variable [Λ₂ : Language Expr₂ State Obs Val₂]

-- TODO : it is unclear if the handling of thread is what we really want
-- I think we would want the type of Expr spawned to be a parameter
-- which would be different from the Expr under scrutiny
-- this typeclass would require both language to agree on the former
-- if we map context on threa spawned, we cannot derive and instance for EctxLanguage because of that
-- if we require no threads to be swpawned, then some lemmas fail
-- maybe another (bad) solution is for the context to hol threads too?
class ContextItem (K : Expr₁ → Expr₂) where
  inj : Function.Injective K
  fill_val e : (toVal (K e)).isSome → (toVal e).isSome
  toVal_eq_none_fill {e : Expr₁} :
    toVal e = none → toVal (K e) = none
  primStep_fill {e : Expr₁} {σ : State} {obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) →
    (K e, σ) -<obs>-> (K e', σ', eₜ.map K)
  -- primStep_fill {e : Expr₁} {σ : State} {obs e' σ'} :
  --   (e, σ) -<obs>-> (e', σ', []) →
  --   (K e, σ) -<obs>-> (K e', σ', [])
  primStep_fill_inv {e : Expr₁} {σ : State} {obs K_e' σ' K_eₜ} :
    toVal e = .none →
    (K e, σ) -<obs>-> (K_e', σ', K_eₜ) →
    ∃ (e' : Expr₁) (eₜ' : List Expr₁), K_e' = K e' ∧ K_eₜ = eₜ'.map K ∧  (e, σ) -<obs>-> (e', σ', eₜ')
  -- primStep_fill_inv {e : Expr₁} {σ : State} {obs K_e' σ'} :
  --   toVal e = .none →
  --   (K e, σ) -<obs>-> (K_e', σ', []) →
  --   ∃ (e' : Expr₁), K_e' = K e' ∧  (e, σ) -<obs>-> (e', σ', [])




namespace ContextItem

variable (K : Expr₁ → Expr₂) [ContextItem K]

@[grind =>]
theorem fill_not_val (e : Expr₁) : (toVal e) = none → (toVal (K e)) = none := by
  grind only [!fill_val, Option.not_isSome_iff_eq_none]

theorem reducible_fill ⦃e : Expr₁⦄ ⦃σ : State⦄ : Reducible (e,σ) → Reducible ((K e), σ) :=
  fun ⟨obs, e', σ', eₜ, h⟩ => ⟨obs, K e', σ', eₜ.map K, primStep_fill h⟩

theorem reducible_fill_inv ⦃e : Expr₁⦄ ⦃σ : State⦄ (toVal_none : toVal e = none) :
    Reducible (K e, σ) → Reducible (e,σ) :=
  fun ⟨obs, _, σ', _, K_red⟩ =>
    have ⟨e', eₜ', _, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨obs, e', σ', eₜ', red⟩

theorem reducibleNoObs_fill ⦃e : Expr₁⦄ ⦃σ : State⦄ :
    ReducibleNoObs (e, σ) → ReducibleNoObs (K e, σ) :=
  fun ⟨e', σ', eₜ, h⟩ => ⟨K e', σ', eₜ.map K, primStep_fill h⟩

theorem reducibleNoObs_fill_inv ⦃e : Expr₁⦄ ⦃σ : State⦄ (toVal_none : toVal e = none) :
    ReducibleNoObs (K e, σ) → ReducibleNoObs (e,σ) :=
  fun ⟨_, σ', _, K_red⟩ =>
    have ⟨e', eₜ', _, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨e', σ', eₜ', red⟩

theorem irreducible_fill ⦃e : Expr₁⦄ ⦃σ : State⦄ (hv : toVal e = none) (irr : Irreducible (e, σ)) :
    Irreducible (K e, σ) :=
  not_reducible_iff_irreducible.1 fun red =>
  not_reducible_iff_irreducible.2 irr <|
  reducible_fill_inv K hv red

theorem irreducible_fill_inv ⦃e : Expr₁⦄ ⦃σ : State⦄ (irr : Irreducible (K e, σ)) :
    Irreducible (e,σ) :=
  not_reducible_iff_irreducible.1 fun red =>
  not_reducible_iff_irreducible.2 irr <|
  reducible_fill K red

theorem notStuck_fill_inv (hyp : NotStuck (K e, σ)) :
    NotStuck (e, σ)  := by
  dsimp only [NotStuck]
  match hyp with
  | .inl hyp =>
    left
    match h : toVal e with
    | none => grind [toVal_eq_none_fill (K := K) h]
    | some v => simp
  | .inr hyp =>
    match h₂ : toVal e with
    | none => exact .inr <| reducible_fill_inv K h₂ hyp
    | some v => grind

theorem stuck_fill : Stuck (e, σ) → Stuck (K e, σ) :=
  fun ⟨toVal_e, irred⟩ => ⟨toVal_eq_none_fill toVal_e, irreducible_fill K toVal_e irred⟩

end ContextItem


-- instance [Λ : EctxLanguage Expr Ectx State Obs Val] (K : Ectx) : ContextItem (fill (Expr := Expr) K) where
--   inj := EvContext.fill_inj
--   fill_val := EctxLanguage.fill_val K
--   toVal_eq_none_fill {e} := by
--     cases h: toVal (fill K e)
--     case none => simp
--     case some v =>
--       have : (toVal e).isSome := by
--         apply EctxLanguage.fill_val
--         rw [h]
--         trivial
--       grind
--   primStep_fill := Context.primStep_fill
--   primStep_fill_inv := Context.primStep_fill_inv
