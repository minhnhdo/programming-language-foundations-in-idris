module Maps

import Logic
import IndProp

%access public export

%default total

data Id : Type where
  MkId : String -> Id

beq_id : (x1, x2 : Id) -> Bool
beq_id (MkId x) (MkId y) = decAsBool $ decEq x y

mkIdInjective : MkId x = MkId y -> x = y
mkIdInjective Refl = Refl

implementation DecEq Id where
  decEq (MkId x) (MkId y) with (decEq x y)
    decEq _ _ | Yes prf = Yes $ cong {f=MkId} prf
    decEq _ _ | No contra = No $ \prf => contra $ mkIdInjective prf

beq_id_refl : (x : Id) -> True = beq_id x x
beq_id_refl (MkId x) with (decEq x x)
  beq_id_refl _ | Yes _ = Refl
  beq_id_refl _ | No contra = absurd $ contra Refl

beq_id_true_iff : (beq_id x y = True) ↔ x = y
beq_id_true_iff = (forward, backward)
where forward : beq_id x y = True -> x = y
      forward {x = (MkId x)} {y = (MkId y)} prf with (decEq x y)
        forward Refl | Yes eq = cong {f=MkId} eq
        forward Refl | No _ impossible
      backward : x = y -> beq_id x y = True
      backward {x = (MkId x)} {y = (MkId y)} prf with (decEq x y)
        backward Refl | Yes _ = Refl
        backward prf | No contra = absurd . contra $ mkIdInjective prf

beq_id_false_iff : (beq_id x y = False) ↔ Not (x = y)
beq_id_false_iff = (forward, backward)
where forward : beq_id x y = False -> Not (x = y)
      forward prf = (snd not_true_iff_false) prf . (snd beq_id_true_iff)
      backward : Not (x = y) -> beq_id x y = False
      backward not_eq = (fst not_true_iff_false) $ not_eq . (fst beq_id_true_iff)

beq_id_x_y_eq_beq_id_y_x : beq_id x y = beq_id y x
beq_id_x_y_eq_beq_id_y_x {x} {y} = case decEq x y of
  Yes prf => rewrite prf in Refl
  No contra => rewrite (snd beq_id_false_iff) contra
               in case decEq y x of
                    Yes prf => void . contra $ sym prf
                    No contra => rewrite (snd beq_id_false_iff) contra
                                 in Refl

TotalMap : Type -> Type
TotalMap a = Id -> a

t_empty : (v : a) -> TotalMap a
t_empty = const

t_update : (x : Id) -> (v : a) -> (m : TotalMap a) -> TotalMap a
t_update x v m = \y => if beq_id x y then v else m y

t_update_eq : (t_update x v m) x = v
t_update_eq {x} = rewrite sym $ beq_id_refl x in Refl

t_update_neq : Not (x = y) -> (t_update x v m) y = m y
t_update_neq not_eq = rewrite (snd beq_id_false_iff) not_eq
                      in Refl

function_extensionality : ((x : t) -> f x = g x) -> f = g
function_extensionality = really_believe_me

t_update_shadow : t_update x v2 $ t_update x v1 m = t_update x v2 m
t_update_shadow {x} = function_extensionality $ \y => case decEq x y of
  Yes prf => rewrite (snd beq_id_true_iff) prf in Refl
  No contra => rewrite (snd beq_id_false_iff) contra in Refl

beq_idP : {x, y : Id} -> Reflect (x = y) (beq_id x y)
beq_idP = iff_reflect $ iff_sym $ beq_id_true_iff

t_update_same : t_update x (m x) m = m
t_update_same {x} = function_extensionality $ \y => case decEq x y of
  Yes prf => rewrite (snd beq_id_true_iff) prf in cong prf
  No contra => rewrite (snd beq_id_false_iff) contra in Refl

t_update_permute : Not (x2 = x1) -> t_update x1 v1 $ t_update x2 v2 m
                                  = t_update x2 v2 $ t_update x1 v1 m
t_update_permute {x1} {x2} x2_neq_x1 = function_extensionality $ \y =>
  case decEq x1 y of
    Yes x1_eq_y => rewrite (snd beq_id_true_iff) x1_eq_y
                   in rewrite sym x1_eq_y
                   in rewrite (snd beq_id_false_iff) x2_neq_x1
                   in Refl
    No x1_neq_y => rewrite (snd beq_id_false_iff) x1_neq_y
                   in Refl

PartialMap : Type -> Type
PartialMap a = TotalMap (Maybe a)

empty : PartialMap a
empty = t_empty Nothing

update : (x : Id) -> (v : a) -> (m : PartialMap a) -> PartialMap a
update x v m = t_update x (Just v) m

apply_empty : empty {a} x = Nothing {a}
apply_empty = Refl

update_eq : (update x v m) x = Just v
update_eq {v} = t_update_eq {v=Just v}

update_neq : Not (x2 = x1) -> (update x2 v m) x1 = m x1
update_neq {x1} {x2} {v} = t_update_neq {x=x2} {y=x1} {v=Just v}

update_shadow : update x v2 $ update x v1 m = update x v2 m
update_shadow {v1} {v2} = t_update_shadow {v1=Just v1} {v2=Just v2}

update_same : m x = Just v -> update x v m = m
update_same prf = rewrite sym prf in t_update_same

update_permute : Not (x2 = x1) -> update x1 v1 $ update x2 v2 m
                                = update x2 v2 $ update x1 v1 m
update_permute {v1} {v2} = t_update_permute {v1=Just v1} {v2=Just v2}
