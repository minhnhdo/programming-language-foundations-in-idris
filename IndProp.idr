module IndProp

import Logic

%access public export

%default total

data Reflect : (p : Type) -> Bool -> Type where
  ReflectT : p -> (b=True) -> Reflect p b
  ReflectF : (Not p) -> (b=False) -> Reflect p b

iff_reflect : (p ↔ (b=True)) -> Reflect p b
iff_reflect {b = False} (pb, _) = ReflectF (uninhabited . pb) Refl
iff_reflect {b = True} (_, bp) = ReflectT (bp Refl) Refl

reflect_iff : Reflect p b -> (p ↔ (b=True))
reflect_iff (ReflectT p b_true) = (\_ => b_true, \_ => p)
reflect_iff (ReflectF not_p b_false) =
  ( \p => void (not_p p)
  , \b_true => void . uninhabited $
      the (False = True) $ rewrite sym b_false in b_true)
