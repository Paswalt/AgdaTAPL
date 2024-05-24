data Type = TyBool | TyArrow Type Type
  deriving(Show, Eq)

data Term =
    TmVar Int
  | TmAbs Type Term
  | TmApp Term Term
  | TmTrue
  | TmFalse
  | TmIf Term Term Term
  deriving(Show)

type Context = [Type]

addBinding :: Context -> Type -> Context
addBinding ctx ty = ty : ctx

shift :: Int -> Int -> Term -> Term
shift d c t = case t of
  (TmVar i)       -> if i >= c then (TmVar (i + d)) else (TmVar i)
  (TmAbs ty t)    -> TmAbs ty (shift d (c + 1) t)
  (TmApp t1 t2)   -> TmApp (shift d c t1) (shift d c t2) 
  (TmTrue)        -> TmTrue
  (TmFalse)       -> TmFalse
  (TmIf t1 t2 t3) -> TmIf (shift d c t1) (shift d c t2) (shift d c t3)

sub :: Int -> Term -> Term -> Term
sub j s t = case t of
  (TmVar i)       -> if i == j then s else (TmVar i)
  (TmAbs ty t1)   -> TmAbs ty (sub (j+1) (shift 1 0 s) t1)
  (TmApp t1 t2)   -> (TmApp (sub j s t1) (sub j s t2)) 
  (TmTrue)        -> TmTrue
  (TmFalse)       -> TmFalse
  (TmIf t1 t2 t3) -> TmIf (sub j s t1) (sub j s t2) (sub j s t3)

tyLookup :: Int -> Context -> Maybe Type
tyLookup i ctx = if i < 0 then Nothing else lookup' i ctx
  where lookup' :: Int -> Context -> Maybe Type
        lookup' i [] = Nothing
        lookup' 0 (ty:ctx) = Just ty
        lookup' i (ty:ctx) = lookup' (i - 1) ctx 

typeof :: Context -> Term -> Maybe Type
typeof ctx (TmVar i) = tyLookup i ctx
typeof ctx (TmTrue) = Just TyBool
typeof ctx (TmFalse) = Just TyBool
typeof ctx (TmAbs ty t1) = case (typeof (addBinding ctx ty) t1) of
      Nothing -> error ("(" ++ (show t1) ++ ")" ++ " is ill typed")
      Just ty' -> Just (TyArrow ty ty')
typeof ctx (TmApp t1 t2) = case (typeof ctx t1) of
      Nothing -> error ("(" ++ (show t1) ++ ")" ++ " is ill typed")
      Just TyBool -> error ("(" ++ (show t1) ++ ")" ++ " must be of type TyArrow")
      Just (TyArrow ty1 ty2) -> case (typeof ctx t2) of
          Nothing -> error ("(" ++ (show t2) ++ ")" ++ " is ill typed")
          Just ty3 -> if (ty1 == ty3) then Just ty2 else
            error ("Argument type " ++ (show ty1) ++ " expected. Got: " ++ (show ty3))
typeof ctx (TmIf t1 t2 t3) = case (typeof ctx t1) of
      Nothing -> error ("(" ++ (show t1) ++ ")" ++ " is ill typed")
      Just (TyArrow _ _) -> error ("(" ++ (show t1) ++ ")" ++ " must evaluate to TyBool")
      Just TyBool -> case (typeof ctx t2) of
        Nothing -> error ("(" ++ (show t2) ++ ")" ++ " is ill typed")
        Just ty2 -> case (typeof ctx t3) of
          Nothing -> error ("(" ++ (show t3) ++ ")" ++ " is ill typed") 
          Just ty3 -> if (ty2 == ty3) then Just ty2 else
            (error ("If-branch type mismatch. Got:\n"
             ++ "(" ++ (show t2) ++ ")" ++ " of type " ++ (show ty2)
             ++ "\n" ++ "(" ++ (show t3) ++ ")" ++ " of type " ++ (show ty3)))
          
exampleTerm :: Term
exampleTerm = TmIf TmTrue (TmAbs TyBool (TmVar 0)) (TmAbs TyBool TmFalse)

exampleTerm2 :: Term
exampleTerm2 = TmIf TmFalse TmTrue (TmAbs TyBool TmTrue)

isValue :: Term -> Bool
isValue TmTrue = True
isValue TmFalse = True
isValue (TmAbs _ _) = True
isValue _ = False

smallstep :: Term -> Maybe Term
smallstep (TmApp (TmAbs _ t1) v) = if (isValue v) then Just (shift (-1) 0 (sub 0 (shift 1 0 v) t1)) else Nothing
smallstep (TmApp t1 t2) = case (isValue t1) of
  False -> do
    t1' <- smallstep t1
    Just (TmApp t1' t2)
  True  -> do
    t2' <- smallstep t2
    Just (TmApp t1 t2')
smallstep (TmIf TmTrue t2 t3) = Just t2
smallstep (TmIf TmFalse t2 t3) = Just t3
smallstep (TmIf t1 t2 t3) = do
  t1' <- smallstep t1
  Just (TmIf t1' t2 t3)
smallstep _ = Nothing

multistep :: Term -> Maybe Term
multistep t = case (typeof [] t) of
  Nothing -> Nothing
  Just _  -> multistep' t
    where multistep' :: Term -> Maybe Term
          multistep' t = case (smallstep t) of
            Nothing -> Just t
            Just t' -> multistep' t'
