data Term =
       TmTrue
     | TmFalse
     | TmZero
     | TmSucc Term
     | TmPred Term
     | TmIsZero Term
     | TmIf Term Term Term
    deriving(Show)

isNumeric :: Term -> Bool
isNumeric TmZero = True
isNumeric (TmSucc t) = isNumeric t
isNumeric _ = False

isVal :: Term -> Bool
isVal TmTrue = True
isVal TmFalse = True
isVal t = isNumeric t

smallstep :: Term -> Maybe Term
smallstep (TmSucc t) = case (smallstep t) of
    Nothing -> Nothing
    Just t' -> Just (TmSucc t')
smallstep (TmPred TmZero) = Just TmZero
smallstep (TmPred (TmSucc t)) = if (isNumeric t) then Just t else Nothing
smallstep (TmPred t) = case (smallstep t) of
    Nothing -> Nothing
    Just t' -> Just (TmPred t')
smallstep (TmIsZero TmZero) = Just TmTrue
smallstep (TmIsZero (TmSucc t)) = if (isNumeric t) then Just TmFalse else Nothing
smallstep (TmIsZero t) = case (smallstep t) of
    Nothing -> Nothing
    Just t' -> Just (TmIsZero t')
smallstep (TmIf TmTrue t t') = Just t
smallstep (TmIf TmFalse t t') = Just t'
smallstep (TmIf t t' t'') = case (smallstep t) of
    Nothing -> Nothing
    Just s -> Just (TmIf s t' t'')
smallstep _ = Nothing

multistep :: Term -> Maybe Term
multistep t = case (smallstep t) of
    Nothing -> Just t
    Just t' -> multistep t'

exampleTerm :: Term
exampleTerm = TmIf (TmIsZero TmZero) (TmSucc TmZero) (TmFalse)