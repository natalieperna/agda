
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.NVTTerm.Pretty () where

import Prelude hiding (Floating)

import Control.Arrow ((&&&), (***), first, second)
import Control.Applicative
import Control.Monad.Reader
import Data.Maybe

import Agda.Syntax.Treeless
import Agda.Compiler.Treeless.NVTTerm
import Agda.Utils.Pretty

data PEnv = PEnv { pPrec :: Int
                 , pFresh :: [String]
                 , pBound :: [String] }

type P = Reader PEnv

withName :: (String -> P a) -> P a
withName k = withNames 1 $ \[x] -> k x

withNames :: Int -> ([String] -> P a) -> P a
withNames n k = do
  (xs, ys) <- asks $ splitAt n . pFresh
  local (\ e -> e { pFresh = ys }) (k xs)

paren :: Int -> P Doc -> P Doc
paren p doc = do
  n <- asks pPrec
  (if p < n then parens else id) <$> doc

prec :: Int -> P a -> P a
prec p = local $ \ e -> e { pPrec = p }

name :: Int -> P String
name x = asks $ (!! x) . (++ map (('^' :) . show) [1..]) . pBound

runP :: P a -> a
runP p = runReader p PEnv{ pPrec = 0, pFresh = names, pBound = [] }
  where
    names = [ x ++ i | i <- "" : map show [1..], x <- map (:[]) ['a'..'z'] ]

instance Pretty NVTTerm where
  prettyPrec p t = runP $ prec p (pTerm t)

opName :: TPrim -> String
opName PAdd = "+"
opName PSub = "-"
opName PMul = "*"
opName PQuot = "quot"
opName PRem = "rem"
opName PGeq = ">="
opName PLt  = "<"
opName PEqI = "==I"
opName PEqF = "==F"
opName PEqS = "==S"
opName PEqC = "==C"
opName PEqQ = "==Q"
opName PIf  = "if_then_else_"
opName PSeq = "seq"

isInfix :: TPrim -> Maybe (Int, Int, Int)
isInfix op =
  case op of
    PMul -> l 7
    PAdd -> l 6
    PSub -> l 6
    PGeq -> non 4
    PLt  -> non 4
    p | isPrimEq p -> non 4
    _    -> Nothing
  where
    l n   = Just (n, n, n + 1)
    r n   = Just (n, n + 1, n)
    non n = Just (n, n + 1, n + 1)

pTerm' :: Int -> NVTTerm -> P Doc
pTerm' p = prec p . pTerm

pVar :: Var -> P Doc
pVar = return . text . show

pTerm :: NVTTerm -> P Doc
pTerm t = case t of
  NVTVar v -> pVar v
  NVTApp (NVTPrim op) [a, b] | Just (c, l, r) <- isInfix op ->
    paren c $ sep <$> sequence [ pTerm' l a
                               , pure $ text $ opName op
                               , pTerm' r b ]
  NVTApp (NVTPrim PIf) [a, b, c] ->
    paren 0 $ (\ a b c -> sep [ text "if" <+> a
                              , nest 2 $ text "then" <+> b
                              , nest 2 $ text "else" <+> c ])
              <$> pTerm' 0 a
              <*> pTerm' 0 b
              <*> pTerm c
  NVTDef var f -> text . shows f <$> case var of
    NVTDefDefault -> return ""
    NVTDefAbstractPLet is -> do
      let vs = map show is
      return $ ".dv[ " ++ unwords (vs ++ ["]"])
  NVTCon c -> pure $ text (show c)
  NVTLit l -> pure $ pretty l
  NVTPrim op | isJust (isInfix op) -> pure $ text ("_" ++ opName op ++ "_")
             | otherwise -> pure $ text (opName op)
  NVTApp f es ->
    paren 9 $ (\a bs -> sep [a, nest 2 $ fsep bs])
              <$> pTerm' 9 f
              <*> mapM (pTerm' 10) es
  NVTLam _v _ -> paren 0 $
    (\b -> sep [ text ("λ " ++ unwords vs ++ " →")
               , nest 2 b ]) <$> pTerm' 0 b
    where
      (vs, b) = lamV id t
      lamV acc (NVTLam v b) = lamV (acc . (show v :)) b
      lamV acc t        = (acc [], t)
  NVTLet{} -> paren 0 $
    (\ (binds, b) -> sep [ text "let" <+> vcat [ sep [ text x <+> text "="
                                                     , nest 2 e ] | (x, e) <- binds ]
                              <+> text "in", b ])
      <$> pLets es b
    where
      (es, b) = letV id t
      letV acc (NVTLet v e b) = letV (acc . ((show v, e) :)) b
      letV acc t              = (acc [], t)

      pLets [] b = ([],) <$> pTerm' 0 b
      pLets ((x, e) : bs) b = do
        e <- pTerm' 0 e
        first ((x, e) :) <$> pLets bs b

  NVTCase x _ def alts -> paren 0 $
    (\ sc alts defd ->
      sep [ text "case" <+> sc <+> text "of"
          , nest 2 $ vcat (alts ++ [ text "_ →" <+> defd | null alts || def /= NVTError TUnreachable ]) ]
    ) <$> pTerm' 0 (NVTVar x)
      <*> mapM pAlt alts
      <*> pTerm' 0 def
    where
      pAlt (NVTALit l b) = pAlt' <$> pTerm' 0 (NVTLit l) <*> pTerm' 0 b
      pAlt (NVTAGuard g b) =
        pAlt' <$> ((text "_" <+> text "|" <+>) <$> pTerm' 0 g)
              <*> (pTerm' 0 b)
      pAlt (NVTACon c cvars b) =
        -- withNames (length cvars) $ \ xs ->
        pAlt' <$> pTerm' 0 (NVTApp (NVTCon c) [NVTVar i | i <- reverse cvars])
              <*> pTerm' 0 b
      pAlt' p b = sep [p <+> text "→", nest 2 b]

  NVTUnit -> pure $ text "()"
  NVTSort -> pure $ text "Set"
  NVTErased -> pure $ text "_"
  NVTError err -> paren 9 $ pure $ text "error" <+> text (show (show err))

instance Pretty NVPat where
  prettyPrec p t = runP $ prec p (pPat t)

instance Pretty NVConPat where
  prettyPrec p t = runP $ prec p (pConPat t)

instance Pretty Floating where
  prettyPrec p t = runP $ prec p (pFloating t)

pConPat :: NVConPat -> P Doc
pConPat (NVConPat _ct _dft c pats) =
    paren 9 $ (\ a bs -> sep [a, nest 2 $ fsep bs])
              <$> pTerm' 9 (NVTCon c)
              <*> mapM (pPat' 10) pats

pPat :: NVPat -> P Doc
pPat p = case p of
  NVPVar v -> pVar v
  NVPAsCon v cp -> do
    v' <- pVar v
    cp' <- prec 10 $ pConPat cp
    return $ hcat [v', text "@", cp']

pPat' :: Int -> NVPat -> P Doc
pPat' p = prec p . pPat

pFloating :: Floating -> P Doc
pFloating fl = case fl of
  FloatingPLet pat rhs _ -> do
    pat' <- pPat pat
    rhs' <- pTerm rhs
    return $ text "let" <+> sep [ pat' <+> text "=", nest 2 rhs' ]
  FloatingCase v cp -> do
    v' <- pVar v
    cp' <- pConPat cp
    return $ text "case" <+> sep [ v' <+> text "of", nest 2 cp' ]
