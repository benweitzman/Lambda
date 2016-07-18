{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lib where

import Debug.Trace

import Data.Monoid

import Data.Proxy

import Data.Singletons.Prelude

import Data.Tagged

import Data.Typeable

import qualified Data.Kind as K

import GHC.TypeLits

type Name = String

data Kind = Star
          | KArrow Kind Kind

data Type (k :: Kind) where
  TLit :: a -> Type Star
  TCon :: Symbol -> Type k
  TApp :: Type (KArrow k1 k2) -> Type k1 -> Type k2

type TInt = TLit Int
type TBool = TLit Bool

type family TArr :: Type (KArrow Star (KArrow Star Star)) where
  TArr = TCon "arr"

infixr -->

type (-->) a b = TApp (TApp TArr a) b

data Expr (n :: Maybe Symbol) (ctx :: [(Symbol, Type Star)]) (t :: Type Star) where
  Lit :: (Show a, Typeable a) => a -> Expr 'Nothing ctx (TLit a)
  Var :: forall n ctx t . (KnownSymbol n, Lookup n ctx ~ 'Just t, Typeable t) => Expr ('Just n) ctx t
  App :: (Typeable a, Typeable b) => Expr x ctx (a --> b) -> Expr y ctx a -> Expr 'Nothing ctx b
  Lam :: (KnownSymbol n) => Expr x ('(n, a) ': ctx) b -> Expr ('Just n) ctx (a --> b)

-- | This is a workaround since the order of the foralls in the gadt is not respected
var :: forall n ctx t . (KnownSymbol n, Lookup n ctx ~ 'Just t, Typeable t) => Expr ('Just n) ctx t
var = Var

-- | Likewise
lam :: forall n x ctx a b . (KnownSymbol n) => Expr x ('(n, a) ': ctx) b -> Expr ('Just n) ctx (a --> b)
lam = Lam

data Val (t :: Type Star) where
  VLit :: Show a => a -> Val (TLit a)
  VBuiltIn :: (Show a, Typeable a) => (a -> Val b) -> Val (TLit a --> b)
  VClosure :: (KnownSymbol n) => Proxy n -> Expr q ('(n, a) ': ctx) b -> Env ctx -> Val (a --> b)

data SomeVal = forall t . (Typeable t) => SomeVal (Val t)

type Scope = [(Name, SomeVal)]

instance Show (Val t) where
  show (VLit l) = show l
  show (VBuiltIn f) = "<<builtin>>"
  show (VClosure p body _) = "(\\" <> symbolVal p <> " -> " <> show body <> ")"

instance Show (Expr q ctx t) where
  show (Lit x) = show x
  show (App e1 e2) = show e1 <> " " <> show e2
  show v@Var = showNamed v
  show l@(Lam _) = showNamed l

showNamed :: forall n ctx t . Expr ('Just n) ctx t -> String
showNamed Var = symbolVal (Proxy @n)
showNamed (Lam body) = "(\\" <> (symbolVal (Proxy @n)) <> " -> " <> show body <> ")"


infixr :>

data Env (ctx :: [(Symbol, Type Star)]) where
  Empty :: Env '[]
  (:>) :: forall n t ctx . (KnownSymbol n, Typeable t) => Val t -> Env ctx -> Env ('(n, t) ': ctx)


(+++) :: Env a -> Env b -> Env (a :++ b)
Empty +++ b = b
(x :> y) +++ b = x :> (y +++ b)


lookupVal1 :: forall (p :: Symbol) ctx v rest t q t'
            . (KnownSymbol p, Typeable t)
           => Env ('(q, t') ': ctx)
           -> Maybe (Val t)
lookupVal1 (val :> rest) = case eqT of
  Just (Refl :: p :~: q)  -> cast val
  Nothing -> lookupVal' @p rest

lookupVal' :: forall (p :: Symbol) ctx v rest t
            . (KnownSymbol p, Typeable t)
           => Env ctx
           -> Maybe (Val t)
lookupVal' Empty = Nothing
lookupVal' g@(val :> rest) = lookupVal1 @p g


lookupVal :: forall p ctx t . (Lookup p ctx ~ Just t, Typeable t, KnownSymbol p)
          => Env ctx
          -> Val t
lookupVal ctx = case lookupVal' @p ctx of
  Just x -> x
  Nothing -> error "this shouldn't happen!"

deriving instance Show SomeVal

instance Show (Env '[]) where
  show Empty = "Empty"

instance (Show (Env ctx), Typeable t) => Show (Env ('(p, t) ': ctx)) where
  show (v :> rest) = "(" <> symbolVal (Proxy @p) <> ", " <> show v <> ") :> " <> show rest


evalNamed :: forall ctx t n
           . Env ctx
          -> Expr ('Just n) ctx t
          -> Val t
evalNamed scope Var = lookupVal @n scope
evalNamed scope (Lam body) = VClosure (Proxy @n) body scope

eval' :: forall ctx t (b :: Type Star) q
       . Env ctx
      -> Expr q ctx t
      -> Val t
eval' _ (Lit l) = VLit l
eval' scope v@Var = evalNamed scope v
eval' scope (App e1 e2) = let
  f = eval' scope e1
  a = eval' scope e2
  in
    case f of
    VClosure (_ :: Proxy p) body closure -> eval' (a :> closure) body
    VBuiltIn f' -> case a of
      VLit v -> f' v
eval' scope l@(Lam body) = evalNamed scope l

check' :: Env ctx -> Expr q ctx t -> Expr q ctx t
check' _ = id

check = check' base

eval e = eval' base e

succ' :: Val ('TLit Int --> 'TLit Int)
succ' = VBuiltIn $ \x -> VLit (x + 1)

plus :: Val ('TLit Int --> 'TLit Int --> 'TLit Int)
plus = VBuiltIn (\x -> VBuiltIn (\y -> VLit (x + y)))


base = (:>) @"succ" succ' $
       (:>) @"+" plus $
       Empty

someFunc :: IO ()
someFunc = putStrLn "someFunc"
