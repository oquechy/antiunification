import Data.List
import Data.Maybe
import Control.Exception.Base
import qualified Data.Map.Lazy as Map
import Debug.Trace

data IType = IVar String
           | IFun IType IType
           | Both IType IType
                deriving Eq

data PType = PVar String
           | PFun PType PType
           | Forall String PType
                deriving Eq

data ExtPType = EVar String
              | SVar String
              | EFun ExtPType ExtPType
              | EForall String ExtPType
                deriving (Eq, Ord)

instance Show PType where
  show (PVar v) = v
  show (PFun s t) = "(" ++ (show s) ++ ") -> (" ++ (show t) ++ ")"
  show (Forall v s) = "∀" ++ v ++ "." ++ show s

instance Show IType where
  show (IVar v) = v
  show (IFun s t) = "(" ++ show s ++ ") -> (" ++ (show t) ++ ")"
  show (Both x y) = show x ++ " ^ " ++ show y

instance Show ExtPType where
  show (EVar v) = "var " ++ v
  show (SVar v) = "sub " ++ v
  show (EFun s t) = "(" ++ (show s) ++ ") -> (" ++ (show t) ++ ")"
  show (EForall v s) = "∀" ++ v ++ "." ++ show s

freeVars :: ExtPType -> [String]
freeVars (EVar v)      = [v]
freeVars (SVar v)      = [v]
freeVars (EFun s t)    = union (freeVars s) (freeVars t)
freeVars (EForall v s) = freeVars s \\ [v]

rename :: ExtPType -> String -> String -> ExtPType
rename t@(EVar v) x y
  | x == v    = EVar y
  | otherwise = t
rename t@(SVar v) x y
  | x == v    = error "Bounded variable with same name as substitution variable"
  | otherwise = t
rename (EFun s t) x y = EFun (rename s x y) (rename t x y)
rename t@(EForall v s) x y
  | v == x    = t
  | otherwise = EForall v (rename s x y)

-- A bounded variable from s shouldn't have the same name as any other variable from s and t.
-- The same for t.
check :: [String] -> ExtPType -> ExtPType -> Bool
check bound s t
    | noBounds s && noBounds t = True
    | otherwise                = check' bound s t
    where noBounds :: ExtPType -> Bool
          noBounds s = null $ intersect (freeVars s) bound
          check' :: [String] -> ExtPType -> ExtPType -> Bool
          check' bound (EVar s)      (EVar t)      = s == t
          check' bound (SVar s)      (SVar t)      = s == t
          check' bound (EFun s t)    (EFun s' t')  = check bound s s' && check bound t t'
          -- Variables x and y are free in s and t => invariant for bounded variables is kept.
          check' bound (EForall x s) (EForall y t) = check (x:bound) s (rename t y x)
          check' _ _ _                             = False

subs :: [String]
subs = zipWith (\x y -> x ++ show y) as [1..]
  where as = "a" : as

freshVars :: [String]
freshVars = zipWith (\x y -> x ++ show y) us [1..]
  where us = "u" : us

type Unif = Map.Map (ExtPType, ExtPType) String

aUni :: Unif -> [String] -> ExtPType -> ExtPType -> (Unif, [String], ExtPType)
aUni unified subs s@(EVar x) t@(EVar y)
  | x == y                    = (unified, subs, EVar x)
  | Map.member (s, t) unified = (unified, subs, SVar $ unified Map.! (s, t))
  | otherwise                 = let sub:subs' = subs in (Map.insert (s, t) sub unified, subs', SVar sub)
aUni unified subs s@(SVar x) t@(SVar y)
  | x == y                    = (unified, subs, SVar x)
  | Map.member (s, t) unified = (unified, subs, SVar $ unified Map.! (s, t))
  | otherwise                 = let sub:subs' = subs in (Map.insert (s, t) sub unified, subs', SVar sub)
aUni unified subs (EFun s s') (EFun t t')           = let (unified', subs', u)   = aUni unified subs s t in
                                                      let (unified'', subs'', v) = aUni unified' subs' s' t' in
                                                         (unified'', subs'', EFun u v)
aUni unified subs s@(EForall x s') t@(EForall y t') = let t'' = rename t' y x in
                                                        if check [x] s' t''
                                                           then let (unified', subs', u) = aUni unified subs s' t'' in
                                                            (unified, subs', EForall x u)
                                                           else let sub:subs' = subs in
                                                            (Map.insert (s, t) sub unified, subs', SVar sub)
aUni unified subs s t
  | Map.member (s, t) unified = (unified, subs, SVar $ unified Map.! (s, t))
  | otherwise                 = let sub:subs' = subs in (Map.insert (s, t) sub unified, subs', SVar sub)

trimForall :: PType -> ExtPType
trimForall p = trimPrefix [] p
  where trimPrefix :: [String] -> PType -> ExtPType
        trimPrefix trimmed (Forall x s) = trimPrefix ([x] `union` trimmed) s
        trimPrefix trimmed p            = trimSuffix trimmed p
        trimSuffix :: [String] -> PType -> ExtPType
        trimSuffix trimmed (PVar v)
                  | v `elem` trimmed = SVar v
                  | otherwise        = EVar v
        trimSuffix trimmed (PFun x y) = EFun (trimSuffix trimmed x) (trimSuffix trimmed y)
        trimSuffix trimmed (Forall x s) = assert (x `notElem` trimmed) (EForall x $ trimSuffix trimmed s)

greatestLowerBound :: Unif -> [String] -> PType -> PType -> (Unif, [String], PType)
greatestLowerBound unified subs s t = let (unif, subs', p) = aUni unified subs (trimForall s) (trimForall t) in
                                      (unif, subs', extendForall p)

extendForall :: ExtPType -> PType
extendForall p = let (subs, p') = getSubs p in addForallVars subs p'
  where getSubs :: ExtPType -> ([String], PType)
        getSubs (EVar v)      = ([], PVar v)
        getSubs (SVar v)      = ([v], PVar v)
        getSubs (EFun x y)    = let (subs, p) = getSubs x in
                                let (subs', p') = getSubs y in
                                (subs `union` subs', PFun p p')
        getSubs (EForall v s) = let (subs, p) = getSubs s in (subs, Forall v p)
        addForallVars :: [String] -> PType -> PType
        addForallVars subs p = foldr (\v p -> Forall v p) p subs

tr :: IType -> PType
tr i = let (_, _, t) = tr' Map.empty subs i in t
  where tr' :: Unif -> [String] -> IType -> (Unif, [String], PType)
        tr' unified subs (IVar v)   = (unified, subs, PVar v)
        tr' unified subs (IFun s t) = let (unif, subs', p)   = tr' unified subs s in
                                      let (unif', subs'', p') = tr' unif subs' t in
                                      (unif', subs'', PFun p p')
        tr' unified subs (Both s t) = let (unif, subs', p)   = tr' unified subs s in
                                      let (unif', subs'', p') = tr' unif subs' t in
                                      greatestLowerBound unif' subs'' p p'

main :: IO ()
main = do
  -- test check
  assert (      check []    (EVar "x")                                (EVar "y"))                                   (putStrLn "#1 OK")
  assert (not $ check ["x"] (EVar "x")                                (EVar "y"))                                   (putStrLn "#2 OK")
  assert (      check ["x"] (EVar "x")                                (EVar "x"))                                   (putStrLn "#3 OK")
  assert (      check ["x"] (EFun (EVar "x") (EForall "s" (EVar "x"))) (EFun (EVar "x") (EForall "t" (EVar "x"))))  (putStrLn "#4 OK")
  assert (not $ check ["x"] (EFun (EVar "x") (EForall "s" (EVar "x"))) (EFun (EVar "x") (EForall "t" (EVar "t"))))  (putStrLn "#5 OK")
  assert (      check ["x"] (EFun (EVar "x") (EForall "s" (EVar "s"))) (EFun (EVar "x") (SVar "t")))                (putStrLn "#6 OK")
  assert (not $ check ["x"] (EFun (EVar "x") (EForall "s" (EVar "x"))) (EFun (EVar "x") (EVar "x")))                (putStrLn "#7 OK")
  assert (      check ["x"] (EForall "x" (EFun (EVar "x") (EVar "x"))) (EForall "y" (EFun (SVar "y") (SVar "y"))))  (putStrLn "#8 OK")
  assert (not $ check ["x"] (EForall "y" (EFun (EVar "y") (EVar "x"))) (EForall "z" (EFun (EVar "y") (EVar "y"))))  (putStrLn "#9 OK")
  assert (      check []    (EForall "x" $ EFun (EForall "y" $ EVar "y") (EForall "z" $ EVar "x"))
                            (EForall "b" $ EFun (EForall "c" $ (EFun (EVar "d") (EVar "c"))) (EForall "d" $ EVar "b"))) (putStrLn "#10 OK")
  -- test aUni
  let (_, _, gen) = aUni Map.empty subs (EVar "x") (EVar "x")
  assert (gen == EVar "x")                                                                        (putStrLn "#11 OK")
  let (_, _, gen) = aUni Map.empty subs (EVar "x") (EVar "y")
  assert (gen == SVar "a1")                                                                       (putStrLn "#12 OK")
  let (_, _, gen) = aUni Map.empty subs (EVar "x") (EFun (EVar "y") (EVar "y"))
  assert (gen == SVar "a1")                                                                       (putStrLn "#13 OK")
  let (_, _, gen) = aUni Map.empty subs (EForall "x" (EFun (EVar "y") (EVar "y"))) (EFun (EVar "y") (EVar "y"))
  assert (gen == SVar "a1")                                                                       (putStrLn "#14 OK")
  let (_, _, gen) = aUni Map.empty subs (EFun (EFun (EVar "x") (EVar "y")) (EVar "z"))
                           (EFun (EFun (EVar "y") (EForall "y" (EVar "y"))) (EVar "y"))
  assert (gen == EFun (EFun (SVar "a1") (SVar "a2")) (SVar "a3"))                                 (putStrLn "#15 OK")
  let (_, _, gen) = aUni Map.empty subs (EForall "x" $ EFun (EForall "y" $ EVar "x") (EForall "z" $ EVar "y"))
                           (EForall "b" $ EFun (EForall "c" $ (EFun (EVar "b") (EVar "d"))) (EForall "d" $ EVar "b"))
  assert (gen == SVar "a1")                                                                       (putStrLn "#16 OK")
  let (_, _, gen) = aUni Map.empty subs (EForall "x" $ EFun (EForall "y" $ EVar "y") (EForall "z" $ EVar "x"))
                           (EForall "b" $ EFun (EForall "c" $ (EFun (EVar "d") (EVar "c"))) (EForall "d" $ EVar "b"))
  assert (gen == EForall "x" (EFun (SVar "a1") (EForall "z" $ EVar "x")))                         (putStrLn "#17 OK")
  -- test trimForall
  assert (trimForall (PVar "a") == EVar "a")                                                      (putStrLn "#18 OK")
  assert (trimForall (Forall "a" (PVar "a")) == SVar "a")                                         (putStrLn "#19 OK")
  assert (trimForall (Forall "b" (PVar "a")) == EVar "a")                                         (putStrLn "#20 OK")
  let trim = trimForall (Forall "a" $ Forall "b" (PFun (PVar "a") (Forall "c" (PVar "c"))))
  assert (trim == EFun (SVar "a") (EForall "c" (EVar "c")))                                       (putStrLn "#21 OK")
  -- test greatestLowerBound
  let (_, _, glb) = greatestLowerBound Map.empty subs (PVar "x") (PVar "x")
  assert (glb == PVar "x")                                                                        (putStrLn "#22 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (PVar "x") (PVar "y")
  assert (glb == Forall "a1" (PVar "a1"))                                                         (putStrLn "#23 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (PVar "x") (PFun (PVar "y") (PVar "y"))
  assert (glb == Forall "a1" (PVar "a1"))                                                         (putStrLn "#24 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (Forall "x" (PFun (PVar "y") (PVar "y"))) (PFun (PVar "y") (PVar "y"))
  assert (glb == PFun (PVar "y") (PVar "y"))                                                      (putStrLn "#25 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (PFun (PFun (PVar "x") (PVar "y")) (PVar "z"))
                                         (PFun (PFun (PVar "y") (Forall "y" (PVar "y"))) (PVar "y"))
  assert (glb == Forall "a1" (Forall "a2" (Forall "a3"
                  (PFun (PFun (PVar "a1") (PVar "a2")) (PVar "a3")))))                            (putStrLn "#26 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (Forall "x" $ PFun (Forall "y" $ PVar "x") (Forall "z" $ PVar "y"))
                                         (Forall "b" $ PFun (Forall "c" $ (PFun (PVar "b") (PVar "d"))) (Forall "d" $ PVar "b"))
  putStrLn (show glb)
  assert (glb == Forall "a1" (Forall "a2"
                   (PFun (Forall "y" (PVar "a1")) (Forall "z" (PVar "a2")))))                     (putStrLn "#27 OK")
  let (_, _, glb) = greatestLowerBound Map.empty subs (Forall "x" $ PFun (Forall "y" $ PVar "y") (Forall "z" $ PVar "x"))
                                         (Forall "b" $ PFun (Forall "c" $ (PFun (PVar "d") (PVar "c"))) (Forall "d" $ PVar "b"))
  putStrLn (show glb)
  assert (glb == Forall "a1" (Forall "a2" (PFun (PVar "a1") (Forall "z" $ PVar "a2"))))           (putStrLn "#28 OK")
  -- test tr
  assert (tr (IVar "x") == (PVar "x"))                                                            (putStrLn "#29 OK")
  let t = Both (IVar "x") (IFun (IVar "x") (IVar "x"))
  putStrLn (show $ tr (IFun t t))
  -- \x -> x
  assert (tr (IFun t t) == (PFun (Forall "a1" (PVar "a1")) (Forall "a1" (PVar "a1"))))            (putStrLn "#30 OK")
  -- \x -> x x
  putStrLn (show $ tr (IFun t (IVar "x")))
  assert (tr (IFun t (IVar "x")) == (PFun (Forall "a1" (PVar "a1")) (PVar "x")))   (putStrLn "#31 OK")
  let a'   = IFun (IVar "p") (IVar "p")
  let pa'  = PFun (PVar "p") (PVar "p")
  let a    = IFun (Both a' (IFun a' a')) a'
  let b''  = IFun (IVar "q") (IFun (IVar "q") (IVar "q"))
  let pb'' = PFun (PVar "q") (PFun (PVar "q") (PVar "q"))
  let b'   = IFun b'' b''
  let pb'  = PFun pb'' pb''
  let b    = IFun (Both b'' (IFun b'' b')) b'
  putStrLn (show $ tr a)
  assert (tr a == (PFun (Forall "a1" (PFun (PVar "a1") (PVar "a1"))) pa'))                        (putStrLn "#32 OK")
  putStrLn (show $ tr b)
  assert (tr b == (PFun (Forall "a1" (PFun (PVar "a1") (PFun (PVar "a1") (PVar "a1")))) pb'))     (putStrLn "#32 OK")
  putStrLn (show $ tr (Both a b))
  assert (tr (Both a b) == (Forall "a3" (Forall "a4"
                              (PFun (PVar "a3") (PFun (PVar "a4") (PVar "a4"))))))                (putStrLn "#34 OK")

