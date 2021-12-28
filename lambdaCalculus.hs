
-- Apartat 1: Definir LT

-- Definim el tipus Var per les variables que sera de tipus string
type Var = String

-- Definim el LTa que poden ser variables,
data LT =
    Variable Var
  | Lambda   Var  LT
  | Apply    LT LT

instance Show LT where
  show (Variable x) = x
  show (Lambda x y) = "(/"++x++". " ++ show y ++ ")"
  show (Apply x y) = "("++ show x ++ " " ++ show y ++ ")"

eliminarElement :: Eq a => a-> [a] ->[a]
eliminarElement _ [] = []
eliminarElement x (y:ys)
  | x == y    = eliminarElement x ys
  | otherwise = y : eliminarElement x ys

test1 = Lambda "x" (Apply (Apply (Variable "x") (Variable "x")) (Variable "y"))
test2 = Lambda "y" (Apply (Variable "x") (Lambda "x" (Variable "x")))

freeVars :: LT -> [Var]
freeVars (Variable x) = [x]
freeVars (Lambda x y) = (eliminarElement x (freeVars y))
freeVars (Apply x y) = (freeVars x) ++ (freeVars y)

buscarLligada :: Var -> LT -> Bool
buscarLligada lligada (Variable x) = lligada == x
buscarLligada lligada (Lambda x y) = if x==lligada then False else buscarLligada lligada y
buscarLligada lligada (Apply x y) = buscarLligada lligada x || buscarLligada lligada y

boundVars :: LT -> [Var]
boundVars (Variable x) = []
boundVars (Lambda x y) = if buscarLligada x y then x : boundVars y else boundVars y
boundVars (Apply x y) = boundVars x ++ boundVars y

buscarVariable :: [Var] -> Var -> Bool
buscarVariable [] _ = False
buscarVariable (y:ys) x
  | x == y    = True
  | otherwise = buscarVariable ys x


subst :: LT -> Var -> LT -> LT
subst (Variable x) v t = if x==v then t else Variable x -- si la variable es la que es vol subsstituir es retorna el LTa el qual es substituiex, altrament retornem la mateix variable
subst (Apply x y) v t = Apply (subst x v t) (subst y v t) -- es retorna la substitucio aplicada als dos costats de la aplicacio
--si hi ha la variable lliure fer la substitucio sempre i quan el nom concideixi amb un lligat
subst (Lambda x y) v t = if(x==v) then (Lambda x y) --aqui dins segur esta lligada la variable per tant retornemel mateix
                          else if buscarVariable (freeVars t) x then subst (Lambda (x++"_") (subst y x (Variable (x ++ "_")))) v t
                          else (Lambda x (subst y v t)) 

m1 = Lambda "x" (Apply (Apply (Variable "x") (Variable "x")) (Variable "y"))
m2 = Lambda "y" (Apply (Variable "x") (Lambda "x" (Variable "x")))
test_subst_lligada = Lambda "y" (Variable "x")
test_subst_lligada_final = subst test_subst_lligada "x" (Variable "y")

esta_normal :: LT -> Bool
esta_normal (Variable x) = True --si es variable nomes retornem true
esta_normal (Lambda x y) = esta_normal y --si es una lambda tambe retornem true
esta_normal (Apply (Lambda x y) z) = False --si tenim una aplicacio on la part esquerra es una abstracio retornem que no es normal perque hi ha un redex
esta_normal (Apply x y) = esta_normal x && esta_normal y --si tenim una aplicacio d'una altre forma retornem si esta normal els dos costats

-- (\x. x)(\x. x) -> hi ha un redex
testNormal1 = Apply (Lambda "x" (Variable "x")) (Lambda "x" (Variable "x"))

beta_redueix :: LT -> LT
beta_redueix (Variable x) = (Variable x) --Si es una variable retornem la mateixa variable
beta_redueix (Lambda x y) = (Lambda x (beta_redueix y)) --Si es una abstreccio retornem la abstraccio i el el seu LTe li apliquem la funcio de beta redeueix
beta_redueix (Apply (Lambda x y) z) = subst y x z --si observem un redex, retornem el resultat de substituir al LTe de la abstraccio el redex
beta_redueix (Apply x y) = Apply (beta_redueix x)(beta_redueix y) --si es una aplicacio d'una altre forma retornem el resultat de aplicar la beta reduccio als dos costats

e1 = (Lambda "x" (Variable "y")) -- (\x. y)
e2 = (Lambda "x" (Apply (Apply (Variable "x") (Variable "x")) (Variable "x"))) --(\x. x x x)
testBetaRed1 = Apply e1 (Apply e2 e2)

redueix_un_n :: LT -> LT
redueix_un_n x = beta_redueix x

-- \x. \y. ((\f. y (f y x)) (\x. \y. x))
--construccio
ultim = Lambda "x"(Lambda "y" (Variable "x")) --(\x. \y. x)
ePrimerUltim = Apply (Apply (Variable "f")(Variable "y")) (Variable "x") --(f y x) -> mateix que -> ((f y) x)
ePrimer = Lambda "f" (Apply (Variable "y") ePrimerUltim) --(\f. y (f y x))
aplyGran = Apply ePrimer ultim --((\f. y (f y x)) (\x. \y. x))
testRedueixUn = Lambda "x" (Lambda "y" aplyGran) -- \x. \y. ((\f. y (f y x)) (\x. \y. x))

--"\\x. \\y. ((\\f. ((y) (((((f) (y))) (x))))) (\\x. \\y. x))"
primer_pas = redueix_un_n testRedueixUn
segon_pas = redueix_un_n primer_pas
tercer_pas = redueix_un_n segon_pas
quart_pas = redueix_un_n tercer_pas

redueix_un_a :: LT -> LT
redueix_un_a (Variable x) = (Variable x) --Si es una variable retornem la mateixa variable
redueix_un_a (Lambda x y) = (Lambda x (redueix_un_a y)) --Si es una abstreccio retornem la abstraccio i el el seu LTe li apliquem la funcio de redueix un
redueix_un_a (Apply (Lambda x y) z)
                                    | (not (esta_normal z)) = (Apply (Lambda x y) (redueix_un_a z)) --si z no esta normal es redueix primer
                                    | (not (esta_normal y)) = (Apply (Lambda x (redueix_un_a y)) z)  --si y no esta normal es redueix primer
                                    | otherwise = subst y x z --alrament es redueix el lambda actual
redueix_un_a (Apply x y) = if(not (esta_normal y)) then (Apply x (redueix_un_a y)) else (Apply (redueix_un_a x) y)

--testbetared
-- (\x. y)((\x. x x x)(\x. x x x))
-- "((\\x. y) (((\\x. ((((x) (x))) (x))) (\\x. ((((x) (x))) (x))))))"
primer_pas_a = redueix_un_a testBetaRed1
-- (\x. y)((\x. x x x)(\x. x x x)(\x. x x x))
-- "((\\x. y) (((((\\x. ((((x) (x))) (x))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))))"
segon_pas_a = redueix_un_a primer_pas_a
-- "((\\x. y) (((((((\\x. ((((x) (x))) (x))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))))"
tercer_pas_a = redueix_un_a segon_pas_a
-- "((\\x. y) (((((((((\\x. ((((x) (x))) (x))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))) (\\x. ((((x) (x))) (x))))))"
-- ...

l_normalitza_n :: LT -> [LT]
l_normalitza_n x = if esta_normal x then [] else  normalitzat : l_normalitza_n normalitzat
  where
    normalitzat = redueix_un_n x

l_normalitza_a :: LT -> [LT]
l_normalitza_a x = if esta_normal x then [] else  normalitzat : l_normalitza_a normalitzat
  where
    normalitzat = redueix_un_a x

general_list :: (LT -> LT) -> LT -> [LT]
general_list f x = if esta_normal x then [] else  normalitzat : general_list f normalitzat
  where
    normalitzat = f x

normalitza_n :: LT -> (Int,LT)
normalitza_n x = (length arrayLTs,last arrayLTs)
  where
    arrayLTs = l_normalitza_n x

normalitza_a :: LT -> (Int,LT)
normalitza_a x = (length arrayLTs,last arrayLTs)
  where
    arrayLTs = l_normalitza_a x

general_tuple :: (LT -> [LT]) -> LT -> (Int,LT)
general_tuple f x = (length arrayLTs,last arrayLTs)
  where
    arrayLTs = f x

_1 = Lambda "f" (Lambda "x" (Apply (Variable "f")(Variable "x") ))
-- \f. \x. f x
_2 = Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Variable "f")(Variable "x")) ))
_3 = Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Variable "f") (Apply (Variable "f")(Variable "x")) )))
-- \f. \x. f(f x)
_4 = last(l_normalitza_n (Apply (Apply _prod _2) _2))
_16 = last(l_normalitza_n (Apply (Apply _prod _4) _4))
_256 = last(l_normalitza_n (Apply (Apply _prod _16) _16))

_true = Lambda "x" (Lambda "y" (Variable "x"))
-- \x. \y. x
_false = Lambda "x" (Lambda "y" (Variable "y"))
-- \x. \y. y
_not = Lambda "t" (Apply (Apply (Variable "t") _false) _true)
-- \t. t false true
_and = Lambda "x" (Lambda "y" (Apply (Apply (Variable "x") (Variable "y")) _false))
-- \x. \y.(x->y|false)
_fst = Lambda "x" (Apply (Variable "x") _true)
-- \x. x true
_snd = Lambda "x" (Apply (Variable "x") _false)
-- \x. x false
_suc = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "n") (Variable "f")) (Apply (Variable "f") (Variable "x")))))
-- \n. \f. \x. n f (f x)
testSuc = last(l_normalitza_n (Apply _suc _2))
--ok
_eszero = Lambda "n" ((Apply (Apply (Variable "n") (Lambda "x" _false)) _true))
-- \n. n (\x. false) true
parentesisPrefn = Apply (Apply (Apply _fst (Variable "p")) (Apply _snd (Variable "p"))) (Apply (Variable "f") (Apply _snd (Variable "p")))
-- (fst p -> snd p | f(snd p))
-- <e1, e2> = \p. ((p e1) e2)
-- < false , (fst p -> snd p | f(snd p)) >
parella = Lambda "x" (Apply (Apply (Variable "x") _false) parentesisPrefn)
_prefn = Lambda "f" (Lambda "p" parella)
-- \f. \p. < false , (fst p -> snd p | f(snd p)) >
parellaPrec = Lambda "p" (Apply (Apply (Variable "p") _true) (Variable "x"))
-- \n. \f. \x. snd (n (prefn f) <true,x>)
_prec = Lambda "n" (Lambda "f" (Lambda "x" (Apply _snd (Apply (Apply (Variable "n") (Apply _prefn (Variable "f"))) parellaPrec))))
testPrec = last(l_normalitza_n (Apply _prec _2))
testPrec3 = last(l_normalitza_n (Apply _prec _4))
termeTestPrefn = Apply (Variable "f") (Lambda "p" (Apply (Apply (Variable "p") _true) (Variable "z")))
testPrefn = last(l_normalitza_n (Apply _prefn termeTestPrefn))
mitg_t = Lambda "x" (Lambda "y" (Apply (Variable "y") (Apply (Apply (Variable "x") (Variable "x")) (Variable "y")) ))
-- (\x.(\y. y(x x y)))
_t = Apply mitg_t mitg_t
-- ((\x.(\y. y(x x y))) (\x.(\y. y(x x y))))
_prod = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Apply (Variable "n") (Variable "f"))) (Variable "x")))))
testProd = last(l_normalitza_n (Apply (Apply _prod _2) _4))
parentesisFact = Apply (Apply (Apply _eszero (Variable "n")) _1) (Apply (Apply _prod (Variable "n")) (Apply (Variable "f") (Apply _prec (Variable "n"))))
_fact = Apply _t (Lambda "f" (Lambda "n" parentesisFact))

--test
testFactorial_1 = l_normalitza_n (Apply _fact _1)
testFactorial_2 = last(l_normalitza_n (Apply _fact _2))
_test4 = l_normalitza_n (Apply (Apply _prod _2) _2)

testFactorial_4 = last(l_normalitza_n (Apply _fact _4))

-- DE BRUYNE
data LTdB =
    V Int
  | L LTdB
  | A LTdB LTdB

instance Show LTdB where
  show (V x) = show x
  show (L y) = "(/. " ++ show y ++ ")"
  show (A x y) = "("++ show x ++ " " ++ show y ++ ")"

type Context = [(String,Int)]
-- parelles nom lambda LTa i distancia
-- si no hi es s'afegeix 1 a la distancia mes gran delc context

buscarVarContext :: (Num b, Eq t) => t -> [(t, b)] -> (Bool, b)
buscarVarContext v [] = (False,0)
buscarVarContext v (x:xs) = if(fst x == v) then (True,snd x) else buscarVarContext v xs

buscarNum :: Eq t => t -> [(a, t)] -> Maybe (a, t)
buscarNum v [] = Nothing
buscarNum v (x:xs) = if(snd x == v) then Just x else buscarNum v xs

buscarMesGran :: Ord t => [(a, t)] -> t -> t
buscarMesGran [] m = m
buscarMesGran (x:xs) m = if(snd x>m)then buscarMesGran xs (snd x) else buscarMesGran xs m

afegirContext :: Eq a => (a, b) -> [(a, b)] -> [(a, b)]
afegirContext p [] = [p]
afegirContext p (x:xs) = if(fst p /= fst x) then x : (afegirContext p xs) else (x:xs)

increment :: Num a => a -> a
increment x = x +1 

afegirContextShiftant :: (Num b, Eq a) => (a, b) -> [(a, b)] -> [(a, b)]
afegirContextShiftant p [] = [p]
afegirContextShiftant p (x:xs) = (fst x,increment (snd x)) : (afegirContext p xs)

test_afegirContextShiftant = afegirContextShiftant ("x",0) [("y",1)]
test_buscarVarContext = buscarVarContext "y" test_afegirContextShiftant
test_afegirContext = afegirContext ("x",0) [("z",1)]
test_buscarMesGran = buscarMesGran test_afegirContext 0

--s'ha de fer aplicatiu primer aplicacions sense tenir en compte fora,
-- llavors el lambda LTa shifta lo de dins seu
a_deBruijn :: LT -> Context -> LTdB
a_deBruijn (Variable x) c = if (fst p) then (V (snd p)) else if((buscarMesGran c 0) ==0) then(V 1) else (V ((buscarMesGran c 0)+1)) 
  where
    p = buscarVarContext x c
--si hi ha variables afegim al context a l'altre costat
a_deBruijn (Apply (Variable x) y) c = 
  (A 
    (a_deBruijn (Variable x) c) 
    (a_deBruijn y (afegirContext (x,(buscarMesGran c 1)+1) c))
 )
a_deBruijn (Apply y (Variable x)) c = 
  (A 
    (a_deBruijn y (afegirContext (x,(buscarMesGran c 1)+1) c)) 
    (a_deBruijn (Variable x) c) 
 )
a_deBruijn (Apply x y) c = A (a_deBruijn x c) (a_deBruijn y c)
--Afegim context el lambda a distancia 0 i sumem 1 a tots els altres i apliquem el mateix
a_deBruijn (Lambda x y) c = L(a_deBruijn y (afegirContextShiftant (x,0) c))


-- \o. o \z. x y z -> \. 0 \.  1 2 0
testBruijn_1 :: LTdB
testBruijn_1 = a_deBruijn  (Lambda "o" (Apply (Variable "o") (Lambda "z" (Apply (Apply (Variable "x") (Variable "y")) (Variable "z"))))) []

-- \x. \y. z m y x -> \. \. 2 3 0 1
testBruijn_2 = a_deBruijn (Lambda "x" (Lambda "y" (Apply (Apply (Apply (Variable "z") (Variable "m")) (Variable "y")) (Variable "x")))) []

testBruijn_3 = a_deBruijn (Apply (Lambda "x" (Variable "x")) (Lambda "x" (Variable "x"))) []

lletres = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"] --tamany 25

afegirBarraBaixa :: (Eq t, Num t) => t -> [Char]
afegirBarraBaixa 0 = ""
afegirBarraBaixa x = "_"++afegirBarraBaixa (x-1)

novaVariable :: (Num t, Eq t) => t -> Int -> [Char]
novaVariable x y = if(y>25)then novaVariable (x+1) (y-25) else afegirBarraBaixa x ++ lletres!!y

de_deBruijn :: LTdB -> Context -> LT
--variable sola
de_deBruijn (V n) c = case p of                           
    Nothing -> (Variable (novaVariable 0 ((length c)))) --buscar nova variable
    Just (a,b) -> (Variable a)
  where
    p = buscarNum n c

--variable al costat esquerra
de_deBruijn (A (V n) y) c = case p of                           
  Nothing -> Apply (Variable variable)  (de_deBruijn y (afegirContext (variable,0) c)) --buscar nova variable
  Just (a,b) -> Apply (Variable a) (de_deBruijn y c)
  where
  p = buscarNum n c
  variable = novaVariable 0 ((length c))

--variable al costat dret
de_deBruijn (A y (V n)) c = case p of                           
  Nothing -> Apply (de_deBruijn y (afegirContext (variable,0) c)) (Variable variable) --buscar nova variable
  Just (a,b) -> Apply (de_deBruijn y c) (Variable a)
  where
  p = buscarNum n c
  variable = novaVariable 0 ((length c))

--lambda abstraccio
de_deBruijn (L x) c= (Lambda variable (de_deBruijn x (afegirContextShiftant (variable,0) c))) --afegir nova variable i afegirla al context a distancia 0
  where
    variable = novaVariable 0 ((length c))

--altres aplicacions
de_deBruijn (A x y) c = Apply (de_deBruijn x c) (de_deBruijn y c)

--test Anterior
-- \o. o \z. x y z -> \. 0 \.  1 2 0
-- testBruijn_1 :: LTdB
-- testBruijn_1 = a_deBruijn  (Lambda "o" (Apply (Variable "o") (Lambda "z" (Apply (Apply (Variable "x") (Variable "y")) (Variable "z"))))) []
testDe_DeBrujin_1 = de_deBruijn testBruijn_1 []

--altre test Anterior
-- \x. \y. z m y x -> \. \. 2 3 0 1
-- testBruijn_2 = a_deBruijn (Lambda "x" (Lambda "y" (Apply (Apply (Apply (Variable "z") (Variable "m")) (Variable "y")) (Variable "x")))) []

testDe_DeBrujin_2 = de_deBruijn testBruijn_2 []

instance Eq LTdB where
  V x == V y = x == y
  L x == L y = x == y
  A x y == A m n = x == m && y == n
  _ == _ = False

instance Eq LT where
  x == y = (a_deBruijn x []) == (a_deBruijn y [])


buscarNumMesGran :: LTdB -> Int -> Int
buscarNumMesGran (V x) mesGran = if(x>mesGran) then x else mesGran
buscarNumMesGran (L x) mesGran = buscarNumMesGran x mesGran
buscarNumMesGran (A x y) mesGran = if(mesGranX > mesGranY) then mesGranX else mesGranY
    where 
      mesGranX = buscarNumMesGran x mesGran
      mesGranY = buscarNumMesGran y mesGran

instance Ord LT where
  x <= y = (buscarNumMesGran (a_deBruijn x []) 0) <= (buscarNumMesGran (a_deBruijn y []) 0)

-- \x. y x == \y. z y
testAlphaEqual_1 = Lambda "x" (Lambda "y" (Variable "x")) == Lambda "y" (Lambda "z" (Variable "y"))

testAlphaEqual_2 = Lambda "x" (Lambda "y" (Variable "x")) == Lambda "y" (Lambda "z" (Variable "x"))

testAlphaEqual_3 = (Lambda "o" (Apply (Variable "o") (Lambda "z" (Apply (Apply (Variable "x") (Variable "y")) (Variable "z"))))) == (Lambda "o" (Apply (Variable "o") (Lambda "q" (Apply (Apply (Variable "x") (Variable "y")) (Variable "q")))))
