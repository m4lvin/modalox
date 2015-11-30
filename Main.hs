module Main where

import SAT
import Modalox
import qualified Data.Map as M

--------------------------------------------------------------------------------

proveModal :: (Show a, Ord a, Show m, Ord m) =>
              (String->IO()) -> Form m a -> IO Bool
proveModal say p =
  do -- create SAT-solver
     s <- newSolver
  
     -- rename atoms in formula as SAT-atoms
     say "-- litifying formula --"
     (p',mp) <- litify s p M.empty
     sequence_ [ say (show x ++ " = " ++ show a) | (a,x) <- M.toList mp ]

     -- import formula into SAT-solver
     say "-- clausifying formula --"
     (x,boxs,dias) <- run s say (define False True p')
     say "-- modalities --"
     sequence_ [ say (show a ++ " -> [" ++ show m ++ "]" ++ show b) | (a,m,b) <- boxs ]
     sequence_ [ say (show a ++ " -> <" ++ show m ++ ">" ++ show b) | (a,m,b) <- dias ]
     say "-- top-level name --"
     say (show x)
     
     -- run prove on the formula
     say "-- proving --"
     res <- prove s say [] boxs dias [neg x]
     deleteSolver s
     case res of
       Left _  -> do say "== COUNTERSATISFIABLE =="
                     return False
       Right _ -> do say "== THEOREM =="
                     return True

--------------------------------------------------------------------------------

main :: IO ()
main = print =<< proveModal putStrLn muddy

--------------------------------------------------------------------------------

simple =
  box alice a .->. box alice a

canReason =
  (box alice a .&. box alice (a .->. b)) .->. box alice b

transitive =
  box alice a .->. box alice (box alice a)

serial =
  box alice a .->. dia alice a

euclidean =
  dia alice a .->. box alice (dia alice a)

bar2 =
    ( box alice a
  .&. box common ( whether alice a
               .&. whether bob b
               .&. nt (whether bob (a .&. b))
                 )
    ) .->. 
      box alice (a .&. b)

muddy :: Form [Char] [Char]
muddy =
   ( box common ( (a .|. b .|. c)
              .&. whether alice   b
              .&. whether alice   c
              .&. whether bob     a
              .&. whether bob     c
              .&. whether charlie a
              .&. whether charlie b
              .&. nt (box bob b)
              .&. nt (box charlie c)
                )
   ) .->.
     box alice a

nMuddy :: Int -> Form [Char] [Char]
nMuddy n =
  let
    atom    = (Atom).show
    atoms   = map atom [1..n]
    agent k = ("Agent" ++ show k) :@ [Reflexive,Transitive]
    agents  = map agent [1..n]
    nGroup  = foldl1 (:&&:) agents
    nCommon = Star nGroup
    seeOthers k = foldl1 (.&.) [ whether (agent k) (atom j) | j<-[1..n], j /= k ]
    dontKnowSelf k = nt (box (agent k) (atom k))
  in
   ( box nCommon ( ( foldl1 (.|.) atoms )
              .&. (foldl1 (.&.) (map seeOthers [1..n]))
              .&. (foldl1 (.&.) (map dontKnowSelf [2..n]))
                )
   ) .->.
     box (agent 1) (atom 1)

{-
  n | seconds
----|---------
  3 |    0.03
  4 |    0.03
  5 |    0.05
  6 |    0.11
  7 |    0.23
  8 |    0.55
  9 |    1.41
 10 |    3.88
 11 |   12.25
 12 |   22.97
 13 |   75.03
-}

bad =
  box common a .->. box common a -- crashes

--------------------------------------------------------------------------------

a = Atom "a"
b = Atom "b"
c = Atom "c"

alice   = "Alice"   :@ [Reflexive,Transitive]
bob     = "Bob"     :@ [Reflexive,Transitive]
charlie = "Charlie" :@ [Reflexive,Transitive]

group  = alice :&&: bob :&&: charlie
common = Star group

whether m p = box m p .|. box m (nt p)

--------------------------------------------------------------------------------

