
module MultiArmedBanditTree (runWithHistory, BanditProblem(..), initTree, bestNode, BanditTree(..), findBest, twinPeaks) where
import Data.List
import Control.Monad.IO.Class
import System.Random
import Data.Maybe
import Text.Printf
import Text.PrettyPrint.HughesPJ
--import Graphics.Rendering.Chart.Simple
import GHC.Float

--------- This section is a utility for maintaining empirical mean and variance estimates without keeping all scores.
-- |Sufficient information to calculate online mean and variance, see
-- |Donald E. Knuth (1998). The Art of Computer Programming, volume 2: Seminumerical Algorithms, 3rd edn., p. 232. Boston: Addison-Wesley.
data Stats = OnlineMeanAndVariance {
     mvN :: !Integer,   -- number of samples so far
     mvX,              -- current mean
     mvM2 :: !Float     -- extra information for variance
}

instance Show Stats where
  show st = printf "#=%d mean=%f var=%f" (entries st) (mean st) (variance st)

-- |Stats for the empty sequence.
emptyStats = OnlineMeanAndVariance {mvN = 0, mvX = 0, mvM2 = 0}

singletonStat val = emptyStats `withEntry` val

-- |Add a number to the sequence over which we maintain statistics.
withEntry :: Stats -> Float -> Stats
withEntry (OnlineMeanAndVariance {mvN = n, mvX = x, mvM2 = m2}) xNew =
       OnlineMeanAndVariance {mvN = n + 1,
                              mvX = newMean,
                              mvM2 = m2 + delta * (xNew - newMean) }
          where
                delta = xNew - x
                newMean = x + delta / fromInteger (n + 1)

summarize :: [Float] -> Stats
summarize = foldr (flip withEntry) emptyStats

-- |Number of entries in sequence
entries OnlineMeanAndVariance {mvN = n} = n
-- |Mean of entries
mean OnlineMeanAndVariance {mvX = r} = r
-- |Variance of entries
variance OnlineMeanAndVariance {mvN = n, mvX = r, mvM2 = m2} = m2 / fromInteger n
------- Utility section ends here

-- | Each bandit is characterized by its statistical properties of its scores (number, mean and variance), and by some opaque identity a seen only by the environment.
data UCBBandits a = Bandits [(Stats, a)] deriving Show



-----------------------  Generic code ---------------------------
-- | Each bandit in a tree also keeps a list of nodes for visited reachable ids, and a list of ids to be visited. Note that here the Stats of a node include also visits to its children. 
data BanditTree a
  = BanditNode { bnStats :: Stats             -- Score at his node
               , bnOwnPayoff :: Float
               , bnId :: [a]                   -- Game state at this node
               , bnSons :: [BanditTree a]
               , bnUnvisitedSons :: [[a]] }

instance Show a => Show (BanditTree a) where
  show bt = show $ prettyBanditTree bt

prettyBanditTree (BanditNode bnStats bnOwnPayoff bnId bnSons bnUS)
  = own $$ (nest 2 $ vcat $ reverse sons)
    where
       own = text $ show (bnStats, bnOwnPayoff, bnId)
       sons = map prettyBanditTree bnSons


-- | bpPlayAction represents the environment (which gives rewards and
-- next-actions). A deterministic environment is referentially transparent.
data BanditProblem m a = BanditProblem { bpPlayAction   :: a -> m (Float, [[a]])
                                       , bpRoot     :: [a]
                                       , bpIsDeterministic :: Bool }

--bestNode :: BanditProblem m a -> BanditTree m a -> BanditTree m a
bestNode bp
         t@(BanditNode {bnSons = []}) = t
bestNode bp@(BanditProblem {bpIsDeterministic = isDet})
         t@(BanditNode     {bnSons = sons})
  = let measure = if isDet
                       then bnOwnPayoff
                       else (mean . bnStats)
        (best, rest) = maximalAndRestBy measure $ map (bestNode bp) sons
    in best



-- | selfVisitStats, #totalArms, #totalVisits, errorProbability -> upper confidence bound. See:
-- | Audibert, Munos and Szepesvari (2006). Use of variance estimation in the multi-armed bandit problem.
ucbBeta :: Stats -> Integer -> Float -> Float -> Float
ucbBeta stats _ _ _ | entries stats == 0 = 1/0
ucbBeta stats arms beta scale = empMean + confidenceSlow + confidenceFast
         where empMean = mean stats
               confidenceSlow = sqrt (2 * (variance stats) * logPart / visit)
               confidenceFast = 16 * scale * logPart / 3 / visit
               visit = fromInteger $ entries stats
               logPart = log $ 1 / betaS
               betaS = beta / 4.0 / fromInteger arms / visit / (visit + fromInteger 1)

maximalAndRestBy :: (Ord b) => (a -> b) -> [a] -> (a, [a])
maximalAndRestBy f [] = error "empty list has no maximal element"
maximalAndRestBy f (x:[]) = (x, [])
maximalAndRestBy f (x:x':xs) =
    let rest = x':xs
        (largestInSuffix, restFromSuffix) = maximalAndRestBy f rest
    in case (f x) >= (f largestInSuffix) of
         True -> (x,rest)
         False -> (largestInSuffix, x:restFromSuffix)


-- |Choose an arm that maximizes ucbBeta (appropriate to play according to the UCB algorithm)
chosenAndRest bandits toStats beta scale =
          let arms = toInteger $ length bandits
              currUCB b = ucbBeta (toStats b) arms beta scale
              maxUCB = maximum $ map currUCB bandits
          in maximalAndRestBy currUCB bandits

{-
-- |Play the UCB algorithm with a given history and problem, returning the updated history.
play :: Monad m => UCBBandits a -> BanditProblem m a -> Float -> m (UCBBandits a)
play (Bandits bandits) problem beta =
     let
          BanditProblem {bpPlayAction = playAction} = problem
          ((chosenStats, chosenIdentity), otherArms) = chosenAndRest bandits (\(s,i) -> s) beta 1
     in do
          (newScore, _) <- playAction chosenIdentity -- UCB does not deal with recursive structure.
          let updatedArm = (chosenStats `withEntry` newScore, chosenIdentity)
          return (Bandits (updatedArm : otherArms))
-}
initTree :: BanditProblem m a -> m (Maybe [a], Float, BanditTree a)
initTree = undefined
{-initTree (BanditProblem playAction rootId _)
  = do (score, actions) <- playAction rootId
       return (Just rootId, score
              , BanditNode { bnStats = emptyStats `withEntry` score
                           , bnOwnPayoff = score
                           , bnId = rootId
                           , bnSons = []
                           , bnUnvisitedSons = actions})
-}
data ActionNovelty = NewAction | SonFreeVisited Integer Float


chooseActions :: BanditProblem m a -> Integer -> BanditTree a -> Float -> Float -> (ActionNovelty, [a])
chooseActions (BanditProblem playAction _ _) decisionBudget (BanditNode stats ownPayoff id sons (xunvisited : xs)) beta scale
   | fromInteger (toInteger (length sons)) <= max 1 (0.02 * (sqrt $ fromInteger (entries stats)))
   = (NewAction, xunvisited)

chooseActions problem decisionBudget (BanditNode stats ownPayoff id sons unvisited) beta scale
  | not (null sons)   -- We need at least one son
  = let uStats = (if decisionBudget <= mvN stats
                   then (withEntry emptyStats) . fromIntegral . mvN -- past budget use most visited
                   else \x->x) . bnStats  -- else use full stats
        (chosenSon, otherSons) = chosenAndRest sons uStats beta scale  -- Pick son with
    in chooseActions problem decisionBudget chosenSon beta scale


chooseActions (BanditProblem playAction _ isDet) decisionBudget (BanditNode stats ownPayoff id [] []) beta scale = (SonFreeVisited (mvN stats) ownPayoff, id)

chooseActions _ _ _ _ _ = error "Logic error in chooseActions: should not arrive here."

data Decision a = Decision {dPayoff :: Float, dActions :: Maybe [[a]]}

interactWithProblem :: BanditProblem m a -> a -> ActionNovelty -> m (Decision a)
interactWithProblem (BanditProblem {bpIsDeterministic = True})
                    _
                    (SonFreeVisited vis payoff)
  = return $ Decision payoff Nothing

interactWithProblem (BanditProblem {bpPlayAction = playAction
                                   , bpIsDeterministic = True})
                    action
                    _
  = do (payoff, actions) <- playAction action
       return $ Decision payoff $ Just actions

-- Possibilities:
--   the action list describes the path to a node that exists (therefore runs out at a node).
--   the action list describes the path to a node that needs to be created (therefore is a singleton at a node, and we must receive a list of its unvisited actions).
--   we are not there yet; the first element in the list identifies where to proceed.

updateTree :: BanditTree a -> [a] -> ActionNovelty -> Decision a -> Int -> BanditTree a

updateTree old [] _ decision _
  = old { bnStats = bnStats old `withEntry` dPayoff decision
        , bnUnvisitedSons = fromMaybe [] $ dActions decision }

-- Unchecked invariant: here act should be equal to first
updateTree old@BanditNode { bnUnvisitedSons = first : rest}
           [act]
           _
           (Decision payoff (Just actions))
           _
  = let newNode = BanditNode { bnStats = singletonStat $ payoff
                             , bnOwnPayoff = payoff
                             , bnId = bnId old ++ [act]
                             , bnSons = []
                             , bnUnvisitedSons = actions }
    in old { bnStats = (bnStats old) `withEntry` payoff
           , bnSons = newNode : bnSons old
           , bnUnvisitedSons = rest }

updateTree old actionList@(next:after:rest) an d depth
  = let suffix = after:rest
        (wrong, toUpdate:wrongAfter) = break (\s -> suffix == (drop depth $ bnId s)) $ bnSons old
        updatedSon = updateTree toUpdate suffix an d $ depth - 1
    in old { bnStats = (bnStats old) `withEntry` (dPayoff d)
           , bnSons = toUpdate : (wrong ++ wrongAfter)}

updateTree _ _ _ _ _ = error "logic error in updateTree, shouldn't get here."





playFromTree :: Monad m => BanditProblem m a -> Integer -> BanditTree m a -> Float -> Float
                        -> m (Maybe a, Float, BanditTree m a)
-- A single iteration of main loop: 
-- Returns (state after chosen move, its payoff, updated tree)

-- First possibility: if we have unvisited nodes, and
-- the visited nodes have had sufficient attention, get a new node.
playFromTree (BanditProblem playAction _ _) decisionBudget (BanditNode stats ownPayoff id sons (xunvisited : xs)) beta scale
   | fromInteger (toInteger (length sons)) <= max 1 (0.02 * (sqrt $ fromInteger (entries stats)))
   = do let newState = xunvisited
        (newScore, newUnvisited) <- playAction newState
        let newStats = emptyStats `withEntry` newScore
        let newNode = BanditNode newStats newScore newState [] newUnvisited
        let updatedStats = (stats `withEntry` newScore)
        return (Just newState, newScore, (BanditNode updatedStats ownPayoff id (newNode:sons) xs))

-- Second possiblity: go down an already-visited son
-- If there are no unvisited nodes, and there is at
-- least one visited son: visit a visited son.  If attention to
-- visited hasn't been sufficient, and there is at least one visited
-- son: visit a visited son.
playFromTree problem decisionBudget (BanditNode stats ownPayoff id sons unvisited) beta scale
  | not (null sons)   -- We need at least one son
  = let uStats = (if decisionBudget <= mvN stats
                   then (withEntry emptyStats) . fromIntegral . mvN -- past budget use most visited
                   else \x->x) . bnStats  -- else use full stats
        (chosenSon, otherSons) = chosenAndRest sons uStats beta scale  -- Pick son with highest upper bound
    in do (actionM, newScore, updatedSon) <- playFromTree problem decisionBudget chosenSon beta scale
          let updatedStats = stats `withEntry` newScore
          return (actionM, newScore, BanditNode updatedStats ownPayoff id (updatedSon : otherSons) unvisited)

-- Third possibility: if we arrive here, there are no visited sons, and in particular, no
-- attention deficit, therefore there are no unvisited sons left. So
-- we can only play the current node. When feedback is deterministic,
-- this is wasteful. When environment is random, we might grow more
-- possible actions.
playFromTree (BanditProblem playAction _ isDet) decisionBudget (BanditNode stats ownPayoff id [] []) beta scale =
     do (newScore, nextActions) <- if isDet
          then return (ownPayoff, [])
          else playAction id
        let actionM = if isDet then Nothing else Just id
        let updatedStats = (stats `withEntry` newScore)
        return (actionM, newScore, BanditNode updatedStats ownPayoff id [] nextActions)

playFromTree _ _ _ _ _ = error "Logic error in playFromTree: should not arrive here."

---------------------- Problem 1: bigger is better --------------------
-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
bibHelper m n = case m of
               0 -> [(fromInteger $ toInteger m) | m <- [1..n]]
               _ -> []

biggerIsBetter :: Int -> BanditProblem IO Float
biggerIsBetter n = BanditProblem { bpPlayAction = \i -> return (i, bibHelper i n)
                                 , bpRoot = 0
                                 , bpIsDeterministic = True}

---------------------- Problem 2: twinPeaks --------------------
-- | A simple non concave problem testing UCT
-- An infinitely-branching tree of possiblities
{-twinPeaks :: BanditProblem IO Float
twinPeaks = BanditProblem { bpPlayAction = twinHelper
                          , bpRoot = []
                          , bpIsDeterministic = False}

twinHelper :: [Float] -> IO (Float, [Float])
twinHelper [x] = do let payoff = - (min (abs (x+1)) (abs (x-1)))
                    actions <- randomList x
                    return (payoff, map (\x -> [x]) actions)
-}
randomList x = mapM randomRIO $ replicate 5 (x-0.1,x+0.1)

-- | f (f (f ... (f a) running f n times. Like unfold, without creating the list.
iterationResult :: (Num a, Ord a) => a -> (t -> t) -> t -> t
iterationResult n f a | n <= 0 = a
                      | otherwise = iterationResult (n - 1) f (f a)

-- problem = twinPeaks

simulationStep (i, _, _, _, _, _, _)  | i == 0 = return Nothing
simulationStep hextuple =
        let (i, bt, problem, playBudget, beta, minScore, maxScore) = hextuple
        in do (a, s, nbs) <- playFromTree problem playBudget bt beta $ max 1 (maxScore - minScore)
              let miS = min minScore s
                  maS = max maxScore s
              return (Just ((a,s,nbs), (i-1, nbs, problem, playBudget, beta, miS, maS)))

-- Ended up equivalent to unfoldrM from Control.Monad.Loops in monad-loops, but that's not standard issue.
unfoldrMine      :: Monad m => (tb -> m (Maybe (ta, tb))) -> tb -> m [ta]
unfoldrMine f b  = do
  x <- f b 
  case x of
   Just (a,new_b) -> do rest <- unfoldrMine f new_b
			return (a : rest)
   Nothing        -> return []

runWithHistory n beta problem playBudget startState = unfoldrMine simulationStep (n, startState, problem, playBudget, beta, 0, 0)

-- main = findBest 10 10 twinPeaks Nothing

findBest budget beta problem playBudgetM =
    do initRes <- initTree problem -- Uses 1 run from the budget
       let (_, _, startbt) = initRes
       allResults <- runWithHistory (budget - 1) beta problem (fromMaybe (ceiling budget) playBudgetM) startbt
       let tree = head $ reverse $ [c | (a,b,c) <- initRes : allResults]
       putStrLn $ show tree
       return $ bnId $ bestNode problem tree
