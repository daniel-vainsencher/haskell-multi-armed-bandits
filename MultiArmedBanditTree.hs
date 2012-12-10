
module MultiArmedBanditTree (runWithHistory, BanditProblem(..), initTree, bestNode, BanditTree(..), findBest, twinPeaks, ActionSpec(..), addAction, justActions, BanditFeedback(..)) where
import Data.List
import Control.Monad.IO.Class
import Control.Monad.Loops
import System.Random
import Data.Maybe
import Text.Printf
import Text.PrettyPrint.HughesPJ
--import Graphics.Rendering.Chart.Simple
import GHC.Float
import CoreMonad hiding (liftIO)
import SimplMonad
import System.IO

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
               , bnSubtrees :: [BanditTree a]
               , bnSons :: [BanditTree a]
               , bnUnvisitedSons :: [[a]] }

instance Show a => Show (BanditTree a) where
  show bt = show $ prettyBanditTree bt

data BanditFeedback a
     = BanditFeedback { fbSubproblemFeedbacks :: [BanditFeedback a]
                      , fbPayoff :: Float
                      , fbActions :: [[a]]}
       | BanditSubFeedback { fbSubproblemFeedbacks :: [BanditFeedback a]
                         , fbActionTaken :: a
                         , fbNext :: BanditFeedback a}
       deriving Show

mkActionSpec (a:as) = ActionSpec {asAction = a, asNext = (mkActionSpec as), asSubproblems = []}
mkActionSpec [] = ActionSeqEnd

addAction ActionSeqEnd a = ActionSpec {asAction = a, asNext = ActionSeqEnd, asSubproblems = []}
addAction (ActionSpec {asAction = a, asNext = rest}) an
          = let new = addAction rest an
            in ActionSpec {asAction = a, asNext = new, asSubproblems = []}

justActions :: ActionSpec a -> [a]
justActions (ActionSpec {asAction = a, asNext = n}) = a : justActions n
justActions ActionSeqEnd = []

prettyBanditTree (BanditNode { bnStats = stats
                             , bnOwnPayoff = ownPayoff
                             , bnId = id
                             , bnSons = sons
                             , bnUnvisitedSons = unvisited
                             , bnSubtrees = []})
  = ownDoc $$ unvisDocs $$ (nest 2 $ vcat $ reverse sonsDocs)
    where
       ownDoc = text $ show (stats, ownPayoff, id)
       sonsDocs = map prettyBanditTree sons
       unvisDocs = hcat $ map (text . show) unvisited


-- | bpPlayAction represents the environment (which gives rewards and
-- next-actions). A deterministic environment is referentially transparent.
data BanditProblem m a = BanditProblem { bpPlayAction   :: ActionSpec a -> m (BanditFeedback a)
                                       , bpRoot     :: ActionSpec a
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

bestActionSpec bp t = mkActionSpec $ bnId $ bestNode bp t

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
initTree :: (MonadIO m, Show a) => BanditProblem m a -> m (ActionSpec a, Float, BanditTree a)
initTree (BanditProblem playAction rootId _)
  = do BanditFeedback {fbPayoff = score, fbSubproblemFeedbacks = subfbs, fbActions = actions} <- playAction rootId
       liftIO $ putStrLn $ "Init action got score and further actions:" ++ show (score, actions)
       return (rootId, score
              , BanditNode { bnStats = emptyStats `withEntry` score
                           , bnOwnPayoff = score
                           , bnId = justActions rootId
                           , bnSubtrees = map treeMaker subfbs
                           , bnSons = []
                           , bnUnvisitedSons = actions})

data ActionNovelty = NewAction | SonFreeVisited Integer Float deriving Show


chooseActions :: BanditProblem m a -> Integer -> BanditTree a -> Float -> Float -> (ActionNovelty, ActionSpec a)
chooseActions (BanditProblem playAction _ _) decisionBudget (BanditNode stats ownPayoff id subtrees sons (xunvisited : xs)) beta scale
   | fromInteger (toInteger (length sons)) <= max 1 (0.02 * (sqrt $ fromInteger (entries stats)))
   = (NewAction, mkActionSpec xunvisited)

chooseActions problem decisionBudget (BanditNode { bnStats = stats
                                                 , bnOwnPayoff = ownPayoff
                                                 , bnId = id
                                                 , bnSons = sons
                                                 , bnUnvisitedSons = unvisited
                                                 , bnSubtrees = []}) 
              beta scale
  | not (null sons)   -- We need at least one son
  = let uStats = (if decisionBudget <= mvN stats
                   then (withEntry emptyStats) . fromIntegral . mvN -- past budget use most visited
                   else \x->x) . bnStats  -- else use full stats
        (chosenSon, otherSons) = chosenAndRest sons uStats beta scale  -- Pick son with
    in chooseActions problem decisionBudget chosenSon beta scale


chooseActions (BanditProblem playAction _ isDet) 
              decisionBudget 
              (BanditNode { bnStats = stats
                          , bnOwnPayoff = ownPayoff
                          , bnId = id
                          , bnSons = []
                          , bnUnvisitedSons = []
                          , bnSubtrees = []}) 
              beta scale = (SonFreeVisited (mvN stats) ownPayoff, mkActionSpec id)

chooseActions _ _ _ _ _ = error "Logic error in chooseActions: should not arrive here."

data Decision a = Decision {dPayoff :: Float, dActions :: Maybe [[a]]} deriving Show

interactWithProblem :: Monad m => BanditProblem m a -> ActionSpec a -> ActionNovelty -> m (Decision a)
interactWithProblem (BanditProblem {bpIsDeterministic = True})
                    _
                    (SonFreeVisited vis payoff)
  = return $ Decision payoff Nothing

interactWithProblem (BanditProblem {bpPlayAction = playAction
                                   , bpIsDeterministic = True})
                    action
                    _
  = do BanditFeedback {fbPayoff = payoff, fbSubproblemFeedbacks = subfb, fbActions = actions} <- playAction action
       return $ Decision payoff $ Just actions


updateTrees :: (Show a, Eq a) => [BanditTree a] -> [BanditFeedback a] -> [BanditTree a]
updateTrees bts bfs 
  = if length bts /= length bfs 
       then error "Subproblem list length inconsistent between feedback and tree." 
       else let (_, trees) = unzip [updateTree2 t fb 0 | (t, fb) <- zip bts bfs]
	    in trees

treeMaker bf
  = BanditNode { bnStats = singletonStat $ fbPayoff bf
	       , bnOwnPayoff = fbPayoff bf
	       , bnId = []
	       , bnSubtrees = map treeMaker $ fbSubproblemFeedbacks bf
	       , bnSons = []
	       , bnUnvisitedSons = fbActions bf} 

updateTree2 :: (Show a, Eq a) => BanditTree a -> BanditFeedback a -> Int -> (Float, BanditTree a)
-- If the BF carries a payoff, action occured in current existing BT node. Cannot be that we have sons (visited or otherwise), or feedback would be in one of them.
updateTree2 old@BanditNode {bnSons = [], bnUnvisitedSons = []} bf@BanditFeedback {} depth
  = let po = fbPayoff bf
    in (po
       , old { bnStats = bnStats old `withEntry` fbPayoff bf
	     , bnOwnPayoff = po
	     , bnSubtrees = updateTrees (bnSubtrees old) $ fbSubproblemFeedbacks bf
	     , bnUnvisitedSons = fbActions bf})

-- If actionTaken on BSF matches the next unvisited son, its successor must be a BF; create a son. Relies on unvisited sons being visited in a constant order. Subproblems need to be created; since we just found them the initial feedback is assumed a BF.
updateTree2 old@BanditNode {bnUnvisitedSons = ua:uas} bsf@BanditSubFeedback {fbActionTaken = act, fbNext = BanditFeedback {}} depth
  = let bf = fbNext bsf 
	po = fbPayoff $ bf
	freshSon = (treeMaker bf) { bnId = bnId old ++ [fbActionTaken bsf] }
	newNode = old { bnStats = (bnStats old) `withEntry` po
		      , bnSons = freshSon : bnSons old
		      , bnSubtrees = updateTrees (bnSubtrees old) 
						 $ fbSubproblemFeedbacks bsf
		      , bnUnvisitedSons = uas}
    in (po, newNode)

-- If actionTaken on BSF matches an existing son, continue into it.
updateTree2 old bsf@BanditSubFeedback {} depth
  = let (wrong, sonToUpdate:wrongAfter) = break (\s -> fbActionTaken bsf == head (drop depth $ bnId s)) $ bnSons old
	(po, freshSon) = updateTree2 sonToUpdate (fbNext bsf) $ depth + 1
	newNode = old { bnStats = (bnStats old) `withEntry` po
		      , bnSons = freshSon : (wrong ++ wrongAfter)
		      , bnSubtrees = updateTrees (bnSubtrees old) (fbSubproblemFeedbacks bsf)}
    in (po, newNode)

-- Other options should not happen.
updateTree2 node feedback depth = error $ "Should not get here. " ++ show node ++ show feedback ++ show depth

{-playFromTreeStaged :: (Monad m, Eq a) => BanditProblem m a -> Integer -> BanditTree a
                      -> Float -> Float
                      -> m (Maybe [a], Float, BanditTree a)
-}
playFromTreeStaged problem decisionBudget node beta scale
  = do let (novelty, tape) = chooseActions problem decisionBudget node beta scale
       putStrLn $ "Got tape: " ++ show tape
       feedback <- bpPlayAction problem tape
       putStrLn $ "Going to update " ++ show node ++ " with feedback " ++ show feedback
       let (payoff, newTree) = updateTree2 node feedback 0
       putStrLn $ "Updated tree:" ++ show newTree
       return (tape, payoff, newTree)


---------------------- Problem 1: bigger is better --------------------
-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
bibPlayAction :: Monad m => Int -> ActionSpec Float -> m (BanditFeedback Float)
bibPlayAction n m
  = do return $ case justActions m of
        [] ->  BanditFeedback { fbPayoff = 0
                             , fbActions = [ [fromInteger $ toInteger m] | m <- [1..n]]
                             , fbSubproblemFeedbacks = []}

        [i] -> BanditFeedback { fbPayoff = i
                              , fbActions = []
                              , fbSubproblemFeedbacks = []}

        _ -> error "bigger is better is a one turn game."

biggerIsBetter :: Int -> BanditProblem IO Float
biggerIsBetter n = BanditProblem { bpPlayAction = bibPlayAction n
                                 , bpRoot = ActionSeqEnd
                                 , bpIsDeterministic = True}

---------------------- Problem 2: twinPeaks --------------------
-- | A simple non concave problem testing UCT
-- An infinitely-branching tree of possiblities
twinPeaks :: BanditProblem IO Float
twinPeaks = BanditProblem { bpPlayAction = twinHelper
                          , bpRoot = ActionSeqEnd
                          , bpIsDeterministic = False}

twinHelper :: ActionSpec Float -> IO (BanditFeedback Float)
twinHelper (ActionSpec {asAction = x})
           = do let payoff = - (min (abs (x+1)) (abs (x-1)))
                actions <- randomList x
                return $ BanditFeedback { fbPayoff = payoff 
                                        , fbActions = map (\x -> [x]) actions 
                                        , fbSubproblemFeedbacks = [] }

randomList x = mapM randomRIO $ replicate 5 (x-0.1,x+0.1)

-- problem = twinPeaks

simulationStep (i, _, _, _, _, _, _)  | i == 0 = return Nothing
simulationStep hextuple =
        let (i, bt, problem, playBudget, beta, minScore, maxScore) = hextuple
        in do (a, s, nbs) <- playFromTreeStaged problem playBudget bt beta $ max 1 (maxScore - minScore)
              putStrLn $ show (i, length $ justActions a, s)
              let miS = min minScore s
                  maS = max maxScore s
              return (Just ((a,s,nbs), (i-1, nbs, problem, playBudget, beta, miS, maS)))

-- Ended up equivalent to unfoldrM from Control.Monad.Loops in monad-loops, but that's not standard issue.
-- unfoldrMine      :: (MonadIO m, Show tb, Show ta) => (tb -> m (Maybe (ta, tb))) -> tb -> m [ta]
unfoldrMine f b  = do
  x <- f b 
  case x of
   Just (a,new_b) -> do rest <- unfoldrMine f new_b -- liftIO $ putStrLn $ show a
			return $ a : rest
   Nothing        -> return []

runWithHistory n beta problem playBudget startState = unfoldrMine simulationStep (n, startState, problem, playBudget, beta, 0, 0)

-- main = findBest 10 10 twinPeaks Nothing

findBest budget beta problem playBudgetM =
    do hSetBuffering stdout NoBuffering
       hSetBuffering stderr NoBuffering
       putStrLn $ "Entered findBest with budget, beta: " ++ show (budget, beta)
       initRes <- initTree problem -- Uses 1 run from the budget
       let (_, _, startbt) = initRes
       allResults <- runWithHistory (budget - 1) beta problem (fromMaybe (ceiling budget) playBudgetM) startbt
       let tree = head $ reverse $ [c | (a,b,c) <- initRes : allResults]
       -- putStrLn $ show tree
       return $ bestActionSpec problem tree
