
module MultiArmedBanditTree (BanditProblem(..), findBest, twinPeaks, ActionSpec(..), justActions, BanditFeedback(..)) where
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
	       , bnUCBDecisions :: Integer
               , bnId :: [a]                   -- Game state at this node
               , bnSubtrees :: [BudgetedBanditTree a]
               , bnSons :: [BanditTree a]
               , bnUnvisitedSons :: [[a]] }

data BudgetedBanditTree a 
  = BudgetedBanditTree { bbtPlayBudget :: Integer
		       , bbtNode :: BanditTree a 
		       , bbtMin :: Float
		       , bbtMax :: Float} deriving Show

instance Show a => Show (BanditTree a) where
  show bt = show $ prettyBanditTree bt

data BanditFeedback a
     = BanditFeedback { fbSubproblemFeedbacks :: [BanditFeedback a]
                      , fbPayoff :: Float
                      , fbInclusivePayoff :: Float
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
justActions (ActionSpec {asAction = Just a, asNext = n}) = a : justActions n
justActions _ = []

prettyBanditTree (BanditNode { bnStats = stats
                             , bnOwnPayoff = ownPayoff
                             , bnId = id
                             , bnSons = sons
                             , bnUnvisitedSons = unvisited
                             , bnSubtrees = subtrees})
  = ownDoc $$ unvisDocs $$ (nest 2 $ vcat $ reverse sonsDocs) $$ subDoc
    where
       ownDoc = text $ show (stats, ownPayoff, id)
       sonsDocs = map prettyBanditTree sons
       unvisDocs = hcat $ map (text . show . last) unvisited
       subDoc = nest 2 $ vcat $ map (text . show) subtrees


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
        (bestDescendant, rest) = maximalAndRestBy measure $ map (bestNode bp) sons
    in if measure bestDescendant > measure t then bestDescendant else t

bestActionSpec :: BanditProblem m a -> Int -> BanditTree a -> (Float, ActionSpec a)
bestActionSpec bp depth t@BanditNode { bnId = id
				     , bnSubtrees = subtrees
				     , bnSons = [] }
 = let (subPayoffs, subSpecs) = unzip $ map (bestActionSpec bp 0 . bbtNode) subtrees 
   in (bnOwnPayoff t + sum subPayoffs
      , ActionSpec { asAction = Nothing
		   , asNext = ActionSeqEnd
		   , asSubproblems = subSpecs })

bestActionSpec bp@(BanditProblem {bpIsDeterministic = isDet})
	       depth 
	       t@BanditNode { bnSubtrees = subtrees
			    , bnSons = sons }
 = let (subPayoffs, subSpecs) = unzip $ map (bestActionSpec bp 0 . bbtNode) subtrees
       ((bestSon, (bestSonPayoff, bestSonSpec)) , _subOptimal) 
           = maximalAndRestBy (fst . snd) $ map (\s -> (s, bestActionSpec bp 
									  (depth + 1) 
									  s)) 
						sons
       subProblemPayoffs = sum subPayoffs
       ownOptPayoff = bnOwnPayoff t + subProblemPayoffs
   in if bnOwnPayoff t > bestSonPayoff 
	 then ( ownOptPayoff, ActionSeqEnd) 
			      --ActionSpec {asAction = Nothing, asNext = ActionSeqEnd, asSubproblems = subSpecs})
	 else let act = Just $ head $ drop depth $ bnId bestSon
	      in  ( subProblemPayoffs + bestSonPayoff
	          , ActionSpec { asAction = act
			       , asNext = bestSonSpec
			       , asSubproblems = subSpecs})

-- | selfVisitStats, #totalArms, #totalVisits, errorProbability -> upper confidence bound. See:
-- | Audibert, Munos and Szepesvari (2006). Use of variance estimation in the multi-armed bandit problem.
-- | Modification: if we receive a Just Float, use that as the variance.
ucbBeta :: Stats -> Integer -> Float -> Float -> Maybe Float-> Float
ucbBeta stats _ _ _ _ | entries stats == 0 = 1/0
ucbBeta stats arms beta scale givenVarianceM = empMean + confidenceSlow + confidenceFast
         where empMean = mean stats
	       theVariance = fromMaybe (variance stats) givenVarianceM
               confidenceSlow = sqrt (2 * theVariance * logPart / visit)
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
          let maxVariance = maximum $ map (variance . toStats) bandits
	      arms = toInteger $ length bandits
              currUCB b = ucbBeta (toStats b) arms beta scale $ Just maxVariance
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
initTree :: (MonadIO m, Show a) => BanditProblem m a -> m (ActionSpec a, Float, BudgetedBanditTree a)
initTree (BanditProblem playAction rootId _) -- initDecisionBudget
  = do liftIO $ putStrLn $ " Init to use the ActionSpec: " ++ show rootId 
       feedback <- playAction rootId 
       case feedback of
	    BanditSubFeedback {} -> error "We currently expect rootId to be ActionSeqEnd, therefore only BanditFeedback." 
	    bf@BanditFeedback { fbPayoff = score
			      , fbInclusivePayoff = incScore
			      , fbSubproblemFeedbacks = subfbs
			      , fbActions = actions} -> do 
		 liftIO $ putStrLn $ "Init got feedback:" ++ show bf 
		 let node = BanditNode { bnStats = emptyStats `withEntry` incScore
				       , bnOwnPayoff = score
				       , bnId = justActions rootId
				       , bnUCBDecisions = 0
				       , bnSubtrees = map treeMaker subfbs
				       , bnSons = []
				       , bnUnvisitedSons = actions}
                 return (rootId, score
			, BudgetedBanditTree 
			    { bbtPlayBudget = 4 -- Corresponds to greedy mode
			    , bbtNode = node
			    , bbtMin = score
			    , bbtMax = score})

data ActionNovelty = NewAction | SonFreeVisited Integer Float deriving Show

chooseActionSequence :: BanditProblem m a -> BudgetedBanditTree a -> Float -> ActionSpec a
chooseActionSequence bp bbt beta
  = chooseActions bp (bbtPlayBudget bbt) (bbtNode bbt) beta (max 1 $ bbtMax bbt - bbtMin bbt) 0

-- Some unvisited son, and no lack of attention to visited: visit the new.
chooseActions :: BanditProblem m a -> Integer -> BanditTree a -> Float -> Float -> Int -> ActionSpec a
chooseActions bp@(BanditProblem playAction _ _) decisionBudget 
	      (BanditNode { bnStats = stats
			  , bnSubtrees = subtrees
			  , bnSons = sons
			  , bnUnvisitedSons = xunvisited : xs})
	      beta scale depth
   | fromInteger (toInteger (length sons)) <= max 1 (0.02 * (sqrt $ fromInteger (entries stats)))
   = ActionSpec { asAction = Just $ head $ drop depth xunvisited 
		, asNext = ActionSeqEnd
		, asSubproblems = 
		    map (\sp -> chooseActionSequence bp sp beta) 
			subtrees }

-- Visit existing son.
chooseActions bp decisionBudget (BanditNode { bnStats = stats
					    , bnOwnPayoff = ownPayoff
                                            , bnId = id
                                            , bnSons = sons
					    , bnUCBDecisions = ucbDec
                                            , bnUnvisitedSons = unvisited
                                            , bnSubtrees = subtrees}) 
              beta scale depth 
  | not (null sons)   -- We need at least one son
  = let uStats = (if decisionBudget <= ucbDec
                   then (withEntry emptyStats) . fromIntegral . mvN -- past budget use most visited
                   else \x->x) . bnStats  -- else use full stats
        (chosenSon, otherSons) = chosenAndRest sons uStats beta scale  -- Pick son with
	sonAct = chooseActions bp decisionBudget chosenSon 
			       beta scale $ depth + 1
    in ActionSpec { asAction = Just $ head $ drop depth $ bnId chosenSon 
		  , asNext = sonAct
		  , asSubproblems = 
		      map (\sp -> chooseActionSequence bp sp beta)
			  subtrees }
    

-- No sons, visited or otherwise: must play self.
chooseActions bp@ (BanditProblem playAction _ isDet) 
              decisionBudget 
              (BanditNode { bnStats = stats
                          , bnOwnPayoff = ownPayoff
                          , bnId = id
                          , bnSons = []
                          , bnUnvisitedSons = []
                          , bnSubtrees = subtrees}) 
              beta scale depth
  = ActionSpec { asAction = Nothing 
	       , asNext = ActionSeqEnd
	       , asSubproblems = map (\sp -> chooseActionSequence bp sp beta)
				     subtrees }


chooseActions _ _ _ _ _ _ = error "Logic error in chooseActions: should not arrive here."


updateTree :: (Show a, Eq a) => BudgetedBanditTree a -> BanditFeedback a 
	   -> (Float, BudgetedBanditTree a)
updateTree bbt bf 
  = let (payoff, repeatedAction, newNode) = updateTree2 (bbtNode bbt) bf (bbtPlayBudget bbt) 0 
	cBudget = bbtPlayBudget bbt
    in  (payoff
	 , bbt { bbtNode = newNode
	       , bbtPlayBudget = if repeatedAction then cBudget + 1 else cBudget
	       , bbtMin = min payoff $ bbtMin bbt
	       , bbtMax = max payoff $ bbtMax bbt })


updateTrees :: (Show a, Eq a) => [BudgetedBanditTree a] -> [BanditFeedback a] -> [BudgetedBanditTree a]
updateTrees bts bfs 
  = if length bts /= length bfs 
       then error "Subproblem list length inconsistent between feedback and tree." 
       else let (_, trees) = unzip [updateTree t fb | (t, fb) <- zip bts bfs]
	    in trees


nodeMaker bf@BanditFeedback {}
	     = BanditNode { bnStats = singletonStat $ fbInclusivePayoff bf
			  , bnOwnPayoff = fbPayoff bf
			  , bnId = []
			  , bnSubtrees = map treeMaker 
					     $ fbSubproblemFeedbacks bf
			  , bnUCBDecisions = 0
			  , bnSons = []
			  , bnUnvisitedSons = fbActions bf} 
nodeMaker _ = error "A fresh node is only created with unvisitedSons."

treeMaker bf@BanditFeedback {}
  = let node = nodeMaker bf
    in BudgetedBanditTree { bbtNode = node
			  , bbtPlayBudget = 4
			  , bbtMin = fbInclusivePayoff bf
			  , bbtMax = fbInclusivePayoff bf}
treeMaker _ = error "Trying to create a new tree with BanditSubFeedback"

updateTree2 :: (Show a, Eq a) => BanditTree a -> BanditFeedback a -> Integer -> Int -> (Float, Bool, BanditTree a)
-- If the BF carries a payoff, action occured in current existing BT node. Cannot be that we have sons (visited or otherwise), or feedback would be in one of them.
updateTree2 old@BanditNode {bnSons = [], bnUnvisitedSons = []} bf@BanditFeedback {} decisionBudget depth
  = let po = fbInclusivePayoff bf
    in (po
       , True -- Replaying a terminal action, time to widen
       , old { bnStats = bnStats old `withEntry` po
	     , bnSubtrees = updateTrees (bnSubtrees old) $ fbSubproblemFeedbacks bf
	     , bnUnvisitedSons = fbActions bf})

-- If actionTaken on BSF matches the next unvisited son, its successor must be a BF; create a son. Relies on unvisited sons being visited in a constant order. Subproblems need to be created; since we just found them the initial feedback is assumed a BF.
updateTree2 old@BanditNode {bnUnvisitedSons = ua:uas} bsf@BanditSubFeedback {fbActionTaken = act, fbNext = BanditFeedback {}} decisionBudget depth
  = let bf = fbNext bsf 
	po = fbInclusivePayoff bf
	freshSon = (nodeMaker bf) { bnId = bnId old ++ [fbActionTaken bsf] }
	newNode = old { bnStats = (bnStats old) `withEntry` po
		      , bnSons = freshSon : bnSons old
		      , bnSubtrees = updateTrees (bnSubtrees old) 
						 $ fbSubproblemFeedbacks bsf
		      , bnUCBDecisions = bnUCBDecisions old + 1
		      , bnUnvisitedSons = uas}
    in if last ua /= act 
	  then error $ "An action was taken that does not correspond to the next unvisited son. Node: " ++ show old ++ "Feedback: " ++ show bsf ++ "depth: " ++ show depth
	  else (po, False, newNode)

-- If actionTaken on BSF matches an existing son, continue into it.
updateTree2 old bsf@BanditSubFeedback {} decisionBudget depth
  = let (wrong, sonToUpdate:wrongAfter) = break (\s -> fbActionTaken bsf == head (drop depth $ bnId s)) $ bnSons old
	(po, rehashing, freshSon) = updateTree2 sonToUpdate (fbNext bsf) decisionBudget $ depth + 1
	newNode = old { bnStats = (bnStats old) `withEntry` po
		      , bnSons = freshSon : (wrong ++ wrongAfter)
		      , bnSubtrees = updateTrees (bnSubtrees old) (fbSubproblemFeedbacks bsf)
		      , bnUCBDecisions = bnUCBDecisions old + if decisionBudget <= bnUCBDecisions old then 0 else 1 }
    in (po, rehashing, newNode)

-- Other options should not happen.
updateTree2 node feedback decisionBudget depth = error $ "Should not get here. " ++ show node ++ show feedback ++ show decisionBudget ++ show depth

{-playFromTreeStaged :: (Monad m, Eq a) => BanditProblem m a -> Integer -> BanditTree a
                      -> Float -> Float
                      -> m (Maybe [a], Float, BanditTree a)
-}
playFromTreeStaged problem node beta
  = do let tape = chooseActionSequence problem node beta
       -- putStrLn $ "Got tape: " ++ show tape
       feedback <- bpPlayAction problem tape
       putStrLn $ "Got feedback " ++ show feedback
       putStrLn $ "Going to update " ++ show node 
       let (payoff, newTree) = updateTree node feedback
       -- putStrLn $ "Updated tree:" ++ show newTree
       return (tape, payoff, newTree)


---------------------- Problem 1: bigger is better --------------------
-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
bibPlayAction :: Monad m => Int -> ActionSpec Float -> m (BanditFeedback Float)
bibPlayAction n m
  = do return $ case justActions m of
        [] ->  BanditFeedback { fbPayoff = 0
			      , fbInclusivePayoff = 0
                              , fbActions = [ [fromInteger $ toInteger m] | m <- [1..n]]
                              , fbSubproblemFeedbacks = []}

        [i] -> BanditFeedback { fbPayoff = i
			      , fbInclusivePayoff = i
                              , fbActions = []
                              , fbSubproblemFeedbacks = []}

        _ -> error "bigger is better is a one turn game."

biggerIsBetter :: Int -> BanditProblem IO Float
biggerIsBetter n = BanditProblem { bpPlayAction = bibPlayAction n
                                 , bpRoot = ActionSeqEnd
                                 , bpIsDeterministic = True}

---------------------- Problem 2: twinPeaks --------------------
-- | A simple problem testing UCT
-- An infinitely-branching tree 
twinPeaks :: BanditProblem IO Float
twinPeaks = BanditProblem { bpPlayAction = twinHelper
                          , bpRoot = ActionSeqEnd
                          , bpIsDeterministic = False}

twinHelper :: ActionSpec Float -> IO (BanditFeedback Float)
twinHelper (ActionSpec {asAction = Just x})
           = do let payoff = - (min (abs (x+1)) (abs (x-1)))
                actions <- randomList x
                return $ BanditFeedback { fbPayoff = payoff 
					, fbInclusivePayoff = payoff 
                                        , fbActions = map (\x -> [x]) actions 
                                        , fbSubproblemFeedbacks = [] }
twinHelper _ = undefined 
randomList x = mapM randomRIO $ replicate 5 (x-0.1,x+0.1)

-- problem = twinPeaks

{-simulationStep :: (Int, BanditTree a, BanditProblem m a, Integer, Float, Float, Float) 
		  -> Maybe ((ActionSpec a, Float, BanditTree a), 
			    (Int, BanditTree a, BanditProblem m a, Integer, Float, Float, Float)) -}
simulationStep (i, _, _, _)  | i == 0 = return Nothing
simulationStep quad =
        let (i, bt, problem, beta) = quad
        in do (a, s, nbs) <- playFromTreeStaged problem bt beta
              -- liftIO $ putStrLn $ show (i, length $ justActions a, s)
              return $ Just ((a,s,nbs), (i-1, nbs, problem, beta))

-- Ended up equivalent to unfoldrM from Control.Monad.Loops in monad-loops, but that's not standard issue.
--unfoldrMine      :: (MonadIO m, Show tb, Show ta) => (tb -> m (Maybe (ta, tb))) -> tb -> m [ta]
unfoldrMine f b  = do
  x <- f b 
  case x of
   Just (a,new_b) -> do rest <- unfoldrMine f new_b -- liftIO $ putStrLn $ show a
			return $ a : rest
   Nothing        -> return []

-- runWithHistory :: MonadIO m => Float -> Float -> BanditProblem m a -> Integer -> BanditTree a -> m ([(ActionSpec a, Float, BanditTree a)])
runWithHistory n beta problem startState = unfoldrMine simulationStep (n, startState, problem, beta)

-- main = findBest 10 10 twinPeaks Nothing

-- findBest :: (Show a, MonadIO m) => Float -> Float -> BanditProblem m a -> Maybe Integer -> m (ActionSpec a)
findBest budget beta problem playBudgetM =
    do liftIO $ do --hSetBuffering stdout NoBuffering
		   --hSetBuffering stderr NoBuffering
		   putStrLn $ "Entered findBest with budget, beta: " ++ show (budget, beta)
       initRes <- initTree problem  -- Uses 1 run from the budget
       -- (fromMaybe (ceiling budget) playBudgetM)
       let (_, _, startbt) = initRes
       allResults <- runWithHistory (budget - 1) beta problem startbt
       let tree = head $ reverse $ [c | (a,b,c) <- initRes : allResults]
       liftIO $ putStrLn $ show tree
       let (bestScore, actSpec) = bestActionSpec problem 0 $ bbtNode tree
       liftIO $ putStrLn $ show (actSpec, bbtPlayBudget tree)
       return actSpec
