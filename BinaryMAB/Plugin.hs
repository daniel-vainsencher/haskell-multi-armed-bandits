module BinaryMAB.Plugin (plugin) where
import GhcPlugins
import MABOpt
import MultiArmedBanditTree
import SimplCore

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

simpl_mode = SimplMode { sm_phase      = Phase 0
                         , sm_names      = []
                         , sm_rules      = True
                         , sm_eta_expand = True
                         , sm_inline     = True
                         , sm_case_case  = True }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  return $ todo ++ [CoreDoPluginPass "Learning simplification" $ learnAndApply 3.0]
-- Simplify 2 [Just (repeat True), Nothing] simpl_mode]

learnAndApply :: Float -> ModGuts -> CoreM ModGuts

learnAndApply _ mg
    = do dflags <- getDynFlags
         let problem = inliningProblem mg dflags
         tape <- liftIO $ findBest 100 100 problem
         simplifyPgm (todo $ tapeSetFromTape tape) mg
