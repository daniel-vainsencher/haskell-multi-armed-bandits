module BinaryMAB.Plugin (plugin) where
import GhcPlugins

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
  putMsgS "Hello!"
  return $ todo ++ [CoreDoSimplify 2 [Just (repeat True), Nothing] simpl_mode]
