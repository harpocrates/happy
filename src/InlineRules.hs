module InlineRules(inline_rules, Prod2(..), Rule2(..), InlinedCode(..)) where

import AbsSyn
import ParamRules (Prod1(..), Rule1(..), RuleName, Subst)   -- only depend on the types
import qualified Data.Map as M
import Control.Monad.State

-- XXX: cycles in inlining will cause divergence

-- | Similar to 'Rule1', but `IsInline`'s have been eliminated
data Rule2    = Rule2 RuleName [Prod2] (Maybe (String, Subst))

-- | Similar to 'Prod1', but `IsInline`'s have been eliminated
data Prod2    = Prod2
                  [RuleName]
                  InlinedCode
                  Int
                  (Maybe String)


-- | Right hand side of a production: the code
--
-- The reason this is tree like is that we have to accomodate for inlining of
-- code coming from potentially many inlined rules.
data InlinedCode = Code
                     String                -- code from this level
                     [Maybe InlinedCode]   -- code from inlined rules (usually empty)
  deriving Show

-- | Desugar productions with inline annotations to ones without
--
-- Doing this is just a matter of splicing in
-- and collect every possible instantiation of parameterized productions. Then,
-- we generate a new non-parametrized rule for each of these.
inline_rules :: [Rule1] -> [Rule2]
inline_rules rules = M.elems $ execState (mapM_ inline_rule [ n | Rule1 n _ _ <- rules ])
                                         M.empty
  where
    rule1_bank :: M.Map RuleName Rule1
    rule1_bank = M.fromList [ (n, r) | r@(Rule1 n _ _) <- rules ]

    -- Ensure a rule is translated into the states' rule bank.
    --
    -- NB: this may involve translating more rules, or no rules. All we can say
    -- for sure is that when this function returns, the state will contain the
    -- translation of the rule with the given name.
    inline_rule
      :: RuleName                            -- ^ the new rule to process
      -> State (M.Map RuleName Rule2) Rule2  -- ^ updated processed rules
    inline_rule rn = do
      maybeProcessed <- gets (M.lookup rn)
      case maybeProcessed of
        Just alreadyProcessed -> return alreadyProcessed
        Nothing -> do let Just (Rule1 n ps ts) = M.lookup rn rule1_bank
                      ps' <- mapM process_prod ps
                      let r2 = Rule2 n (concat ps') ts
                      modify' (M.insert n r2)
                      return r2

    -- NB: we get back a list of 'Prod2' (instead of just one) because inlining
    -- can multiply the number of productions.
    --
    -- TODO: how is precedence or subst stuff affected by inlining?
    process_prod :: Prod1 -> State (M.Map RuleName Rule2) [Prod2]
    process_prod (Prod1 [] code n p) = return [Prod2 [] (Code code []) n p]
    process_prod (Prod1 terms code n p) = do
      terms_expansions <- mapM process_term terms

      -- If this looks like it could get very large fast, that's because it can
      let crossed = foldr1 (\ps1 ps2 -> [ (rs1 ++ rs2, acc1 ++ acc2)
                                        | (rs1, acc1) <- ps1
                                        , (rs2, acc2) <- ps2 ])
                           terms_expansions

      -- TODO: are `n` and `p` really unchanged here?
      return [ Prod2 rs (Code code code_acc) n p
             | (rs, code_acc) <- crossed ]

    process_term
      :: (RuleName, IsInline)
      -> State (M.Map RuleName Rule2)
               [([RuleName], [Maybe InlinedCode])]   -- outer list = all the productions
                                                     -- first tuple = rules in a production
                                                     -- second tuple = inlined code from those rules
    process_term (rn, NotInline) = return [([rn], [Nothing])]
    process_term (rn, IsInline) = do
      Rule2 _ prods _TODO <- inline_rule rn -- TODO: should we not do something with the subst?
      return [ (rs, [Just code])
             | Prod2 rs code _TODO1 _TODO2 <- prods ]

