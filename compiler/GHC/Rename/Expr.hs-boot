module GHC.Rename.Expr where
import GHC.Types.Name
import GHC.Hs
import GHC.Types.Name.Set ( FreeVars )
import TcRnTypes
import GHC.Types.SrcLoc   ( Located )
import Outputable  ( Outputable )

rnLExpr :: LHsExpr GhcPs
        -> RnM (LHsExpr GhcRn, FreeVars)

rnStmts :: --forall thing body.
           Outputable (body GhcPs) => HsStmtContext GhcRn
        -> (Located (body GhcPs) -> RnM (Located (body GhcRn), FreeVars))
        -> [LStmt GhcPs (Located (body GhcPs))]
        -> ([Name] -> RnM (thing, FreeVars))
        -> RnM (([LStmt GhcRn (Located (body GhcRn))], thing), FreeVars)
