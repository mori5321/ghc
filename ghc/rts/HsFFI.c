/* -----------------------------------------------------------------------------
 * $Id: HsFFI.c,v 1.1 2002/11/17 15:27:08 panne Exp $
 *
 * (c) The GHC Team, 2002
 *
 * RTS entry points as mandated by the FFI addendum to the Haskell 98 report
 *
 * ---------------------------------------------------------------------------*/

#include "HsFFI.h"
#include "Rts.h"

void
hs_init(int *argc, char **argv[])
{
  /* ToDo: Implement! */
}

void
hs_exit(void)
{
  /* ToDo: Implement! */
}

void
hs_set_argv(int argc, char *argv[])
{
  /* ToDo: Implement! */
}

void
hs_perform_gc(void)
{
    /* Hmmm, the FFI spec is a bit vague, but it seems to imply a major GC... */
    performMajorGC();
}

void
hs_free_stable_ptr(HsStablePtr *sp)
{
    /* The cast is for clarity only, both HsStablePtr and StgStablePtr are
       typedefs for void*. */
    freeStablePtr((StgStablePtr)sp);
}

void
hs_free_fun_ptr(HsFunPtr *fp)
{
    /* I simply *love* all these similar names... */
    freeHaskellFunctionPtr(fp);
}
