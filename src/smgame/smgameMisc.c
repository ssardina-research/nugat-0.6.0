/**CFile***********************************************************************

  FileName    [ smgameMisc.c ]

  PackageName [ smgame ]

  Synopsis    [ This file contains the main routine for the batch use of
                NuGaT. ]

  Description [ The batch main executes the various model checking
                steps in a predefined order. After the processing of
                the input file than it returned to the calling
                shell. ]

  SeeAlso     [ ]

  Author      [ Marco Roveri, Viktor Schuppan ]

  Copyright   [
  This file is part of the ``smgame'' package of NuGaT.
  Copyright (C) 2010 by FBK-irst.

  NuGaT is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  NuGaT is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuGaT see <http://es.fbk.eu/tools/nugat>
  or email to <nugat-users@list.fbk.eu>.
  Please report bugs to <nugat-users@list.fbk.eu>.

  To contact the NuGaT development board, email to <nugat@list.fbk.eu>. ]

******************************************************************************/

#include "bmc/bmc.h"
#include "cmd/cmd.h"
#include "compile/compile.h"
#include "dd/dd.h"
#include "fsm/bdd/BddFsm.h"
#include "opt/opt.h"
#include "prop/propPkg.h"
#include "utils/utils.h"
#include "utils/error.h"
#include "config.h"
#include "../addons/game/gameInt.h"
#if HAVE_GAME
#include "addons/game/game.h"
#include "addons/game/PropGame.h"
#include "addons/game/PropDbGame.h"
#endif

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: smMisc.c,v 1.26.2.26.2.3.2.26.4.14 2010-02-08 12:25:28 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stderr;
EXTERN FILE* nusmv_stdout;
EXTERN DDMgr_ptr dd_manager;

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The batch main. ]

  Description [ First reads the input file, then flattens the
                hierarchy. After this preliminary phase it creates the
                boolean variables necessary for the encoding and then
                starts compiling the read model into BDD. Now computes
                the reachable states depending if the flag has been
                set. Before starting verifying if the properties
                specified in the model hold or not it computes the
                fairness constraints. You can also activate the
                reordering and also choose to avoid the verification
                of the properties. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Smgame_BatchMain(NuSMVEnv_ptr env)
{
  PropDb_ptr  prop_db = PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB));
  OptsHandler_ptr oh = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  /* Necessary to have standard behavior in the batch mode */
  ErrorMgr_reset_long_jmp(errmgr);
  CATCH(errmgr) {

  /* ================================================== */
  /*   1: Read the model                                */
  /* ================================================== */
  if (Cmd_CommandExecute(env,"read_model")) ErrorMgr_nusmv_exit(errmgr,1);

  /* ================================================== */
  /*  2: Flatten hierarchy                              */
  /* ================================================== */
  if (Cmd_CommandExecute(env,"flatten_hierarchy")) ErrorMgr_nusmv_exit(errmgr,1);

  /* If the -lp option is used, list the properties and exit */
  if (opt_list_properties(oh) == true) {
    if (Cmd_CommandExecute(env,"show_property")) ErrorMgr_nusmv_exit(errmgr,1);
    return;
  }

  /* ================================================== */
  /*  3: Builds the encodings                           */
  /* ================================================== */
  if (Cmd_CommandExecute(env,"encode_variables")) ErrorMgr_nusmv_exit(errmgr,1);

  /* ================================================== */
  /*  4: Builds the flat FSMs                           */
  /* ================================================== */
  if (Cmd_CommandExecute(env,"build_flat_model")) ErrorMgr_nusmv_exit(errmgr,1);



  /* --------------------------------------------------- */
  /*  Write the flat and bool FSMs (if required)         */
  /* ----------------------------------------------------*/
  if (get_output_flatten_model_file(oh) != NIL(char)) {
    if (Cmd_CommandExecute(env,"write_flat_model")) ErrorMgr_nusmv_exit(errmgr,1);
  }

  if (get_output_boolean_model_file(oh) != NIL(char)) {
    if (Cmd_CommandExecute(env,"build_boolean_model")) ErrorMgr_nusmv_exit(errmgr,1);
    if (Cmd_CommandExecute(env,"write_boolean_model")) ErrorMgr_nusmv_exit(errmgr,1);
  }

#if HAVE_SAT_SOLVER
  /* ================================================== */
  /*  5.1 BMC starts                                    */
  /* ================================================== */
  if (opt_bmc_mode(oh) == true) {
    if (opt_verbose_level_gt(oh, 0)) {
      fprintf(stderr, "Entering BMC mode...\n");
    }

    /* games cannot be checked with BMC */
#if HAVE_GAME
    if (opt_game_game(oh)) nusmv_assert(false);
#endif

    /* build_boolean_model may have been already called if the output
       boolean model was specified in the argument list. */
    if (Compile_check_if_bool_model_was_built(env,NULL, false)) {
      if (Cmd_CommandExecute(env,"build_boolean_model")) ErrorMgr_nusmv_exit(errmgr,1);
    }

    /* Initializes the bmc package, and commits both the model and the
       determinization layers: */
    if (Cmd_CommandExecute(env,"bmc_setup")) ErrorMgr_nusmv_exit(errmgr,1);

    if (get_prop_no(oh) != -1) {
      int prop_no = get_prop_no(oh);
      Prop_ptr prop;

      if (opt_verbose_level_gt(oh, 0)) {
        fprintf(stderr, "Verifying property %d...\n", prop_no);
      }

      if ((prop_no < 0) ||
          (prop_no >= PropDb_get_size(prop_db))) {
        fprintf(stderr,
                "Error: \"%d\" is not a valid property index\n",
                prop_no);
        ErrorMgr_nusmv_exit(errmgr,1);
      }

      prop = PropDb_get_prop_at_index(prop_db, prop_no);

      switch (Prop_get_type(prop)) {
      case Prop_Ltl:
        {
          int rel_loop;

          /* skip if -ils option is given */
          if (opt_ignore_ltlspec(oh)) break;

          rel_loop = Bmc_Utils_ConvertLoopFromString(get_bmc_pb_loop(oh),
                                                     NULL);
          Bmc_GenSolveLtl(env,prop, get_bmc_pb_length(oh),
                          rel_loop,
                          /*increasing length*/ TRUE ,
                          TRUE,
                          BMC_DUMP_NONE,
                          NULL);
          break;
        }

      case Prop_Psl:
        {
          int rel_loop = Bmc_Utils_ConvertLoopFromString(get_bmc_pb_loop(oh),
                                                         NULL);
          /* skip if -ips option is given */
          if (opt_ignore_pslspec(oh)) break;

          Bmc_Gen_check_psl_property(env,prop,
                                 false,
                                 false,
                                 false,
                                 get_bmc_pb_length(oh),
                                 rel_loop);
          break;
        }

      case Prop_Invar:
        /* skip if -ii option is given */
        if (opt_ignore_invar(oh)) break;

        Bmc_GenSolveInvar(env,prop, TRUE, BMC_DUMP_NONE, NULL);
        break;

      default:
        fprintf(stderr,
                "Error: only LTL, PSL and INVAR properties can be checked in "
                "BMC mode\n");
        ErrorMgr_nusmv_exit(errmgr,1);
      } /* switch on type */

    }
    else {
      /* Checks all ltlspecs, invarspecs and pslspecs */

      if (! opt_ignore_ltlspec(oh)) {
        lsList props;
        lsGen  iterator;
        Prop_ptr prop;
        int rel_loop;

        if (opt_verbose_level_gt(oh, 0)) {
          fprintf(stderr, "Verifying the LTL properties...\n");
        }


        props = PropDb_get_props_of_type(prop_db, Prop_Ltl);
        nusmv_assert(props != LS_NIL);

        lsForEachItem(props, iterator, prop) {
          rel_loop = Bmc_Utils_ConvertLoopFromString(get_bmc_pb_loop(oh),
                                                     NULL);

          Bmc_GenSolveLtl(env,prop,
                          get_bmc_pb_length(oh),
                          rel_loop,
                          /*increasing length*/ TRUE,
                          TRUE,
                          BMC_DUMP_NONE,
                          NULL);
        }

        lsDestroy(props, NULL); /* the list is no longer needed */
      }

      if (! opt_ignore_pslspec(oh)) {
        lsList props;
        lsGen  iterator;
        Prop_ptr prop;
        int rel_loop =
          Bmc_Utils_ConvertLoopFromString(get_bmc_pb_loop(oh), NULL);

        if (opt_verbose_level_gt(oh, 0)) {
          fprintf(stderr, "Verifying the PSL properties...\n");
        }

        props = PropDb_get_props_of_type(prop_db, Prop_Psl);
        nusmv_assert(props != LS_NIL);

        lsForEachItem(props, iterator, prop) {
          if (Prop_is_psl_ltl(prop)) {
            Bmc_Gen_check_psl_property(env,prop,
                                   false,
                                   false,
                                   false,
                                   get_bmc_pb_length(oh),
                                   rel_loop);
          }
        }

        lsDestroy(props, NULL); /* the list is no longer needed */
      }

      if (! opt_ignore_invar(oh)) {
        lsList props;
        lsGen iterator;
        Prop_ptr prop;

        if (opt_verbose_level_gt(oh, 0)) {
          fprintf(stderr, "Verifying the INVAR properties...\n");
        }

        props = PropDb_get_props_of_type(prop_db,
                                         Prop_Invar);
        nusmv_assert(props != LS_NIL);

        lsForEachItem(props, iterator, prop) {
          Bmc_GenSolveInvar(env,prop, TRUE, BMC_DUMP_NONE, NULL);
        }

        lsDestroy(props, NULL); /* the list is no longer needed */
      }
    }

    return;
  } /* end of BMC */
#endif

  /* ================================================== */
  /*  5.2 BDD-based model checking starts               */
  /* ================================================== */

  /* Builds the BDD FSM of the whole read model.
     If COI is enabled there is no reason to create global BDD FSM since
     every property will have its one instance of a BDD FSM.
  */
  if (opt_cone_of_influence(oh) == false) {
    if (Cmd_CommandExecute(env,"build_model")) ErrorMgr_nusmv_exit(errmgr,1);
  }

  /* checks the fsm if required */
  if (opt_check_fsm(oh) == true) {
    if (opt_cone_of_influence(oh)) {
      fprintf(stderr,
              "WARNING: Check for totality of the transition relation cannot "
              "currently\n"
              "performed in batch mode if the cone of influence reduction has "
              "been enabled.\n");
      ErrorMgr_nusmv_exit(errmgr,1);
    }
#if HAVE_GAME

    /* The Game FSM cannot be checked */
    if (opt_game_game(oh)) {
      fprintf(stderr,
      "WARNING: Check for totality of the Game transition relations cannot \n"
              "currently performed.\n");
      ErrorMgr_nusmv_exit(errmgr,1);
    }
 #endif
    BddFsm_check_machine(Prop_get_bdd_fsm(PROP(NuSMVEnv_get_value(env, ENV_PROP_DB))));
  }

  if (get_prop_no(oh) != -1) {

    char command[20 + sizeof(long)];

#if HAVE_GAME
    {
      /* If this is PropGame_LtlGame, then build Boolean model. */
      Prop_ptr prop;
      prop = PropDb_get_prop_at_index(prop_db,
                                      get_prop_no(oh));
      if (Prop_get_type(prop) == PropGame_LtlGame) {
        if (Compile_check_if_bool_model_was_built(env,NULL, false)) {
          if (Cmd_CommandExecute(env,"build_boolean_model")) ErrorMgr_nusmv_exit(errmgr,1);
        }
      }
    }
#endif

    sprintf(command, "check_property -n %d", get_prop_no(oh));

    if (Cmd_CommandExecute(env,command)) ErrorMgr_nusmv_exit(errmgr,1);
  }
  else {

    /* Evaluates the Specifications */
    if (!opt_ignore_spec(oh)) {
      PropDb_verify_all_type(prop_db, Prop_Ctl);
    }

    if (!opt_ignore_compute(oh)) {
      PropDb_verify_all_type(prop_db, Prop_Compute);
    }

    /* Evaluates the LTL specifications */
    if (!opt_ignore_ltlspec(oh)) {
      PropDb_verify_all_type(prop_db, Prop_Ltl);
    }

    /* Evaluates the PSL specifications */
    if (!opt_ignore_pslspec(oh)) {
      PropDb_verify_all_type(prop_db, Prop_Psl);
    }

    /* Evaluates CHECKINVARIANTS */
    if (!opt_ignore_invar(oh)) {
      PropDb_verify_all_type(prop_db, Prop_Invar);
    }

#if HAVE_GAME
    /* GAME SPECIFICATIONS.
       They are always evaluated.
       This code is actually used only if there is a game definition
       containing game specifications.
    */

    PropDb_verify_all_type(prop_db, PropGame_ReachTarget);
    PropDb_verify_all_type(prop_db, PropGame_AvoidTarget);
    PropDb_verify_all_type(prop_db, PropGame_ReachDeadlock);
    PropDb_verify_all_type(prop_db, PropGame_AvoidDeadlock);
    PropDb_verify_all_type(prop_db, PropGame_BuchiGame);
    {
      /* If the set of PropGame_LtlGame is non-empty, then build
         Boolean model. */
      lsList tmp;
      tmp = PropDb_get_props_of_type(prop_db,
                                     PropGame_LtlGame);
      if (lsLength(tmp) > 0) {
        if (Compile_check_if_bool_model_was_built(env,NULL, false)) {
          if (Cmd_CommandExecute(env,"build_boolean_model")) ErrorMgr_nusmv_exit(errmgr,1);
        }
      }
      lsDestroy(tmp, NULL);
    }
    PropDb_verify_all_type(prop_db, PropGame_LtlGame);
    PropDb_verify_all_type(prop_db, PropGame_GenReactivity);
#endif
  }


  /* Reporting of statistical information. */
  if (opt_verbose_level_gt(oh, 0)) {
    if (Cmd_CommandExecute(env,"print_usage")) ErrorMgr_nusmv_exit(errmgr,1);
  }

  /* Computing and Reporting of the Effect of Reordering */
  if (opt_reorder(oh)) {
    fprintf(stdout, "\n========= starting reordering ============\n");
    dd_reorder(dd_manager, get_reorder_method(oh), DEFAULT_MINSIZE);
    fprintf(stdout, "\n========= after reordering ============\n");
    if (opt_verbose_level_gt(oh, 0)) {
      if (Cmd_CommandExecute(env,"print_usage")) ErrorMgr_nusmv_exit(errmgr,1);
    }

    if (Cmd_CommandExecute(env,"write_order")) ErrorMgr_nusmv_exit(errmgr,1);
  }

  /* Reporting of Reachable States */
  if (opt_print_reachable(oh) == true) {
    if (opt_cone_of_influence(oh)) {
      fprintf(stderr,
              "WARNING: Statistics of reachable states is not currently "
              "available\n"
              "in batch mode if cone of influence reduction has been "
              "enabled.\n");
      ErrorMgr_nusmv_exit(errmgr,1);
    }
#if HAVE_GAME
    /* The Game FSM cannot be checked */
    if (opt_game_game(oh)) {
      fprintf(stderr,
      "WARNING: Statistics of reachable states is not currently available\n"
              "for Game transition relations.\n");
      ErrorMgr_nusmv_exit(errmgr,1);
    }
#endif

    BddFsm_print_reachable_states_info(Prop_get_bdd_fsm(PROP(NuSMVEnv_get_value(env, ENV_PROP_DB))),
                                       false, /* do not print states */
                                       false, /* do not print defines */
                                       false, /* do not print formula */
                                       OSTREAM(nusmv_stdout));
  }

  } FAIL(errmgr) {
    fprintf(stderr, "\nNuGaT terminated by a signal\n");
    ErrorMgr_nusmv_exit(errmgr,1);
  }
}
