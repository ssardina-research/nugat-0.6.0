/**CFile***********************************************************************

  FileName    [ gameWriteModel.c ]

  PackageName [ game ]

  Synopsis    [ Defines functions to write (print out) a scalar (flat) or
                boolean model of a game hierarchy. ]

  Description [ ]

  SeeAlso     [ compileCmd.h ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game'' package of NuGaT.
  Copyright (C) 2010 FBK-irst.

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

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include "gameInt.h"
#include "parser/game_symbols.h"
#include "GameHierarchy.h"
#include "GamePlayer.h"
#include "PropDbGame.h"

#include "compile/compile.h"
#include "enc/enc.h"
#include "node/node.h"
#include "prop/propPkg.h"
#include "utils/utils.h"
#include "utils/NodeList.h"
#include "utils/array.h"
#include "utils/error.h"

#include <stdio.h>
#include <stdbool.h>

/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id: gameWriteModel.c,v 1.1.2.6 2010-02-08 17:12:44 nusmv Exp $";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static bool game_split_and_print_spec ARGS((FILE* out,
                                            node_ptr specs,
                                            const char* str,
                                            BddEnc_ptr enc,
                                            SymbLayer_ptr det_layer));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Performs the "write_flat_model" command for games. ]

  Description [ This function is used in CommandWriteModelFlat to
                adopt "write_flat_model" command to deal with a game
                declaration. ]

  SideEffects [ ]

  SeeAlso     [ Compile_WriteFlattenModel ]

******************************************************************************/
void Game_CommandWriteFlatModel(NuSMVEnv_ptr env,FILE* ofileid)
{
  SymbTable_ptr st;
  array_t* layer1;
  array_t* layer2;

  nusmv_assert((FILE *) NULL != ofileid);

  st = SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE));

  layer1 = array_alloc(const char*, 1);
  layer2 = array_alloc(const char*, 1);
  array_insert_last(const char*, layer1, MODEL_LAYER_1);
  array_insert_last(const char*, layer2, MODEL_LAYER_2);

  fprintf(ofileid, "\n-- Begin GAME Flat Model\n");
  fprintf(ofileid, "GAME\n");

  Compile_WriteFlattenFsm(env,
                          ofileid,
                          st,
                          layer1,
                          PLAYER_NAME_1,
                          GameHierarchy_get_player_1(mainGameHierarchy),
                          true);
  Compile_WriteFlattenFsm(env,
                          ofileid,
                          st,
                          layer2,
                          PLAYER_NAME_2,
                          GameHierarchy_get_player_2(mainGameHierarchy),
                          true);

  /* currently games cannot have usual NuSMV specifications */
  nusmv_assert(NULL == GameHierarchy_get_ctlspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_compute(mainGameHierarchy) &&
               NULL == GameHierarchy_get_ltlspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_invarspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_pslspec(mainGameHierarchy));

  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_reachtarget(mainGameHierarchy),
                            "REACHTARGET",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_avoidtarget(mainGameHierarchy),
                            "AVOIDTARGET",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_reachdeadlock(mainGameHierarchy),
                            "REACHDEADLOCK",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_avoiddeadlock(mainGameHierarchy),
                            "AVOIDDEADLOCK",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_buchigame(mainGameHierarchy),
                            "BUCHIGAME",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_ltlgame(mainGameHierarchy),
                            "LTLGAME",
                            NULL,
                            NULL);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_genreactivity(mainGameHierarchy),
                            "GENREACTIVITY",
                            NULL,
                            NULL);

  fprintf(ofileid, "\n-- End GAME Flat Model\n");

  array_free(layer2);
  array_free(layer1);
}

/**Function********************************************************************

  Synopsis    [ Performe the "write_boolean_model" command for games. ]

  Description [ This function is used in CommandWriteModelFlatBool to
                adopt "write_boolean_model" command to deal with a
                game declaration. ]

  SideEffects [ ]

  SeeAlso     [ Compile_WriteBoolModel ]

******************************************************************************/
void Game_CommandWriteBooleanModel(NuSMVEnv_ptr env,FILE* ofileid)
{
  BddEnc_ptr enc;
  SymbTable_ptr st;
  GameSexpFsm_ptr bool_fsm;
  NodeList_ptr layers;

  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  BoolEnc_ptr bool_enc = BOOL_ENC(NuSMVEnv_get_value(env, ENV_BOOL_ENCODER));

  nusmv_assert((FILE *) NULL != ofileid);

  bool_fsm = PropDbGame_master_get_game_bool_sexp_fsm(PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)));
  enc = NuSMVEnv_get_value(env, ENV_BDD_ENCODER);
  st = BaseEnc_get_symb_table(BASE_ENC(enc));

  fprintf(ofileid, "\nGAME\n");

  /* For each player: create a list of all model layers, i.e., scalar
     and boolean, then print. */
  layers = NodeList_create();
  NodeList_append(layers, (node_ptr) SymbTable_get_layer(st, MODEL_LAYER_1));
  NodeList_append(layers, (node_ptr) SymbTable_get_layer(st,
                            BoolEnc_scalar_layer_to_bool_layer(bool_enc,MODEL_LAYER_1)));
  Compile_WriteBoolFsm(env,
                       ofileid,
                       st,
                       layers,
                       PLAYER_NAME_1,
                       BOOL_SEXP_FSM(GameSexpFsm_get_player_1(bool_fsm)),
                       true);
  NodeList_destroy(layers);

  layers = NodeList_create();
  NodeList_append(layers, (node_ptr) SymbTable_get_layer(st, MODEL_LAYER_2));
  NodeList_append(layers, (node_ptr) SymbTable_get_layer(st,
                            BoolEnc_scalar_layer_to_bool_layer(bool_enc,MODEL_LAYER_2)));
  Compile_WriteBoolFsm(env,
                       ofileid,
                       st,
                       layers,
                       PLAYER_NAME_2,
                       BOOL_SEXP_FSM(GameSexpFsm_get_player_2(bool_fsm)),
                       true);
  NodeList_destroy(layers);

  /* Currently games cannot have usual NuSMV specifications. */
  nusmv_assert(NULL == GameHierarchy_get_ctlspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_compute(mainGameHierarchy) &&
               NULL == GameHierarchy_get_ltlspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_invarspec(mainGameHierarchy) &&
               NULL == GameHierarchy_get_pslspec(mainGameHierarchy));

  SymbLayer_ptr det_layer = SymbTable_create_layer(st,
                                                   (char*) NULL, /*temp name*/
                                                   SYMB_LAYER_POS_DEFAULT);

  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_reachtarget(mainGameHierarchy),
                            "REACHTARGET",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_avoidtarget(mainGameHierarchy),
                            "AVOIDTARGET",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_reachdeadlock(mainGameHierarchy),
                            "REACHDEADLOCK",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_avoiddeadlock(mainGameHierarchy),
                            "AVOIDDEADLOCK",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_buchigame(mainGameHierarchy),
                            "BUCHIGAME",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_ltlgame(mainGameHierarchy),
                            "LTLGAME",
                            enc,
                            det_layer);
  game_split_and_print_spec(ofileid,
                            GameHierarchy_get_genreactivity(mainGameHierarchy),
                            "GENREACTIVITY",
                            enc,
                            det_layer);

  if (/*NodeList_get_length(SymbLayer_get_input_vars*/SymbLayer_get_input_vars_num(det_layer) != 0) {
    ErrorMgr_rpterr(errmgr,"New variables have been created during determinization of game \n"
           "specification. Such new (input) variables are not supported in "
           "games.");
  }

  SymbTable_remove_layer(st, det_layer);
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Splits the list of specifications into individual
                specifications and them prints them. ]

  Description [ The specifications are given as a list of specs.

                If the booleanized version of the specification should
                be output then enc and det_layer should be BDD encoder
                and determinization layer (otherwise they have to be
                NULL, which means the specs are output as they are).

                Before spec's expression string str is output.

                Returns false iff the empty list of specs is
                provided. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static bool game_split_and_print_spec(FILE* out,
                                      node_ptr specs,
                                      const char* str,
                                      BddEnc_ptr enc,
                                      SymbLayer_ptr det_layer)
{

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(specs));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

  if (Nil == specs) return false; /* there are no specifications */

  for (; specs != Nil; specs = cdr(specs)) {
    node_ptr spec = car(specs);

    /* game specifications are wrapped during hierarchy creation */
    nusmv_assert(GAME_SPEC_WRAPPER == node_get_type(spec));

    if (det_layer != NULL) { /* booleanizing is required */
      if (cdr(spec) != Nil) {
        switch (node_get_type(cdr(spec))) {
        case GAME_EXP_LIST:
          {
            node_ptr res;
            nusmv_assert(car(cdr(spec)) != Nil);
            res = Compile_expr2bexpr(enc, det_layer, car(cdr(spec)));
            spec = find_node(nodemgr,GAME_SPEC_WRAPPER,
                             car(spec),
                             find_node(nodemgr,GAME_EXP_LIST,
                                       res,
                                       Nil));
            break;
          }
        case GAME_TWO_EXP_LISTS:
          {
            node_ptr resl, resr;
            nusmv_assert(car(cdr(spec)) != Nil);
            nusmv_assert(cdr(cdr(spec)) != Nil);
            resl = Compile_expr2bexpr(enc, det_layer, car(cdr(spec)));
            resr = Compile_expr2bexpr(enc, det_layer, cdr(cdr(spec)));
            spec = find_node(nodemgr,GAME_SPEC_WRAPPER,
                             car(spec),
                             find_node(nodemgr,GAME_TWO_EXP_LISTS,
                                       resl,
                                       resr));
            break;
          }
        default:
          {
            /* This should be a body of REACH/AVOIDTARGET or LTLGAME,
               i.e., an expression w/o game-specific symbols. */
            node_ptr res;
            nusmv_assert(cdr(spec) != Nil);
            res = Compile_expr2bexpr(enc, det_layer, cdr(spec));
            spec = find_node(nodemgr,GAME_SPEC_WRAPPER, car(spec), res);
            break;
          }
        }
      } /* if (cdr(spec) != Nil) -- else is REACH/AVOIDDEADLOCK, no
           action required. */
    }
    else { /* not manipulations are required */
      /* nothing */
    }

    /* If conversion to DAG is required it should be done here: spec =
       compile_convert_to_dag(spec, dag_info, defines)
    */

    /* print the expression */
    fprintf(out, "\n%s \n", str);
    print_node(wffprint,out, spec);
    fprintf(out, "\n");
  }

  fprintf(out, "\n");
  return true;
}
