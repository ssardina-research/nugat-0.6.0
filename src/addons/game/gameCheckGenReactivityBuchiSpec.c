/**CFile***********************************************************************

  FileName    [ gameCheckGenReactivityBuchiSpec.c ]

  PackageName [ game ]

  Synopsis    [ This file contains functions required to check General
                Reactivity (1) (GENREACTIVITY) problems and Buchi Game
                (BUCHIGAME) problems.

                The algorithm used is from "Synthesis of Reactive(1)
                Designs" by Piterman, Pnueli, Sa'ar.

                For Buchi games the above algorithm is simplified a
                bit (the most internal loop is removed). ]

  Description [ ]

  SeeAlso     [ ]

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

#include "game.h"
#include "gameInt.h"
#include "PropGame.h"
#include "parser/game_symbols.h"

#include "enc/enc.h"
#include "parser/symbols.h"
#include "compile/compile.h"


/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id: gameCheckGenReactivityBuchiSpec.c,v 1.1.2.6 2010-02-08 12:25:25 nusmv Exp $";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stdout;
EXTERN FILE* nusmv_stderr;
EXTERN options_ptr options;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static boolean
game_compute_gen_reactivity ARGS((node_ptr specExp,
                                  GamePlayer player,
                                  GameBddFsm_ptr fsm,
                                  Game_InitTermination earlierTermination,
                                  GameStrategy_ptr* strategy,
                                  node_ptr jxVar,
                                  bdd_ptr overapproxWinStates,
                                  bdd_ptr underapproxWinStates,
                                  bdd_ptr* winningStates));

static boolean game_compute_buchi_game ARGS((NuSMVEnv_ptr env,
                                             PropGame_ptr prop,
                                             GameStrategy_ptr* strategy,
                                             node_ptr jxVar));

static void game_free_list_of_bdd ARGS((NodeMgr_ptr nodemgr,DDMgr_ptr dd, node_ptr list));

static void game_free_array_of_bdd ARGS((DDMgr_ptr dd,
                                         bdd_ptr* array,
                                         int size));

static void game_free_list_of_array_of_bdd ARGS((NodeMgr_ptr nodemgr,
                                                 DDMgr_ptr dd,
                                                 node_ptr list,
                                                 int size));

static void game_declare_special_var ARGS((NuSMVEnv_ptr env,
                                           int guaranteeNumber,
                                           SymbLayer_ptr* new_layer,
                                           node_ptr* new_var));

static void game_undeclare_special_var ARGS((NuSMVEnv_ptr env,
                                             SymbLayer_ptr layer));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Checks a general reactivity specification. ]

  Description [ Input property has to be a general reactivity
                specification. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_CheckGenReactivitySpec(NuSMVEnv_ptr env, PropGame_ptr prop, gameParams_ptr params)
{
  boolean construct_strategy;
  boolean isSuccess;
  GameStrategy_ptr strategy;
  SymbLayer_ptr layer;
  node_ptr var = Nil;
  node_ptr varList1 = Nil;
  node_ptr varList2 = Nil;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  /* The given property must be a general reactivity(1) property.
     Such a property has GAME_TWO_EXPR_LIST at top (see the
     parser). */
  nusmv_assert(PROP_GAME(NULL) != prop &&
               PropGame_GenReactivity == Prop_get_type(PROP(prop)) &&
               (GAME_TWO_EXP_LISTS ==
                node_get_type(Prop_get_expr_core(PROP(prop)))));

  /* Initialization and initial printing. */
  strategy = GAME_STRATEGY(NULL);
  construct_strategy = (((params != (gameParams_ptr) NULL) &&
                         params->strategy_printout) ||
                        opt_game_print_strategy(OptsHandler_create()));
  Game_BeforeCheckingSpec(env,prop);

  /* Declare a special variable required for strategy printing. */
  if (construct_strategy) {
    game_declare_special_var(env,
                            llength(cdr(Prop_get_expr_core(PROP(prop)))),
                             &layer,
                             &var);

    if (UStringMgr_find_string(strings,PLAYER_NAME_1) == PropGame_get_player(prop)) {
      varList1 = cons(nodemgr,var, Nil);
      varList2 = Nil;
    }
    else {
      varList1 = Nil;
      varList2 = cons(nodemgr,var, Nil);
    }
  }

  /* Verification of the property. */
  isSuccess =
    game_compute_gen_reactivity(Prop_get_expr_core(PROP(prop)),
                                Game_StrToPlayer(PropGame_get_player(prop)),
                                PropGame_get_game_bdd_fsm(prop),
                                GAME_INIT_TERM_NORMAL,
                                (construct_strategy ?
                                 (&strategy) :
                                 (GameStrategy_ptr*) NULL),
                                var,
                                NULL,
                                NULL,
                                NULL);

  /* Printing the results and cleaning up. */
  Game_AfterCheckingSpec(env,
                         prop,
                         isSuccess ? GAME_REALIZABLE : GAME_UNREALIZABLE,
                         strategy,
                         varList1,
                         varList2,
                         params);

  /* Remove created free variable. */
  if (construct_strategy) {
    if (Nil != varList1) free_node(nodemgr,varList1);
    if (Nil != varList2) free_node(nodemgr,varList2);
    game_undeclare_special_var(env,layer);
  }
}

/**Function********************************************************************

  Synopsis    [ Checks a buchi game specification. ]

  Description [ Input property has to be a buchi game specification. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_CheckBuchiGameSpec(NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params)
{
  boolean construct_strategy;
  boolean isSuccess;
  GameStrategy_ptr strategy;
  SymbLayer_ptr layer;
  node_ptr var = Nil;
  node_ptr varList1 = Nil;
  node_ptr varList2 = Nil;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  /* The given property must be a buchi game property. Such a
     property is a list of expressions (CONS at top) (see the
     parser). */
  nusmv_assert(PROP_GAME(NULL) != prop &&
               PropGame_BuchiGame == Prop_get_type(PROP(prop)) &&
               GAME_EXP_LIST == node_get_type(Prop_get_expr(PROP(prop))));

  /* Initialization and initial printing. */
  strategy = GAME_STRATEGY(NULL);
  construct_strategy = (((params != (gameParams_ptr) NULL) &&
                         params->strategy_printout) ||
                        opt_game_print_strategy(OptsHandler_create()));
  Game_BeforeCheckingSpec(env,prop);

  /* Declare a special variable required for strategy printing. */
  if (construct_strategy) {
    game_declare_special_var(env,
                             llength(car(Prop_get_expr_core(PROP(prop)))),
                             &layer,
                             &var);

    if (UStringMgr_find_string(strings,PLAYER_NAME_1) == PropGame_get_player(prop)) {
      varList1 = cons(nodemgr,var, Nil);
      varList2 = Nil;
    }
    else {
      varList1 = Nil;
      varList2 = cons(nodemgr,var, Nil);
    }
  }

  /* Verification of the property. */
  isSuccess = game_compute_buchi_game(env,
                                      prop,
                                      (construct_strategy ?
                                       (&strategy) :
                                       (GameStrategy_ptr*) NULL),
                                      var);

  /* Printing the results and cleaning up. */
  Game_AfterCheckingSpec(env,
                         prop,
                         isSuccess ? GAME_REALIZABLE : GAME_UNREALIZABLE,
                         strategy,
                         varList1,
                         varList2,
                         params);

  /* Remove created free variable. */
  if (construct_strategy) {
    if (Nil != varList1) free_node(nodemgr,varList1);
    if (Nil != varList2) free_node(nodemgr,varList2);
    game_undeclare_special_var(env,layer);
  }
}

/**Function********************************************************************

  Synopsis    [ Computes winning states for a general reactivity game. No
                strategy computation. ]

  Description [ For the description of the parameters see
                game_compute_gen_reactivity. Used in
                gameUnrealCore.c. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
boolean Game_ComputeGenReactivity(node_ptr specExp,
                                  GamePlayer player,
                                  GameBddFsm_ptr fsm,
                                  Game_InitTermination earlierTermination,
                                  bdd_ptr overapproxWinStates,
                                  bdd_ptr underapproxWinStates,
                                  bdd_ptr* winningStates)
{
  return game_compute_gen_reactivity(specExp,
                                     player,
                                     fsm,
                                     earlierTermination,
                                     NULL,
                                     NULL,
                                     overapproxWinStates,
                                     underapproxWinStates,
                                     winningStates);
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Takes a list of BDDs, free them and then frees the list. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_free_list_of_bdd(NodeMgr_ptr nodemgr,DDMgr_ptr dd, node_ptr list)
{
  node_ptr iter = list;

  while (Nil != iter) {
    node_ptr tmp = iter;
    iter = cdr(iter);

    bdd_free(dd, (bdd_ptr)car(tmp));
    free_node(nodemgr,tmp);
  }
}

/**Function********************************************************************

  Synopsis    [ Takes an array of BDDs, frees all the BDDs and then frees
                the array. ]

  Description [ "size" is the size of the array. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_free_array_of_bdd(DDMgr_ptr dd, bdd_ptr* array, int size)
{
  int i;

  for (i = 0; i < size; ++i) bdd_free(dd, array[i]);
  FREE(array);
}

/**Function********************************************************************

  Synopsis    [ Takes a list of arrays of BDDs, frees all the BDDs, then
                arrays and then the list.]

  Description [ "size" is the size of array (it should be the same for
                all arrays).]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_free_list_of_array_of_bdd(NodeMgr_ptr nodemgr,
                                            DDMgr_ptr dd,
                                           node_ptr list,
                                           int size)
{
  node_ptr iter = list;

  while (Nil != iter) {
    node_ptr tmp = iter;
    iter = cdr(iter);

    game_free_array_of_bdd(dd, (bdd_ptr*)car(tmp), size);
    free_node(nodemgr,tmp);
  }
}

/**Function********************************************************************

  Synopsis    [ Creates a fresh variable which is required to compute a
                strategy for Buchi and GR(1) games. ]

  Description [ The function creates a new layer, in this layer a new
                variable is created with enumeration type from 0 to
                number-of-guarantees minus one
                (i.e. guaranteeNumber-1). For more information about
                this var see the paper "Synthesis of Reactive(1)
                Designs" by Piterman, Pnueli and Sa'ar.

                NOTE: After printing the strategy, the var is of no
                      use and can be deleted. Use
                      game_undeclare_special_var for that.

                The function returns a newly created layer (in
                'new_layer') and a variable (in 'new_var'). ]

  SideEffects [ ]

  SeeAlso     [ game_undeclare_special_var ]

******************************************************************************/
static void game_declare_special_var(NuSMVEnv_ptr env,
                                     int guaranteeNumber,
                                     SymbLayer_ptr* new_layer,
                                     node_ptr* new_var)
{
  char name[50] = "XJ";
  static int i = 0;

  SymbLayer_ptr layer;
  node_ptr var;
  node_ptr values;
  SymbType_ptr symbolicType;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  /* Create a new temporal layer (with arbitrary name). */
  layer = SymbTable_create_layer(SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE)),
                                 NULL, /* a new name will be created */
                                 SYMB_LAYER_POS_BOTTOM);

  /* Create a new var with arbitrary name. A var name should be a
     fresh one for every specification. Otherwise, there is a chance
     that some caching in type-checking or node-to-bdd may result in a
     problem.
  */
  /* Loop until a free name is found. */
  do {
    sprintf(name+2, "_%d", ++i);
    var = find_node(nodemgr,ATOM, (node_ptr)UStringMgr_find_string(strings,name), Nil);
    var = find_node(nodemgr,DOT, Nil, var);
  } while (!SymbLayer_can_declare_var(layer, var));

  /* Create a list of values. */
  values = CompileFlatten_expand_range(0,0, guaranteeNumber - 1);
  /* We don't declare constants here since there are just numbers. */
  symbolicType = SymbType_create(env,SYMB_TYPE_ENUM, values);
  SymbLayer_declare_state_var(layer, var, symbolicType);

  /* Commit the layer to all encodings. */
  BaseEnc_commit_layer(BASE_ENC(BoolEncClient_get_bool_enc(BOOL_ENC_CLIENT(NULL))),
                       SymbLayer_get_name(layer));
  BaseEnc_commit_layer(BASE_ENC(BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)))),
                       SymbLayer_get_name(layer));

  *new_var = var;
  *new_layer = layer;

  if(opt_verbose_level_gt(OptsHandler_create(), 0)) {
    fprintf(nusmv_stdout, "\n -- VAR %s : 0 .. %d;", name, guaranteeNumber - 1);
  }

  return;
}

/**Function********************************************************************

  Synopsis    [ Deletes the variable declared with
                game_declare_special_var. ]

  Description [ Simply removes the layer containing the created var. ]

  SideEffects [ ]

  SeeAlso     [ game_declare_special_var ]

******************************************************************************/
static void game_undeclare_special_var(NuSMVEnv_ptr env,SymbLayer_ptr layer)
{
  const char* name = SymbLayer_get_name(layer);

  /* remove the layer from all encodings (bool and bdd) */
  if (BaseEnc_layer_occurs(BASE_ENC(BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)))), name)) {
    BaseEnc_remove_layer(BASE_ENC(BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)))), name);
  }
  if (BaseEnc_layer_occurs(BASE_ENC(BoolEncClient_get_bool_enc(BOOL_ENC_CLIENT(NULL))), name)) {
    BaseEnc_remove_layer(BASE_ENC(BoolEncClient_get_bool_enc(BOOL_ENC_CLIENT(NULL))), name);
  }

  SymbTable_remove_layer(SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE)), layer);
}

/**Function********************************************************************

  Synopsis    [ This function performs strategy building for a
                GENREACTIVITY (Generalized Reactivity (1), short
                GR(1)) specification. ]

  Description [ expr - the expression of the GR(1) specification. It
                  is expected to be a GAME_TWO_EXP_LISTS with two
                  lists of fairness conditions of player 1 and 2,
                  respectively.

                player - the player the game is played for.

                fsm - the Game Bdd FSM in which the spec is checked.

                earlierTermination - specifies how earlier termination
                  check is performed. See Game_InitTermination_TAG for
                  possible values.

                strategy - returns the computed strategy. It can be
                  NULL if strategy is not required. NB: The invoker
                  should free the content of the stragety.

                jxVar - a list of vars used in the construction of a
                  strategy. jxVar == NULL iff strategy == NULL.

                overapproxWinStates - if NULL the algorithm begins
                  with "true" as overapproximation of winning states
                  (initial value in greatest fixpoint of Z and X in
                  the algorithm). If this parameter is not NULL then
                  this value is used as overapproximation.

                underapproxWinStates - if NULL the algorithm begins
                  with "false" as underapproximation of winning states
                  (initial value in least fixpoint of Y in the
                  algorithm). If this parameter is not NULL then this
                  value is used as underapproximation.

                winningStates - if not NULL this parameter is used to
                  return the computed winning states. Note that
                  parameter earlierTermination may influence this
                  value: in case of earlier termination with an
                  unrealizable game overapproximation may be returned,
                  in the case of earlierTermination ==
                  GAME_INIT_TERM_CONJUNCT an underapproximation (on
                  the value of external vars) may be returned. See
                  Game_InitTermination_TAG for more info. The invoker
                  has to free the BDD returned.

                In construction of the strategy a fresh var with
                values 0..number_of_guarantees_minus_one is
                required. This variable is passed by "jxVar". It is
                Nil iff a strategy is not required.

                The returned value of the function is true (if exists
                such strategy) or false otherwise.

                NOTE: This function is completely based on the paper
                "Synthesis of Reactive(1) Designs" by Piterman, Pnueli
                and Sa'ar.  Even variables names in this function
                correspond to the paper's notions.  Read this paper if
                you want to understand how this function works. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static int totalZIterations = 0;
static int totalYIterations = 0;
static int totalXIterations = 0;
static boolean game_compute_gen_reactivity(node_ptr specExp,
                                          GamePlayer player,
                                          GameBddFsm_ptr fsm,
                                        Game_InitTermination earlierTermination,
                                          GameStrategy_ptr* strategy,
                                          node_ptr jxVar,
                                          bdd_ptr overapproxWinStates,
                                          bdd_ptr underapproxWinStates,
                                          bdd_ptr* winningStates)
{
//long time_tmp = util_cpu_time();
//long time_init_check;
  BddEnc_ptr enc = BddFsm_get_bdd_encoding(BDD_FSM(fsm));
  DDMgr_ptr dd_manager = BddEnc_get_dd_manager(enc);
  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(dd_manager));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  OptsHandler_ptr oh = OptsHandler_create();

  bdd_ptr init_1, init_2, invar_1, invar_2;
  bdd_ptr Z;
  boolean isSomeInitFalse = false;
  boolean isZFixpointReached = false;
  boolean isRealizable = true;
  bdd_ptr* assumptions = NULL; /* array of justice assumptions */
  bdd_ptr* guarantees = NULL;  /* array of justice guarantees */
  int assumptionsN, guaranteesN; /* total number of assumptions and guarantees */

  node_ptr* yResults; /* an array of lists of values of Y */
  node_ptr* xResults; /* an array of lists of list of values of X */

  /* prepare the initial states (obtain them and add the invariants) */
  init_1 = GameBddFsm_get_init_1(fsm);
  init_2 = GameBddFsm_get_init_2(fsm);
  invar_1 = GameBddFsm_get_invars_1(fsm);
  invar_2 = GameBddFsm_get_invars_2(fsm);

  bdd_and_accumulate(dd_manager, &init_1, invar_1);
  bdd_and_accumulate(dd_manager, &init_2, invar_2);

  /* check what will be our initial values in
     greatest and least fixpoint computations
  */
  if (NULL == overapproxWinStates) {
    overapproxWinStates = bdd_and(dd_manager, invar_1, invar_2);
  }
  else {
    overapproxWinStates = bdd_dup(overapproxWinStates);
  }

  if (NULL == underapproxWinStates) {
    underapproxWinStates = bdd_false(dd_manager);
  }
  else {
    underapproxWinStates = bdd_dup(underapproxWinStates);
  }

  /* initialize the assumptions and guarantees and containers for results */
  {

    /* a GENREACTIVITY expression */
    nusmv_assert(GAME_TWO_EXP_LISTS == node_get_type(specExp));

    assumptionsN = llength(car(specExp));
    assumptions = ALLOC(bdd_ptr, assumptionsN);
    guaranteesN = llength(cdr(specExp));
    guarantees = ALLOC(bdd_ptr, guaranteesN);

    node_ptr originalExps[2] = {car(specExp), cdr(specExp)};
    bdd_ptr** bddExps[2] = {&assumptions, &guarantees};
    int* expNum[2] = {&assumptionsN, &guaranteesN};
    int assumOrGuaran; /* 0 - assumptions, 1 - guarantees */

    for (assumOrGuaran = 0 ; assumOrGuaran < 2; ++assumOrGuaran) {
      node_ptr expIter;
      int i;
      bdd_ptr** constraints = bddExps[assumOrGuaran];
      int* NUM = expNum[assumOrGuaran];
      expIter = originalExps[assumOrGuaran];

      for (i = 0; i < *NUM;  expIter = cdr(expIter)) {
        (*constraints)[i] = BddEnc_expr_to_bdd(enc, car(expIter), Nil);
        bdd_and_accumulate(dd_manager, &((*constraints)[i]), invar_1);
        bdd_and_accumulate(dd_manager, &((*constraints)[i]), invar_2);

        if (bdd_is_false(dd_manager, (*constraints)[i])) {
          fprintf(nusmv_stderr,
                  "\n********   WARNING   ********\n"
                  "An %s condition is false.\n"
                  "Probably this is not what was intended.\n",
                  assumOrGuaran ? "guarantee" : " assumption");
          /* false constraint  makes all other constraint useless */
          /* We need to use i+1 since we filled array including
             position i, but the game_free_array_of_bdd uses i as the
             size of the array, thus it frees till j < i in this
             case */
          game_free_array_of_bdd(dd_manager, *constraints, i+1);
          *constraints = ALLOC(bdd_ptr, 1);
          (*constraints)[0] = bdd_false(dd_manager);
          *NUM = 1;
          i = 1; /* to terminate internal loop */
        }
        else if (bdd_is_true(dd_manager, (*constraints)[i])) {
          fprintf(nusmv_stderr,
                  "\n********   WARNING   ********\n"
                  "An %s condition is true.\n"
                  "Probably this is not what was intended.\n",
                  assumOrGuaran ? "guarantee" : " assumption");
          /* true constraint is useless and can be skipped */
          bdd_free(dd_manager, (*constraints)[i]);
          --*NUM;
        }
        else { /* normal constraints */
          ++i;
        }
      } /* for i < *NUM */
      nusmv_assert(Nil == expIter || 1 == *NUM); /* all constraint are
                                                    collected */
      /* if all constraints  were true => no constraints were created at all */
      if (0 == *NUM) {
        (*constraints)[0] =  bdd_true(dd_manager);
        *NUM = 1;
      }
    } /* for assumOrGuaran */


    /* result containers */
    yResults = ALLOC(node_ptr, guaranteesN);
    xResults = ALLOC(node_ptr, guaranteesN);
    int i;
    for (i = 0; i < guaranteesN; ++i) {
      yResults[i] = Nil;
      xResults[i] = Nil;
    }
  }

  /* Check whether an initial condition is zero and print a
     corresponding warning. */
  if (bdd_is_false(dd_manager, init_1) || bdd_is_false(dd_manager, init_2)) {
    fprintf(nusmv_stderr,
            "\n********   WARNING   ********\n"
            "Initial states set for %s is empty.\n"
            "******** END WARNING ********\n",
            bdd_is_false(dd_manager, init_1) ? PLAYER_NAME_1 : PLAYER_NAME_2);
    isSomeInitFalse = true;
    /* to skip the main loop below */
    if (earlierTermination != GAME_INIT_TERM_NONE) {
      isZFixpointReached = true;
    }
  }

  /* ------------ main loop ------------------*/
  /* Z greatest fix point loop.

     The initial value for Z is all possible states (overapproximation
     of winning states) which can potentially be given from outside.
     isRealizable is set up before above checking.  Here isRealizable
     means that there is still a chance that the game is realizable.
  */
  Z = bdd_dup(overapproxWinStates);

//fprintf(nusmv_stderr,
//        "Init Time : %f\n", (util_cpu_time() - time_tmp)/(double)1000);
//time_init_check = util_cpu_time();
  /* Earlier termination.  earlierTermination controls how the check
     is done (see Game_InitTermination_TAG).
  */
  switch (earlierTermination) {
  case GAME_INIT_TERM_NONE: break;
  case GAME_INIT_TERM_NORMAL:
    isRealizable =
      GameBddFsm_can_player_satisfy(fsm,
                                    init_1,
                                    init_2,
                                    Z,
                                    player,
                                    opt_game_game_initial_condition(oh));
    break;
  case GAME_INIT_TERM_CONJUNCT: {
    /* Note: in this case Z may become an underapproximation of the
       winning states, i.e., it may later increase instead of only
       decreasing.
    */
    bdd_ptr initCheck =
      GameBddFsm_player_satisfies_from(fsm,
                                       init_1,
                                       init_2,
                                       Z,
                                       player,
                                       opt_game_game_initial_condition(oh));
    bdd_and_accumulate(dd_manager, &Z, initCheck);
    isRealizable = bdd_isnot_false(dd_manager, initCheck);
    bdd_free(dd_manager, initCheck);
    break;
  }
  default: nusmv_assert(false); /* impossible code */
  } /* end of earlier termination */
//time_init_check = util_cpu_time() - time_init_check;
//time_tmp = util_cpu_time();

  while (!isZFixpointReached && isRealizable) {
    /* --- Z least fix point loop */
    if (opt_verbose_level_gt(oh, 0)) {
      fprintf(nusmv_stderr, "Z loop begin\n\n");
    }
    int j;
    bdd_ptr previousZ = bdd_dup(Z);

    for (j = 0; j < guaranteesN; ++j) {/* --- loop over guarantees */
      if (opt_verbose_level_gt(oh, 0)) {
        fprintf(nusmv_stderr, "  guarantee number %d \n", j);
      }

      /* It may be worth to make initial value of Y = initial value of
         start below? */
      bdd_ptr Y = bdd_dup(underapproxWinStates); /* initial value of
                                                    least fixpoint */
      boolean isYFixpointReached = false;
      bdd_ptr preImageZAndGuarantee;

      preImageZAndGuarantee = GameBddFsm_get_strong_backward_image(fsm,
                                                                   Z,
                                                                   player);
      bdd_and_accumulate(dd_manager, &preImageZAndGuarantee, guarantees[j]);

      /* free the previously remembered results */
      game_free_list_of_array_of_bdd(nodemgr,dd_manager, xResults[j], assumptionsN);
      xResults[j] = Nil;
      game_free_list_of_bdd(nodemgr,dd_manager, yResults[j]);
      yResults[j] = Nil;

      while (!isYFixpointReached) {/* --- Y least fix point loop */
        int i;
        bdd_ptr previousY, preImageY, start;
        /* array of bdd_ptr to store X for every i */
        bdd_ptr* xArray = ALLOC(bdd_ptr, assumptionsN);

        preImageY = GameBddFsm_get_strong_backward_image(fsm, Y, player);
        start = bdd_or(dd_manager, preImageZAndGuarantee, preImageY);

        /* Removed a disabled optimization to extend start to the set
           of states from which the game can be forced into state. See
           revision 8775. */

        previousY = Y;
        /* Y can be assigned to zero or keep its value. It does not matter.
           Testings showed that keeping the value give (very) small speedup.
        */
        Y = bdd_dup(Y);

        for (i = 0; i < assumptionsN; ++i) { /* --- X greatest fix point loop */

          /* Removed a disabled optimization to extend start to the
             set of states from which the game can be forced into
             state. See revision 8775. */

          bdd_ptr X = bdd_dup(Z);
          boolean isXFixpointReached = false;
          bdd_ptr notAssumption = bdd_not(dd_manager, assumptions[i]);
          int xIterations =0;
          while (!isXFixpointReached) {
            bdd_ptr tmp = GameBddFsm_get_strong_backward_image(fsm, X, player);
            bdd_and_accumulate(dd_manager, &tmp, notAssumption);
            bdd_or_accumulate(dd_manager, &tmp, start);

            /* Note: if after the first iteration X = Z, the second
               iteration is not executed. This is OK since only the
               final X is required. */
            if (X == tmp) isXFixpointReached = true;

            bdd_free(dd_manager, X);
            X = tmp;
            ++xIterations;
          } /* while !isXFixpointReached */
          if (opt_verbose_level_gt(oh, 0)) {
            fprintf(nusmv_stderr,
                    "X fixpoint for assumption %d required %d iterations\n",
                    i,
                    xIterations);
          }
          totalXIterations += xIterations;

          xArray[i] = X;
          bdd_or_accumulate(dd_manager, &Y, X);

          /* Experiments showed that it is better to update "start" to
             "Y". But is not worth to compute all backward reachable
             states here. */
          bdd_free(dd_manager, start);
          start = bdd_dup(Y);

          bdd_free(dd_manager, notAssumption);
        } /* for i = 0 ... */

        xResults[j] = cons(nodemgr,(node_ptr)xArray, xResults[j]);
        yResults[j] = cons(nodemgr,(node_ptr)bdd_dup(Y), yResults[j]);

        /* Note: if after the first iteration Y = 0, the second
           iteration is not executed. This is OK and the game is
           unrealizable. */
        if (previousY == Y) {
          isYFixpointReached = true; /* fixpoint is reached */
          if (opt_verbose_level_gt(oh, 0)) {
            fprintf(nusmv_stderr, "FIXpoint on Y\n");
          }
        }
        /* additional check -- earlier termination. Y cannot be > Z.
           The results can be not the same as if an additional last
           iteration was performed, but nevertheless correct and complete.
           Therefore, a strategy remains correct.

           NOTE: with earlierTermination==GAME_INIT_TERM_CONJUNCT it is possible
           that Y > Z. Then earlier termination will be impossible.
           I could write a proper Y >= Z check but it is may be expensive.
        */
        else if (Y == Z) {
          if (opt_verbose_level_gt(oh, 0)) {
            fprintf(nusmv_stderr, "Y reached Z\n");
          }
          bdd_ptr* newXArray;
          int i;

          isYFixpointReached = true;
          /* create an copy of last elements in xResults and yResults.
             (These elements will be removed at the end)
          */
          yResults[j] = cons(nodemgr,(node_ptr)(bdd_dup(Y)), yResults[j]);

          newXArray = ALLOC(bdd_ptr, assumptionsN);
          for (i = 0; i < assumptionsN; ++i) newXArray[i] = bdd_dup(xArray[i]);
          xResults[j] = cons(nodemgr,(node_ptr)newXArray, xResults[j]);
        }

        bdd_free(dd_manager, previousY);
        bdd_free(dd_manager, start);
        bdd_free(dd_manager, preImageY);
        ++totalYIterations;
      } /* while !isYFixpointReached */

      bdd_free(dd_manager, preImageZAndGuarantee);
      bdd_free(dd_manager, Z);
      Z = Y;
    } /* for j = 1 ... */

    if(opt_verbose_level_gt(oh, 3)) {
      fprintf(nusmv_stdout,
              "\n --- Gen-Reactive. end of external loop interation\n");
    }

    /* Check for earlier termination: if Z is unaccessible, there is
       no need to go further, the game is unrealizable.

       Practical experiments (run for realizable problems where this test
       is useless) showed that this test results in from 2% slowdown
       to 10% speedup. On average it is very small speedup (the
       exact reason is unknown).

       The mode of checking depends on earlierTermination. See
       Game_InitTermination_TAG for explanation.
    */
    //time_init_check = util_cpu_time() - time_init_check;
    switch (earlierTermination) {
    case GAME_INIT_TERM_NONE: break;
    case GAME_INIT_TERM_NORMAL:
      isRealizable =
        GameBddFsm_can_player_satisfy(fsm,
                                      init_1,
                                      init_2,
                                      Z,
                                      player,
                                      opt_game_game_initial_condition(oh));
      break;
    case GAME_INIT_TERM_CONJUNCT: {
      /* Note: in this case Z may become an underapproximation of
         winning states, i.e., it may later increase instead of only
         decreasing.
      */
      bdd_ptr initCheck =
        GameBddFsm_player_satisfies_from(fsm,
                                         init_1,
                                         init_2,
                                         Z,
                                         player,
                                         opt_game_game_initial_condition(oh));
      bdd_and_accumulate(dd_manager, &Z, initCheck);
      isRealizable = bdd_isnot_false(dd_manager, initCheck);
      bdd_free(dd_manager, initCheck);
      break;
    }
    default: nusmv_assert(false); /* impossible code */
    } /* end of earlier termination */
    //time_init_check = util_cpu_time() - time_init_check;

    /* fixpoint is reached.
       Note, if Z = 1 only ONE iteration of the loop is performed. This is OK.
    */
    if (previousZ == Z) isZFixpointReached = true;


    bdd_free(dd_manager, previousZ);

    ++totalZIterations;
  } /* while !zFixpointReached && isRealizable) */

  if (opt_verbose_level_gt(oh, 0)) {
    fprintf(nusmv_stderr,
            "\nNUMBER OF ITERATIONS. Z = %d, Y = %d, X = %d\n\n",
            totalZIterations,
            totalYIterations,
            totalXIterations);
  }

  /* if reachability of winning state has not been checked yet => do it now */
  //time_init_check = util_cpu_time() - time_init_check;
   if (GAME_INIT_TERM_NONE == earlierTermination) {
     isRealizable =
       GameBddFsm_can_player_satisfy(fsm,
                                     init_1,
                                     init_2,
                                     Z,
                                     player,
                                     opt_game_game_initial_condition(oh));
   }
   //time_init_check = util_cpu_time() - time_init_check;
   //fprintf(nusmv_stderr, "Loop Time : %f\n",
   //        (util_cpu_time() - time_tmp - time_init_check)/(double)1000);
   //fprintf(nusmv_stderr,
   //        "Init-check Time : %f\n", time_init_check/(double)1000);

  if(opt_verbose_level_gt(oh, 1)) {
    fprintf(nusmv_stdout, "\n --- Gen-Reactive spec has been computed\n");
  }

  {
    int j;
    for (j = 0; j < guaranteesN; ++j) {
      /* The last elements in xResult[j] and yResult[j] can be
         removed. Because: the previous elements represent the same
         set Z, and as result, the last elements cannot influence
         \rho_2 and \rho_3 (!low will forbid this, see the paper).
      */

      if (xResults[j] != Nil) {
        game_free_array_of_bdd(dd_manager,
                               (bdd_ptr*) car(xResults[j]), assumptionsN);
        xResults[j] = cdr(xResults[j]);
      }

      if (yResults[j] != Nil) {
        bdd_free(dd_manager, (bdd_ptr)car(yResults[j]));
        yResults[j] = cdr(yResults[j]);
      }

      /* restore the correct order of results in the result containers */
      xResults[j] = reverse(xResults[j]);
      yResults[j] = reverse(yResults[j]);
    }
  }

  /*-----------------------------------------------------------------------*/
  /*-------------         STRATEGY COMPUTATION        ---------------------*/
  /*-----------------------------------------------------------------------*/
  /* strategy is computed only if the container for the strategy is provided. */
  if ((GameStrategy_ptr*) NULL != strategy) {
    /* the game is realizable => compute the strategy for the player */
    if (isRealizable) {
      int j;
      bdd_ptr trans, tmp;

      nusmv_assert(Nil != jxVar); /* a fresh var with proper range
                                     must be provided */


      /* compute the strategy (almost) as it is computed in the paper */
      trans = bdd_false(dd_manager);

      /* transition is computed only if the opponent initial conditions
         are NOT zero
      */
      if (!isSomeInitFalse) {

        /* --  compute \rho_1 . see the paper -- */

        /* compute a disjunct of (jx=j & jx' = (j+1) & guarantee[j]) for
           all j and then a conjunct with Z & trans12 & Z' */
        for (j = 0; j < guaranteesN; ++j) {
          node_ptr eq1 = find_node(nodemgr,EQUAL,
                                   jxVar,
                                   find_node(nodemgr,NUMBER, NODE_FROM_INT(j), Nil));
          node_ptr eq2 = find_node(nodemgr,EQUAL,
                                   find_node(nodemgr,NEXT,
                                             jxVar,
                                             Nil),
                                   find_node(nodemgr,NUMBER,
                                             NODE_FROM_INT((j+1) % guaranteesN),
                                             Nil));
          node_ptr eq = find_node(nodemgr,AND, eq1, eq2);
          tmp = BddEnc_expr_to_bdd(enc, eq, Nil);
          bdd_and_accumulate(dd_manager, &tmp, guarantees[j]);
          bdd_or_accumulate(dd_manager, &trans, tmp);
          bdd_free(dd_manager, tmp);
        }
        /* create a conjunct with transition relations, Z and Z' */
        tmp = GameBddFsm_get_move(fsm, Z, player);
        bdd_and_accumulate(dd_manager, &tmp, Z);
        bdd_and_accumulate(dd_manager, &trans, tmp);
        bdd_free(dd_manager, tmp);


        /* --  compute \rho_2 . see the paper -- */

        for (j = 0; j < guaranteesN; ++j) {
          bdd_ptr low;
          node_ptr r = yResults[j];

          nusmv_assert(r != Nil);
          low = bdd_dup((bdd_ptr)car(r));

          for (r = cdr(r); r != Nil; r = cdr(r)) {
            bdd_ptr newTrans;
            node_ptr eq1 = find_node(nodemgr,EQUAL,
                                     jxVar,
                                     find_node(nodemgr,NUMBER, NODE_FROM_INT(j), Nil));
            node_ptr eq = find_node(nodemgr,AND, eq1, find_node(nodemgr,NEXT, eq1, Nil));
            tmp = BddEnc_expr_to_bdd(enc, eq, Nil);

            newTrans = GameBddFsm_get_move(fsm, low, player);
            bdd_and_accumulate(dd_manager, &newTrans, tmp);
            bdd_free(dd_manager, tmp);

            tmp = bdd_not(dd_manager, low);
            bdd_and_accumulate(dd_manager, &newTrans, tmp);
            bdd_free(dd_manager, tmp);

            bdd_and_accumulate(dd_manager, &newTrans, (bdd_ptr)car(r));

            bdd_or_accumulate(dd_manager, &trans, newTrans);
            bdd_free(dd_manager, newTrans);

            bdd_or_accumulate(dd_manager, &low, (bdd_ptr)car(r));
          } /* for */
          bdd_free(dd_manager, low);
        } /* for */


        /* --  compute \rho_3 . see the paper -- */

        for (j = 0; j < guaranteesN; ++j) {
          bdd_ptr low = bdd_false(dd_manager);

          node_ptr eq1 = find_node(nodemgr,EQUAL, jxVar,
                             find_node(nodemgr,NUMBER, NODE_FROM_INT(j), Nil));
          node_ptr eq = find_node(nodemgr,AND, eq1, find_node(nodemgr,NEXT, eq1, Nil));
          bdd_ptr varBdd = BddEnc_expr_to_bdd(enc, eq, Nil);

          node_ptr r;
          for (r = xResults[j]; r != Nil; r = cdr(r)) {
            int i;
            for (i = 0; i < assumptionsN; ++i) {
              bdd_ptr x_j_r_i = ((bdd_ptr*) car(r)) [i];
              bdd_ptr newTrans = GameBddFsm_get_move(fsm, x_j_r_i, player);

              bdd_and_accumulate(dd_manager, &newTrans, x_j_r_i);

              bdd_and_accumulate(dd_manager, &newTrans, varBdd);

              tmp = bdd_not(dd_manager, low);
              bdd_and_accumulate(dd_manager, &newTrans, tmp);
              bdd_free(dd_manager, tmp);

              tmp = bdd_not(dd_manager, assumptions[i]);
              bdd_and_accumulate(dd_manager, &newTrans, tmp);
              bdd_free(dd_manager, tmp);


              bdd_or_accumulate(dd_manager, &trans, newTrans);
              bdd_free(dd_manager, newTrans);

              bdd_or_accumulate(dd_manager, &low, x_j_r_i);
            } /* for */
          } /* for */

          bdd_free(dd_manager, varBdd);
          bdd_free(dd_manager, low);
        } /* for */
      } /* if */
        /* -- transition relation has been computed -- */

      /* -- fill in the strategy structure -- */
      tmp = bdd_false(dd_manager);
      {
        bdd_ptr tmp2;
        if (isSomeInitFalse) {
          tmp2 = bdd_false(dd_manager);
        } else {
          tmp2 = bdd_dup(Z);
        }
        *strategy = GameStrategy_construct(fsm, player, false, tmp, tmp2, trans);
        bdd_free(dd_manager, tmp2);
      }
      bdd_free(dd_manager, trans);
      bdd_free(dd_manager, tmp);
    }

    /* the game is unrealizable => compute the strategy for the opponent */
    else {
      /* For a discussion and computation of counterstrategies in
         GR(1) games see, e.g.: R. Koenighofer, G. Hofferek, R. Bloem:
         Debugging Formal Specifications Using Simple
         Counterstrategies. FMCAD'09 */
      fprintf(nusmv_stderr,
              "\n********   WARNING   ********\n"
              "Computation of a strategy for an opponent in an unrealizable "
              "Reactivity(1) Game\n"
              "is not implemented yet.\n"
              "******** END WARNING ********\n");
      *strategy = GAME_STRATEGY(NULL);
    }
  } /* end of strategy computation */

  /*-----    FREE THE CREATED OBJECTS    --------------------------------------*/

  {
    int i;
    game_free_array_of_bdd(dd_manager, assumptions, assumptionsN);
    game_free_array_of_bdd(dd_manager, guarantees, guaranteesN);

    for (i = 0; i < guaranteesN; ++i) {
      game_free_list_of_bdd(nodemgr,dd_manager, yResults[i]);
      game_free_list_of_array_of_bdd(nodemgr,dd_manager, xResults[i], assumptionsN);
    }
    FREE(yResults);
    FREE(xResults);
  }

  bdd_free(dd_manager, overapproxWinStates);
  bdd_free(dd_manager, underapproxWinStates);

  bdd_free(dd_manager, init_1);
  bdd_free(dd_manager, init_2);
  bdd_free(dd_manager, invar_1);
  bdd_free(dd_manager, invar_2);

  if (winningStates) *winningStates = Z;
  else bdd_free(dd_manager, Z);

  return isRealizable;
}

/**Function********************************************************************

  Synopsis    [ Computes winning states and builds strategy for a Buchi
                game specification (BUCHIGAME). ]

  Description [ prop     - specifies buchi game specification.

                strategy - returns the computed strategy. It can be
                           NULL if strategy is not required. NB: The
                           invoker should free the content of the
                           strategy.

                In construction of the strategy a fresh var with
                values 0..buchi-conditions minus one is required. This
                variable is passed by "jxVar". It can be Nil if a
                strategy is not required.

                The returned value of the function is true (if exists
                such strategy) or false otherwise.

                NOTE: This function is completely based on the paper
                      "Synthesis of Reactive(1) Designs" by Piterman,
                      Pnueli and Sa'ar, but a bit simplified (most
                      internal loop is removed). Even variables names
                      in this function correspond to the paper's
                      notions. Read this paper if you want to
                      understand how this function works. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static boolean game_compute_buchi_game(NuSMVEnv_ptr env,
                                       PropGame_ptr prop,
                                       GameStrategy_ptr* strategy,
                                       node_ptr jxVar)
{
  GameBddFsm_ptr fsm = PropGame_get_game_bdd_fsm(prop);
  BddEnc_ptr enc = BddFsm_get_bdd_encoding(BDD_FSM(fsm));
  DDMgr_ptr dd_manager = BddEnc_get_dd_manager(enc);

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  OptsHandler_ptr opt = OptsHandler_create();


  /* flag which player this game is for */
  GamePlayer player =
    (UStringMgr_find_string(strings,PLAYER_NAME_1) == PropGame_get_player(prop))
    ? PLAYER_1 : PLAYER_2;

  bdd_ptr init_1, init_2, invar_1, invar_2;
  bdd_ptr Z;
  boolean isZFixpointReached = false;
  boolean isRealizable;
  bdd_ptr* buchiConditions = NULL; /* array of justice buchi
                                      conditions */
  int buchiConditionsN;            /* total number of buchi
                                      conditions */
  node_ptr* yResults;              /* an array of lists of values of
                                      Y */

  /* prepare the initial states (obtain them and add the
     invariants) */
  init_1 = GameBddFsm_get_init_1(fsm);
  init_2 = GameBddFsm_get_init_2(fsm);
  invar_1 = GameBddFsm_get_invars_1(fsm);
  invar_2 = GameBddFsm_get_invars_2(fsm);

  bdd_and_accumulate(dd_manager, &init_1, invar_1);
  bdd_and_accumulate(dd_manager, &init_2, invar_2);

  /* initialize the buchiConditions and container for results */
  {
    node_ptr exp, iter;
    int i;

    exp = Prop_get_expr_core(PROP(prop));
    nusmv_assert(GAME_EXP_LIST == node_get_type(exp) &&
                 CONS ==node_get_type(car(exp))); /* a BUCHIGAME expression */
    exp = car(exp); /* get the list */

    /* buchiConditions */
    iter = exp;
    buchiConditionsN = llength(iter);
    buchiConditions = ALLOC(bdd_ptr, buchiConditionsN);
    for (i = 0; i < buchiConditionsN; ++i, iter = cdr(iter)) {
      buchiConditions[i] = BddEnc_expr_to_bdd(enc, car(iter), Nil);
      bdd_and_accumulate(dd_manager, &buchiConditions[i], invar_1);
      bdd_and_accumulate(dd_manager, &buchiConditions[i], invar_2);
    }
    nusmv_assert(i == buchiConditionsN &&
                 Nil == iter); /* both are of the same length */

    /* result containers */
    yResults = ALLOC(node_ptr, buchiConditionsN);

    for (i = 0; i < buchiConditionsN; ++i) {
      yResults[i] = Nil;
    }
  }

  /* Makes a few checkes and print a few warning in the case of
     suspicious input, i.e. init is zero, some buchiConditions
     conditions are zero or one.
  */
  {
    int i;
    /* init is zero */
    if (bdd_is_false(dd_manager, init_1) || bdd_is_false(dd_manager, init_2)) {
      fprintf(nusmv_stderr, "\n********   WARNING   ********\n"
              "Initial states set for %s is empty.\n"
              "******** END WARNING ********\n",
              bdd_is_false(dd_manager, init_1) ? PLAYER_NAME_1 : PLAYER_NAME_2);
      /* to skip the main loop below */
      isZFixpointReached = true;
    }

    /* some buchiConditions are zero or one */
    for (i = 0; i < buchiConditionsN; ++i) {
      if (bdd_is_false(dd_manager, buchiConditions[i]) ||
          bdd_is_false(dd_manager, buchiConditions[i])) {
        fprintf(nusmv_stderr, "\n********   WARNING   ********\n"
                "A Buchi condition is %s.\n"
                "Probably this is not what was intended.\n"
                "******** END WARNING ********\n",
                (bdd_is_false(dd_manager, buchiConditions[i]) ? "zero" : "one"));
      }
    } /* for */
  }

  /* ------------ main loop ------------------*/
  /* Z greatest fix point loop. The initial value for Z is all
     possible states. isRealizable is set up before above
     checking. Here isRealizable means that there is still a chance
     that the game is realizable.
  */
  if (isZFixpointReached) {
    /* initial conditions are zero(see above) =>
       do not perform any computation */
    Z = bdd_false(dd_manager);
  }
  else {
    Z = bdd_and(dd_manager, invar_1, invar_2); /* Z = all states */
  }

  /* Is it realizable or not? Used for earlier (fault) termination. */
  isRealizable =
    GameBddFsm_can_player_satisfy(fsm,
                                  init_1,
                                  init_2,
                                  Z,
                                  player,
                                  opt_game_game_initial_condition(opt));

  while (!isZFixpointReached && isRealizable) { /* --- Z least fix point loop */
    int j;
    bdd_ptr previousZ = bdd_dup(Z);

    for (j = 0; j < buchiConditionsN; ++j) { /* --- loop over buchiConditions */

      bdd_ptr preImageZAndBuchi, Y;

      preImageZAndBuchi = GameBddFsm_get_strong_backward_image(fsm, Z, player);
      bdd_and_accumulate(dd_manager, &preImageZAndBuchi, buchiConditions[j]);

      boolean isYFixpointReached = false;
      Y = bdd_dup(preImageZAndBuchi);

      /* free the previously remembered results and create a new one */
      game_free_list_of_bdd(nodemgr,dd_manager, yResults[j]);
      yResults[j] = cons(nodemgr,(node_ptr)Y, Nil); /* BDD does not belong to
                                               Y anymore */

      while (!isYFixpointReached) { /* --- Y least fix point loop */
        bdd_ptr previousY = Y;
        Y = GameBddFsm_get_strong_backward_image(fsm, Y, player);
        bdd_or_accumulate(dd_manager, &Y, preImageZAndBuchi);

        yResults[j] = cons(nodemgr,(node_ptr)Y, yResults[j]);

        if (previousY == Y) { /* fixpoint is reached */
          isYFixpointReached = true;
          /* The last elements in yResult[j] can be removed since the
             previous elements represent the same set Z. As a result
             last elements cannot influence \rho_2 and \rho_3 ("!low"
             will forbid this, see the paper).
          */
          {
            node_ptr tmp = yResults[j];
            yResults[j] = cdr(tmp);
            bdd_free(dd_manager, (bdd_ptr)car(tmp));
            free_node(nodemgr,tmp);
          }
          yResults[j] = reverse(yResults[j]); /* restore the order */
        }
        /* Additional check -- earlier termination. Y cannot be > Z.
           The results can be not the same as if an additional last
           iteration was performed, but nevertheless correct and
           complete. Therefore, a strategy remains correct.
        */
        else if (Y == Z) {
          isYFixpointReached = true;
          /* Restore the order. No need the remove the last element
             since it was not added. */
          yResults[j] = reverse(yResults[j]);
        }

      } /* while !isYFixpointReached */
      /* Y is freed when last element in yResult[j] is freed, but
         since the element is repeated twice its reference has to be
         >1 => no problem to use it after freeing.
      */
      bdd_free(dd_manager, Z);
      Z = bdd_dup(Y);

      bdd_free(dd_manager, preImageZAndBuchi);
    } /* for j = 1 ... */

    if(opt_verbose_level_gt(opt, 3)) {
      fprintf(nusmv_stdout,
              "\n --- Buchi-Game. end of external loop interation\n");
    }

    /* Fixed point is reached. Note, if Z = 1 only ONE iteration of
       the loop is performed. This is OK.
    */
    if (previousZ == Z) isZFixpointReached = true;

    /* Check for earlier termination: if Z is unaccessible, then there
       is no need to go further as the game is unrealizable. */
    isRealizable =
      GameBddFsm_can_player_satisfy(fsm,
                                    init_1,
                                    init_2,
                                    Z,
                                    player,
                                    opt_game_game_initial_condition(opt));
    bdd_free(dd_manager, previousZ);
  } /* while !zFixpointReached && isRealizable */

  if(opt_verbose_level_gt(opt, 1)) {
    fprintf(nusmv_stdout, "\n --- Buchi-Game spec has been computed\n");
  }

  /*-----------------------------------------------------------------------*/
  /*-------------         STRATEGY COMPUTATION        ---------------------*/
  /*-----------------------------------------------------------------------*/
  /* Strategy is computed only if the game is realizable and the
     container for the strategy is provided.
  */
  if ((GameStrategy_ptr*) NULL != strategy) {
    if (isRealizable) {
      int j;
      bdd_ptr trans, tmp;

      nusmv_assert(Nil != jxVar); /* a fresh var with proper range
                                     must be provided */


      /* compute the strategy (almost) as it is computed in the paper */
      trans = bdd_false(dd_manager);

      /* transition is computed only if the opponent initial conditions
         are NOT zero (otherwise Z is forced to be zero)
      */
      if (bdd_isnot_false(dd_manager, Z)) {

        /* --  compute \rho_1 . see the paper -- */

        /* compute a disjunct of (jx=j & jx' = (j+1) & buchiConditions[j]) for
           all j and then a conjunct with Z & trans12 & Z' */
        for (j = 0; j < buchiConditionsN; ++j) {
          node_ptr eq1 = find_node(nodemgr,EQUAL,
                                   jxVar,
                                   find_node(nodemgr,NUMBER,NODE_FROM_INT(j),Nil));
          node_ptr eq2 =
            find_node(nodemgr,EQUAL,
                      find_node(nodemgr,NEXT,
                                jxVar,
                                Nil),
                      find_node(nodemgr,NUMBER,
                                NODE_FROM_INT(((j+1) % buchiConditionsN)),
                                Nil));
          node_ptr eq = find_node(nodemgr,AND, eq1, eq2);
          tmp = BddEnc_expr_to_bdd(enc, eq, Nil);
          bdd_and_accumulate(dd_manager, &tmp, buchiConditions[j]);
          bdd_or_accumulate(dd_manager, &trans, tmp);
          bdd_free(dd_manager, tmp);
        }
        /* create a conjunct with transition relations, Z and Z' */
        tmp = GameBddFsm_get_move(fsm, Z, player);
        bdd_and_accumulate(dd_manager, &tmp, Z);
        bdd_and_accumulate(dd_manager, &trans, tmp);
        bdd_free(dd_manager, tmp);



        /* --  compute \rho_2 . see the paper -- */

        for (j = 0; j < buchiConditionsN; ++j) {
          bdd_ptr low;
          node_ptr r = yResults[j];

          nusmv_assert(r != Nil && car(r) != Nil);
          low = bdd_dup((bdd_ptr)car(r));

          for (r = cdr(r); r != Nil; r = cdr(r)) {
            bdd_ptr newTrans;
            node_ptr eq1 = find_node(nodemgr,EQUAL,jxVar,find_node(nodemgr,NUMBER,NODE_FROM_INT(j),Nil));
            node_ptr eq = find_node(nodemgr,AND, eq1, find_node(nodemgr,NEXT, eq1, Nil));
            tmp = BddEnc_expr_to_bdd(enc, eq, Nil);

            newTrans = GameBddFsm_get_move(fsm, low, player);
            bdd_and_accumulate(dd_manager, &newTrans, tmp);
            bdd_free(dd_manager, tmp);

            tmp = bdd_not(dd_manager, low);
            bdd_and_accumulate(dd_manager, &newTrans, tmp);
            bdd_free(dd_manager, tmp);

            bdd_and_accumulate(dd_manager, &newTrans, (bdd_ptr)car(r));

            bdd_or_accumulate(dd_manager, &trans, newTrans);
            bdd_free(dd_manager, newTrans);

            bdd_or_accumulate(dd_manager, &low, (bdd_ptr)car(r));
          } /* for */
          bdd_free(dd_manager, low);
        } /* for */


        /* --   \rho_3 is NOT computed  -- */
      } /* if */
        /* -- transition relation has been computed -- */

      /* -- fill in the strategy structure -- */
      tmp = bdd_false(dd_manager);
      *strategy = GameStrategy_construct(fsm, player, false, tmp, Z, trans);

      bdd_free(dd_manager, tmp);
      bdd_free(dd_manager, trans);
    } /* end of strategy computation for realizable game */

    /* the game is unrealizable => compute the strategy for the opponent */
    else {
      fprintf(nusmv_stderr, "\n********   WARNING   ********\n"
              "Computation of a strategy for an opponent in an unrealizable "
              "Buchi Game\n"
              "is not implemented yet.\n"
              "******** END WARNING ********\n");
      *strategy = GAME_STRATEGY(NULL);
    } /* end of strategy computation for unrealizable game */
  } /* end of strategy computation */

  /*-----    FREE THE CREATED OBJECTS    --------------------------------------*/

  {
    int i;
    game_free_array_of_bdd(dd_manager, buchiConditions, buchiConditionsN);

    for (i = 0; i < buchiConditionsN; ++i) {
      game_free_list_of_bdd(nodemgr,dd_manager, yResults[i]);
    }
    FREE(yResults);
  }

  bdd_free(dd_manager, Z);
  bdd_free(dd_manager, init_1);
  bdd_free(dd_manager, init_2);
  bdd_free(dd_manager, invar_1);
  bdd_free(dd_manager, invar_2);

  return isRealizable;
}
